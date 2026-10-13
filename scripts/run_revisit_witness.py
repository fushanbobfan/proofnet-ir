#!/usr/bin/env python3
"""Revisit witness v0.1: branch-level witnesses for a sample of the focused search's tensors revisits.

  python scripts/run_revisit_witness.py --dev
  python scripts/run_revisit_witness.py --register
  python scripts/run_revisit_witness.py --run
  python scripts/run_revisit_witness.py --summarize
  python scripts/run_revisit_witness.py --check-committed

revisit-provenance-v0.1 classed the strictly focused search's revisits by branch signature: 7.8% of those on the
count-preserving negatives are permutations of an earlier branch, 33.3% decompose the same tensors with other splits,
and 58.9% decompose other tensors, a class that mixes attempts that differ with subproblems a reordering of rules
re-creates. So rule order accounts for between 7.8% and 66.7% of the revisits, and the counts cannot say whether it
accounts for most. `proofnet_ir_revisit_witness` runs the same search with its control flow unchanged and writes out
a stratified sample of the tensors revisits with their full branches: the current one and the first four distinct
branches that met the query before. Each sampled revisit is examined branch against branch:

- a *reordering witness*: some earlier branch decomposes, besides tensors both branches decompose with the same sides
  and, once the tensors only one of them decomposes are folded into the rule that sends them away, the same material
  sent at each rule, only tensors none of whose subformulas is in the revisited sub-sequent; the two branches then
  differ by moving those tensors' rules across the splits that send them away, a permutation of commuting rules;
- an *exclusion witness*: every earlier branch, all of them kept, contradicts this one directly, sending a tensor
  both decompose into a different premise, or putting a formula, or a subformula of one, that both meet at the same
  tensor on different sides of it, so no proof structure orders both;
- *alike*: a formula the comparison needs occurs more than once among the input's subformulas, so keys, which the
  memo tables compare, do not identify it, and the branches cannot be compared formula by formula;
- *unresolved*: anything else.

`--dev` runs both searches on matched-search-v0.2's development set, none of it in the corpus, and prints the checks
and the counts of sampled and reconstructed revisits. `--check-committed` verifies hashes and the summary, and reruns
the tasks that finished within 200 ms.
"""

from __future__ import annotations

import argparse
import gzip
import json
import random
import subprocess
import sys
import time
from collections import Counter
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parent))
import run_matched_search as v1  # noqa: E402
import run_pruned_search as v2  # noqa: E402

ROOT = v1.ROOT
EXPERIMENT = ROOT / "experiments" / "revisit-witness-v0.1"
CORPUS = v2.CORPUS
REVISITS = ROOT / "experiments" / "focused-revisits-v0.1" / "results.jsonl"
PROVENANCE = ROOT / "experiments" / "revisit-provenance-v0.1" / "results.jsonl"
PREREG = EXPERIMENT / "preregistration.json"
RESULTS = EXPERIMENT / "results.jsonl.gz"
SUMMARY = EXPERIMENT / "summary.json"
REPORT = EXPERIMENT / "report.md"
EXE = "proofnet_ir_revisit_witness"
PROVENANCE_EXE = "proofnet_ir_revisit_provenance"
V01_EXE = "proofnet_ir_focused_revisits"
IMPLEMENTATIONS = {"search": ROOT / "ProofNetIRRevisitWitness.lean", "runner": Path(__file__).resolve()}
BUDGET_MS = 5000
CHECK_MAX_ELAPSED_MS = 200
COUNTERS = ("proveCalls", "focusCalls", "cacheHits", "proveHits", "focusHits", "decides", "splits", "infeasible")
CLASS_FIELDS = tuple(f"{t}{c}" for t in ("prove", "focus") for c in ("Permutation", "Splits", "Tensors"))
WITNESS = ("reorder", "exclusion", "alike", "unresolved")
RATES = {"unique": 1000, "two-label": 20, "one-label": 20}  # per mille of a count-preserving negative's tensors revisits
BOOTSTRAP_SEED = 20261013
BOOTSTRAP_RESAMPLES = 2000

QUESTION = ("of the focused search's tensors revisits on the count-preserving negatives, how many differ from an earlier "
            "branch to the same sub-sequent only by commuting rules, how many contradict every earlier branch, and does "
            "rule order then account for most revisits where keys identify formulas")
HYPOTHESES = {
    "H119": "on the count-preserving negatives with unique labels (all sizes pooled), at least half of the tensors "
            "revisits have a reordering witness",
    "H120": "on the count-preserving negatives with unique labels (all sizes pooled), fewer than one in ten tensors "
            "revisits has an exclusion witness",
    "H121": "on the 32-atom count-preserving negatives with unique labels, the identification interval for the share of "
            "revisits that rule order accounts for (permutations and reordering-witnessed tensors revisits at its low "
            "end; all revisits but splits and exclusion-witnessed tensors revisits at its high end) lies entirely on "
            "one side of one half",
}
CHECKS = {
    "C51": "the search reproduces focused-revisits-v0.1's outcome and eight counters, and revisit-provenance-v0.1's six "
           "class counts, on every task",
    "C52": "every branch of every sampled revisit, rebuilt from the input sequent rule by rule, reaches the revisited "
           "query",
}


# ---------------------------------------------------------------- formulas


def key(formula: dict[str, Any]) -> str:
    """The search's formula key: sorted-key JSON text."""
    return json.dumps(formula, separators=(",", ":"), sort_keys=True)


def parse(text: str) -> dict[str, Any]:
    return json.loads(text)


def is_positive(formula: dict[str, Any]) -> bool:
    return formula["kind"] == "tensor" or (formula["kind"] == "atom" and formula["positive"])


def subformula_keys(formula: dict[str, Any]) -> list[str]:
    out = [key(formula)]
    if formula["kind"] != "atom":
        out += subformula_keys(formula["left"]) + subformula_keys(formula["right"])
    return out


def decompose(formulas: list[dict[str, Any]]) -> list[dict[str, Any]]:
    out, todo = [], list(formulas)
    while todo:
        f = todo.pop(0)
        if f["kind"] == "par":
            todo[:0] = [f["left"], f["right"]]
        else:
            out.append(f)
    return out


def dual(atom: dict[str, Any]) -> dict[str, Any]:
    return {"kind": "atom", "name": atom["name"], "positive": not atom["positive"]}


# ---------------------------------------------------------------- branches


class Rebuild(Exception):
    pass


def rebuild(sequent: list[dict[str, Any]], steps: list[list[Any]], keys: list[str]) -> tuple[list[dict[str, Any]], tuple]:
    """The branch rule by rule from the input: at each tensor rule the context it splits, what stays and what is sent,
    the side, and at the end the frontier: ('prove', state) or ('focus', context, goal), as key multisets."""
    state: Counter = Counter(key(f) for f in decompose(sequent))
    focus_goal: str | None = None
    focus_context: Counter = Counter()
    infos = []
    for tensor_id, side, sent_ids in steps:
        t, sent = keys[tensor_id], Counter(keys[i] for i in sent_ids)
        if focus_goal is not None:
            if focus_goal != t:
                raise Rebuild("a focused tensor is not the next rule's")
            context = focus_context
        else:
            if state[t] < 1 or not is_positive(parse(t)):
                raise Rebuild("the decided tensor is not in the sequent")
            context = state - Counter([t])
        tensor = parse(t)
        left, right = tensor["left"], tensor["right"]
        if left["kind"] == "atom" and left["positive"]:
            expected = Counter([key(dual(left))])
            if side != 1 or sent != expected or context[key(dual(left))] < 1:
                raise Rebuild("an atomic tensor rule does not match")
            follow = right
        elif right["kind"] == "atom" and right["positive"]:
            expected = Counter([key(dual(right))])
            if side != 0 or sent != expected or context[key(dual(right))] < 1:
                raise Rebuild("an atomic tensor rule does not match")
            follow = left
        else:
            if any(context[k] < n for k, n in sent.items()):
                raise Rebuild("a split sends what the context lacks")
            follow = left if side == 0 else right
        kept = context - sent
        infos.append({"tensor": t, "side": side, "context": context, "kept": kept, "sent": sent})
        if follow["kind"] == "tensor":
            focus_goal, focus_context = key(follow), kept
        elif is_positive(follow):
            raise Rebuild("a branch goes on past a positive atom")
        else:
            focus_goal = None
            state = kept + Counter(key(f) for f in decompose([follow]))
    frontier = ("focus", focus_context, focus_goal) if focus_goal is not None else ("prove", state)
    return infos, frontier


def reaches(frontier: tuple, record: dict[str, Any], keys: list[str]) -> bool:
    query = Counter(keys[i] for i in record["query"])
    if record["table"] == "prove":
        return frontier[0] == "prove" and frontier[1] == query
    goal = keys[record["goal"]]
    if frontier[0] == "focus":
        return frontier[2] == goal and frontier[1] == query
    return frontier[1][goal] >= 1 and frontier[1] - Counter([goal]) == query


def query_keys(record: dict[str, Any], keys: list[str]) -> set[str]:
    out = {keys[i] for i in record["query"]}
    if record["goal"] is not None:
        out.add(keys[record["goal"]])
    return out


def strictly_inside(inner: str, outer: str) -> bool:
    return inner != outer and inner in subformula_keys(parse(outer))[1:]


def exits(infos: list[dict[str, Any]], shared: set[str]) -> dict[str, Any] | None:
    """The material each rule on a tensor in `shared` sends away, with every tensor only this branch decomposes folded
    into the rule that sends its parts away: the tensor stands for itself and for what its own rule sent. None if the
    parts of such a tensor leave at more than one rule."""
    owner: dict[str, str] = {}  # a lineage formula -> the outermost own-only tensor it comes from
    material: dict[str, Counter] = {}
    leaves: dict[str, set[int]] = {}
    out: dict[str, Counter] = {}
    for i, info in enumerate(infos):
        t = info["tensor"]
        if t not in shared:
            unit = owner.get(t, t)
            material.setdefault(unit, Counter())
            for k, n in info["sent"].items():
                material[unit][owner.get(k, k)] += n
            for k in subformula_keys(parse(t))[1:]:
                owner.setdefault(k, unit)
            continue
        sent: Counter = Counter()
        for k, n in info["sent"].items():
            if k in owner:
                leaves.setdefault(owner[k], set()).add(i)
            else:
                sent[k] += n
        out[t] = sent
    for unit, places in leaves.items():
        if len(places) != 1:
            return None
        rule = infos[next(iter(places))]["tensor"]
        out[rule] = out[rule] + Counter([unit]) + material.get(unit, Counter())
    # an own-only tensor whose parts never leave at a shared rule stays unattributed
    attributed = set(leaves)
    if any(unit not in attributed for unit in material):
        return None
    return out


def compare(record: dict[str, Any], current: list[list[Any]], earlier: list[list[Any]], task: dict[str, Any],
            keys: list[str], multiplicity: Counter) -> str:
    """One earlier branch against the current one: reorder, exclusion, alike, or unresolved."""
    infos2, _ = rebuild(task["sequent"], current, keys)
    infos1, _ = rebuild(task["sequent"], earlier, keys)
    q = query_keys(record, keys)
    involved = set(q)
    for info in infos1 + infos2:
        involved |= {info["tensor"]} | set(info["context"])
    if any(multiplicity[k] > 1 for k in involved):
        return "alike"
    tensors1, tensors2 = {i["tensor"] for i in infos1}, {i["tensor"] for i in infos2}
    shared = tensors1 & tensors2
    at1, at2 = {i["tensor"]: i for i in infos1}, {i["tensor"]: i for i in infos2}
    for t in shared:
        a, b = at1[t], at2[t]
        if a["side"] != b["side"]:
            return "exclusion"
        for f in a["context"]:
            for g in b["context"]:
                if f == g or strictly_inside(g, f) or strictly_inside(f, g):
                    if (f in a["kept"]) != (g in b["kept"]):
                        return "exclusion"
    if any(any(k in q for k in subformula_keys(parse(t))) for t in tensors1 ^ tensors2):
        return "unresolved"
    e1, e2 = exits(infos1, shared), exits(infos2, shared)
    if e1 is None or e2 is None:
        return "unresolved"
    return "reorder" if all(e1.get(t, Counter()) == e2.get(t, Counter()) for t in shared) else "unresolved"


def classify(record: dict[str, Any], task: dict[str, Any], keys: list[str], multiplicity: Counter) -> str:
    verdicts = [compare(record, record["current"], b, task, keys, multiplicity) for b in record["earlier"]]
    if "reorder" in verdicts:
        return "reorder"
    if verdicts and all(v == "exclusion" for v in verdicts) and len(record["earlier"]) == record["distinctEarlier"]:
        return "exclusion"
    if "alike" in verdicts:
        return "alike"
    return "unresolved"


def rebuilds(record: dict[str, Any], task: dict[str, Any], keys: list[str]) -> bool:
    try:
        return all(reaches(rebuild(task["sequent"], b, keys)[1], record, keys)
                   for b in [record["current"], *record["earlier"]])
    except Rebuild:
        return False


# ---------------------------------------------------------------- running


def rate(task: dict[str, Any]) -> int:
    return RATES.get(task["labelMode"], 0) if task["kind"] == "negative-count" else 0


def stream(exe: str, tasks: list[dict[str, Any]], partial: Path | None) -> dict[str, dict[str, Any]]:
    payload = "".join(json.dumps({"id": t["id"], "sequent": t["sequent"], "samplePerMille": rate(t)},
                                 separators=(",", ":")) + "\n" for t in tasks)
    process = subprocess.Popen([v1.find_lake(), "exe", exe, "--budget-ms", str(BUDGET_MS)], cwd=ROOT,
                               stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, encoding="utf-8")
    assert process.stdin is not None and process.stdout is not None
    process.stdin.write(payload)
    process.stdin.close()
    rows: dict[str, dict[str, Any]] = {}
    sink = partial.open("w", encoding="utf-8", newline="\n") if partial else None
    for line in process.stdout:
        if line.startswith("{"):
            row = json.loads(line)
            rows[row["id"]] = row
            if sink:
                sink.write(line)
                sink.flush()
            if len(rows) % 100 == 0:
                print(f"{exe}: {len(rows)}/{len(tasks)}", flush=True)
    if sink:
        sink.close()
    if process.wait() != 0:
        raise SystemExit(f"{exe} failed")
    return rows


def compute_results(tasks: list[dict[str, Any]], runs: dict[str, dict[str, Any]]) -> list[dict[str, Any]]:
    rows = []
    for task in tasks:
        result = runs[task["id"]]["strictMemo"]
        outcome = v1.outcome_of(result)
        multiplicity = Counter(k for f in task["sequent"] for k in subformula_keys(f))
        samples = []
        for record in result["samples"]:
            ok = rebuilds(record, task, result["keys"])
            samples.append(record | {"rebuilt": ok,
                                     "witness": classify(record, task, result["keys"], multiplicity) if ok else None})
        row = {k: task[k] for k in ("id", "baseId", "depth", "atoms", "labelMode", "kind", "expectedProvable")}
        row["stratum"] = v2.stratum(task)
        row["samplePerMille"] = rate(task)
        row["strictMemo"] = {"outcome": outcome, "elapsedMs": result["elapsedNs"] / 1e6,
                             **{k: result[k] for k in (*COUNTERS, *CLASS_FIELDS, "tensorsRevisits")},
                             "keys": result["keys"], "samples": samples}
        rows.append(row)
    return rows


# ---------------------------------------------------------------- summary


def tensors_of(memo: dict[str, Any]) -> int:
    return memo["proveTensors"] + memo["focusTensors"]


def permutations_of(memo: dict[str, Any]) -> int:
    return memo["provePermutation"] + memo["focusPermutation"]


def splits_of(memo: dict[str, Any]) -> int:
    return memo["proveSplits"] + memo["focusSplits"]


def witness_shares(rows: list[dict[str, Any]]) -> dict[str, Any]:
    """Shares of the witness classes among a group's sampled tensors revisits, each task's sample weighted by the
    inverse of its sampling rate, and the identification interval for rule order over the group's revisits."""
    weighted: Counter = Counter()
    sampled: Counter = Counter()
    for r in rows:
        weight = 1000 / r["samplePerMille"] if r["samplePerMille"] else 0
        for s in r["strictMemo"]["samples"]:
            if s["rebuilt"]:
                weighted[s["witness"]] += weight
                sampled[s["witness"]] += 1
    total = sum(weighted.values())
    shares = {w: weighted[w] / total if total else None for w in WITNESS}
    memo = [r["strictMemo"] for r in rows]
    revisits = sum(m["cacheHits"] for m in memo)
    tensors, permutations, splits = (sum(f(m) for m in memo) for f in (tensors_of, permutations_of, splits_of))
    interval = None
    if revisits and total:
        low = (permutations + tensors * shares["reorder"]) / revisits
        high = (revisits - splits - tensors * shares["exclusion"]) / revisits
        interval = [low, high]
    return {"tasks": len(rows), "revisits": revisits, "tensorsRevisits": tensors, "sampled": sum(sampled.values()),
            "sampledByWitness": {w: sampled[w] for w in WITNESS}, "witnessShares": shares,
            "ruleOrderInterval": interval}


def bootstrap(rows: list[dict[str, Any]], statistic) -> list[float] | None:
    """A percentile interval over tasks."""
    if not rows:
        return None
    generator = random.Random(BOOTSTRAP_SEED)
    values = []
    for _ in range(BOOTSTRAP_RESAMPLES):
        value = statistic([generator.choice(rows) for _ in rows])
        if value is not None:
            values.append(value)
    if not values:
        return None
    values.sort()
    return [values[int(0.025 * len(values))], values[int(0.975 * len(values)) - 1]]


def summarize(rows: list[dict[str, Any]], v01_rows: list[dict[str, Any]], provenance_rows: list[dict[str, Any]]) -> dict[str, Any]:
    negatives = [r for r in rows if r["kind"] == "negative-count"]
    unique = [r for r in negatives if r["labelMode"] == "unique"]
    unique32 = [r for r in unique if r["atoms"] == 32]
    out: dict[str, Any] = {"experiment": "revisit-witness-v0.1", "tasks": len(rows),
                           "negatives": witness_shares(negatives), "strata": {}}
    for name in sorted({r["stratum"] for r in negatives}):
        out["strata"][name] = witness_shares([r for r in negatives if r["stratum"] == name])
    by_mode = {mode: witness_shares([r for r in negatives if r["labelMode"] == mode])
               for mode in ("unique", "two-label", "one-label")}
    out["byLabelMode"] = by_mode
    u, u32 = by_mode["unique"], witness_shares(unique32)
    reorder, exclusion = u["witnessShares"]["reorder"], u["witnessShares"]["exclusion"]
    interval = u32["ruleOrderInterval"]
    out["hypotheses"] = {
        "H119": {"reorderShare": reorder, "sampled": u["sampled"],
                 "interval": bootstrap(unique, lambda g: witness_shares(g)["witnessShares"]["reorder"]),
                 "holds": reorder is not None and reorder >= 0.5},
        "H120": {"exclusionShare": exclusion, "sampled": u["sampled"],
                 "interval": bootstrap(unique, lambda g: witness_shares(g)["witnessShares"]["exclusion"]),
                 "holds": exclusion is not None and exclusion < 0.1},
        "H121": {"ruleOrderInterval": interval, "tasks": len(unique32),
                 "holds": interval is not None and (interval[0] > 0.5 or interval[1] < 0.5)},
    }
    v01 = {r["id"]: r["strictMemo"] for r in v01_rows}
    prov = {r["id"]: r["strictMemo"] for r in provenance_rows}
    mismatches = [r["id"] for r in rows if r["strictMemo"]["outcome"] != v01[r["id"]]["outcome"]
                  or any(r["strictMemo"][k] != v01[r["id"]][k] for k in COUNTERS)
                  or any(r["strictMemo"][k] != prov[r["id"]][k] for k in CLASS_FIELDS)]
    unbuilt = [(r["id"], s["rank"]) for r in rows for s in r["strictMemo"]["samples"] if not s["rebuilt"]]
    out["checks"] = {
        "C51": {"compared": len(rows), "mismatches": mismatches[:20], "mismatchCount": len(mismatches),
                "holds": not mismatches},
        "C52": {"sampled": sum(len(r["strictMemo"]["samples"]) for r in rows), "notRebuilt": unbuilt[:20],
                "notRebuiltCount": len(unbuilt), "holds": not unbuilt},
    }
    return out


def write_report(summary: dict[str, Any]) -> None:
    def pct(x: float | None) -> str:
        return "n/a" if x is None else f"{100 * x:.1f}%"

    lines = ["# revisit-witness-v0.1", "", f"Tasks: {summary['tasks']}.", "",
             "| Count-preserving negatives | tasks | tensors revisits | sampled | reorder | exclusion | alike | "
             "unresolved | rule order |", "|---|---:|---:|---:|---:|---:|---:|---:|---|"]
    for name, e in [("all", summary["negatives"]), *summary["strata"].items()]:
        w, iv = e["witnessShares"], e["ruleOrderInterval"]
        lines.append(f"| {name} | {e['tasks']} | {e['tensorsRevisits']} | {e['sampled']} | {pct(w['reorder'])} | "
                     f"{pct(w['exclusion'])} | {pct(w['alike'])} | {pct(w['unresolved'])} | "
                     f"{'n/a' if iv is None else pct(iv[0]) + ' to ' + pct(iv[1])} |")
    lines += ["", "## Hypotheses", ""]
    for k, e in summary["hypotheses"].items():
        lines.append(f"- {k} ({'holds' if e['holds'] else 'fails'}): {HYPOTHESES[k]}. "
                     f"{json.dumps({x: y for x, y in e.items() if x != 'holds'})}")
    lines += ["", "## Checks", ""]
    for k, e in summary["checks"].items():
        lines.append(f"- {k} ({'holds' if e['holds'] else 'fails'}): {CHECKS[k]}.")
    v1.write_lf(REPORT, "\n".join(lines) + "\n")


# ---------------------------------------------------------------- registration


DEVELOPMENT_CHECKS = [
    "the question, definitions, hypotheses, and checks above were written into this runner before any development run",
    "ProofNetIRRevisitWitness.lean is revisit-provenance-v0.1's search with its control flow unchanged; branches also "
    "keep their rules in full, each query its first four distinct branches, and a seeded draw writes out a share of the "
    "tensors revisits; it builds with proofnet-ir's toolchain",
    "scripts/test_revisit_witness.py checks the rebuild and the classes on hand-made branches whose answer is known: "
    "two tensors decomposed in either order (a reordering), a shared tensor entered from different sides (an "
    "exclusion), and repeated labels (alike)",
]


def registration_payload(tasks: list[dict[str, Any]], dev: dict[str, Any]) -> dict[str, Any]:
    return {
        "experiment": "revisit-witness-v0.1", "question": QUESTION,
        "registeredLocalDate": time.strftime("%Y-%m-%d") + " America/Los_Angeles",
        "corpus": {"path": "experiments/matched-search-v0.2/corpus.jsonl", "sha256": v1.sha256_file(CORPUS),
                   "tasks": len(tasks)},
        "comparedResults": {"focusedRevisits": v1.sha256_file(REVISITS), "revisitProvenance": v1.sha256_file(PROVENANCE)},
        "search": "revisit-provenance-v0.1's search, copied into ProofNetIRRevisitWitness.lean with its control flow "
                  "unchanged; a branch also keeps its rules in full, and a query its first four distinct branches",
        "sample": {"rule": "a tensors revisit is written out when splitmix64 of the task id's hash xor the mixed rank of "
                           "the revisit among the task's tensors revisits, modulo 1000, is below the task's rate per "
                           "mille", "ratesPerMille": RATES, "tasks": "the count-preserving negatives only"},
        "definitions": {w: d for w, d in zip(WITNESS, (
            "some earlier branch kept for the query decomposes, besides tensors both branches decompose with the same "
            "sides and (once tensors only one branch decomposes are folded into the rule that sends their parts away, "
            "standing for themselves and what their own rules sent) the same material sent at each rule, only tensors "
            "none of whose subformulas is in the revisited query",
            "every earlier branch was kept and each sends a tensor both decompose into a different premise, or puts a "
            "formula, or a subformula of one, that both meet at the same tensor on different sides",
            "a formula the comparison needs (in the query, a decomposed tensor, or a context a rule splits) occurs more "
            "than once among the input's subformulas",
            "any other sampled tensors revisit"))},
        "measures": {"witnessShares": "each class's share of a group's sampled tensors revisits, a task's sample weighted "
                                      "by the inverse of its rate",
                     "ruleOrderInterval": "from (permutations + tensors revisits x the reorder share) / revisits to "
                                          "(revisits - splits - tensors revisits x the exclusion share) / revisits"},
        "budget": {"wallClockMsPerTask": BUDGET_MS, "process": f"{EXE} runs the tasks sequentially, on one core"},
        "hypotheses": HYPOTHESES, "checks": CHECKS,
        "tests": f"the hypotheses are decided by the rules as stated; shares are reported with percentile bootstrap "
                 f"intervals over tasks (seed {BOOTSTRAP_SEED}, {BOOTSTRAP_RESAMPLES} resamples), which do not decide",
        "implementationSha256": {name: v1.sha256_file(path) for name, path in IMPLEMENTATIONS.items()},
        "developmentChecksBeforeRegistration": DEVELOPMENT_CHECKS + [dev["note"]],
        "resultsAbsentAtRegistration": True,
    }


def load_rows(path: Path) -> list[dict[str, Any]]:
    text = gzip.decompress(path.read_bytes()).decode("utf-8") if path.suffix == ".gz" else path.read_text(encoding="utf-8")
    return [json.loads(line) for line in text.splitlines() if line.strip()]


def write_rows(rows: list[dict[str, Any]]) -> None:
    RESULTS.write_bytes(gzip.compress("".join(json.dumps(r, separators=(",", ":")) + "\n" for r in rows).encode("utf-8"),
                                      compresslevel=9, mtime=0))


def dev_check() -> dict[str, Any]:
    tasks = v2.dev_tasks()
    rows = compute_results(tasks, stream(EXE, tasks, None))
    old = stream(V01_EXE, tasks, None)
    prov = stream(PROVENANCE_EXE, tasks, None)
    mismatches = [t["id"] for t, r in zip(tasks, rows)
                  if r["strictMemo"]["outcome"] != v1.outcome_of(old[t["id"]]["strictMemo"])
                  or any(r["strictMemo"][k] != old[t["id"]]["strictMemo"][k] for k in COUNTERS)
                  or any(r["strictMemo"][k] != prov[t["id"]]["strictMemo"][k] for k in CLASS_FIELDS)]
    sampled = sum(len(r["strictMemo"]["samples"]) for r in rows)
    unbuilt = sum(1 for r in rows for s in r["strictMemo"]["samples"] if not s["rebuilt"])
    note = (f"matched-search-v0.2's development set ({len(tasks)} tasks, none in the corpus) through this search, "
            f"revisit-provenance-v0.1's and focused-revisits-v0.1's: outcomes, counters, and class counts agree on "
            f"{len(tasks) - len(mismatches)} of {len(tasks)} tasks; {sampled} tensors revisits were sampled and "
            f"{sampled - unbuilt} rebuilt; only these counts were printed, and no witness class or share was looked at")
    return {"tasks": len(tasks), "mismatches": mismatches, "sampled": sampled, "notRebuilt": unbuilt, "note": note}


def main() -> int:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    for flag in ("--dev", "--register", "--run", "--summarize", "--check-committed"):
        mode.add_argument(flag, action="store_true")
    args = parser.parse_args()
    if args.dev:
        print(json.dumps(dev_check(), indent=1))
        return 0
    tasks = v2.load_tasks()
    if args.register:
        if RESULTS.exists() or SUMMARY.exists():
            raise SystemExit("results already exist; registration must precede them")
        dev = dev_check()
        if dev["mismatches"] or dev["notRebuilt"]:
            raise SystemExit(f"development checks fail: {json.dumps(dev)}")
        EXPERIMENT.mkdir(parents=True, exist_ok=True)
        v1.write_lf(PREREG, json.dumps(registration_payload(tasks, dev), indent=1, sort_keys=True) + "\n")
        print(f"registered {len(tasks)} tasks: {PREREG}")
        return 0
    prereg = json.loads(PREREG.read_text(encoding="utf-8"))
    if prereg["corpus"]["sha256"] != v1.sha256_file(CORPUS):
        raise SystemExit("corpus changed since registration")
    if prereg["implementationSha256"]["search"] != v1.sha256_file(IMPLEMENTATIONS["search"]):
        raise SystemExit("the search changed since registration")
    v01_rows, provenance_rows = load_rows(REVISITS), load_rows(PROVENANCE)
    if args.run:
        rows = compute_results(tasks, stream(EXE, tasks, EXPERIMENT / "search.partial"))
        write_rows(rows)
        (EXPERIMENT / "search.partial").unlink(missing_ok=True)
    if args.run or args.summarize:
        summary = summarize(load_rows(RESULTS), v01_rows, provenance_rows)
        v1.write_lf(SUMMARY, json.dumps(summary, indent=1) + "\n")
        write_report(summary)
        print(json.dumps({k: {"holds": v["holds"]} for k, v in summary["hypotheses"].items()}),
              json.dumps({k: v["holds"] for k, v in summary["checks"].items()}))
        return 0
    if not RESULTS.exists():
        print("revisit-witness-v0.1: registered, no results yet")
        return 0
    committed = load_rows(RESULTS)
    if [row["id"] for row in committed] != [task["id"] for task in tasks]:
        raise SystemExit("committed result ids differ from the corpus")
    fast = [t for t, row in zip(tasks, committed) if row["strictMemo"]["elapsedMs"] <= CHECK_MAX_ELAPSED_MS]
    by_id = {row["id"]: row for row in committed}
    for row in compute_results(fast, stream(EXE, fast, None)):
        old = by_id[row["id"]]["strictMemo"]
        if any(row["strictMemo"][k] != old[k] for k in ("outcome", *CLASS_FIELDS, "tensorsRevisits")) \
                or row["strictMemo"]["samples"] != old["samples"]:
            raise SystemExit(f"recomputed results differ for {row['id']}")
    summary = json.loads(SUMMARY.read_text(encoding="utf-8"))
    if summary != json.loads(json.dumps(summarize(committed, v01_rows, provenance_rows))):
        raise SystemExit("the committed summary does not follow from the results")
    print(f"revisit-witness-v0.1-check-ok: tasks={len(committed)} rerun={len(fast)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
