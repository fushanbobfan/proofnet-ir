#!/usr/bin/env python3
"""Matched search v0.2: pruned arms on both sides and count-preserving negatives.

  python scripts/run_pruned_search.py --dev
  python scripts/run_pruned_search.py --build-corpus
  python scripts/run_pruned_search.py --register
  python scripts/run_pruned_search.py --run
  python scripts/run_pruned_search.py --check-committed

The corpus keeps matched-search-v0.1's 360 positives and 280 connective-flip
negatives and adds one count-preserving negative per positive: the first
unprovable candidate among the exchanges of one tensor with one par (tensors,
then pars, in preorder), then up to 1,000 seeded shuffles of the positive's
atom occurrences. Both keep the atoms and the connective counts, so the
sequent is balanced and has `atoms / 2 - 1` tensors, the two conditions every
provable sequent meets. A candidate's unprovability is certified by a
countermodel in a finite Lukasiewicz chain when one exists (MLL is sound for
every MV-algebra: tensor as strong conjunction, par as strong disjunction, the
dual as negation; the two-element chain is the classical case) and otherwise
by the exhaustive `focusedStrict` search under a 60-second budget. `--dev`
runs every arm on generated bases with seeds disjoint from the corpus and
writes nothing under `experiments/`. `--check-committed` verifies hashes,
labels, and countermodels and reruns the tasks on which every arm finished
within 200 ms.
"""

from __future__ import annotations

import argparse
import copy
import itertools
import json
import math
import random
import statistics
import subprocess
import sys
from pathlib import Path
from typing import Any, Iterator

sys.path.insert(0, str(Path(__file__).resolve().parent))
import run_matched_search as v1  # noqa: E402

ROOT = v1.ROOT
EXPERIMENT = ROOT / "experiments" / "matched-search-v0.2"
CORPUS = EXPERIMENT / "corpus.jsonl"
PREREG = EXPERIMENT / "preregistration.json"
RESULTS = EXPERIMENT / "results.jsonl"
SUMMARY = EXPERIMENT / "summary.json"
REPORT = EXPERIMENT / "report.md"
IMPLEMENTATIONS = {
    "prunedArms": ROOT / "ProofNetIRPrunedSearch.lean",
    "v01Arms": ROOT / "ProofNetIRMatchedSearch.lean",
    "baseGenerator": ROOT / "ProofNetIRSearchCorpus.lean",
    "runner": ROOT / "scripts" / "run_pruned_search.py",
}
BUDGET_MS = 5000
CERTIFY_BUDGET_MS = 60000
MAX_SHUFFLES = 1000
FIRST_SHUFFLES = 200
MAX_CHAIN = 4
MAX_VALUATIONS = 65536
V01_ARMS = ("focused", "focusedBalanced", "nets")
PRUNED_ARMS = ("netsPruned", "focusedStrict")
ARMS = V01_ARMS + PRUNED_ARMS
CHECK_MAX_ELAPSED_MS = 200
DEV_SEED = 900_000
DEV_PER_DEPTH = 8


# Sequent structure

def node_at(sequent: list[dict[str, Any]], path: list[int]) -> dict[str, Any]:
    node = sequent[path[0]]
    for step in path[1:]:
        node = node["left"] if step == 0 else node["right"]
    return node


def leaves(sequent: list[dict[str, Any]]) -> list[dict[str, Any]]:
    out: list[dict[str, Any]] = []

    def walk(formula: dict[str, Any]) -> None:
        if formula["kind"] == "atom":
            out.append(formula)
        else:
            walk(formula["left"])
            walk(formula["right"])
    for formula in sequent:
        walk(formula)
    return out


def count_holds(sequent: list[dict[str, Any]]) -> bool:
    """`2 * tensors + 2 == atoms`, met by every provable sequent."""
    tensors, atoms = 0, 0
    stack = list(sequent)
    while stack:
        formula = stack.pop()
        if formula["kind"] == "atom":
            atoms += 1
        else:
            tensors += formula["kind"] == "tensor"
            stack += [formula["left"], formula["right"]]
    return 2 * tensors + 2 == atoms


def balanced(sequent: list[dict[str, Any]]) -> bool:
    balance: dict[str, int] = {}
    for leaf in leaves(sequent):
        balance[leaf["name"]] = balance.get(leaf["name"], 0) + (1 if leaf["positive"] else -1)
    return all(value == 0 for value in balance.values())


def names_of(sequent: list[dict[str, Any]]) -> list[str]:
    return sorted({leaf["name"] for leaf in leaves(sequent)})


# Countermodels in finite Lukasiewicz chains {0, 1, ..., m}

def lukasiewicz(formula: dict[str, Any], valuation: dict[str, int], m: int) -> int:
    if formula["kind"] == "atom":
        value = valuation[formula["name"]]
        return value if formula["positive"] else m - value
    left, right = lukasiewicz(formula["left"], valuation, m), lukasiewicz(formula["right"], valuation, m)
    return max(0, left + right - m) if formula["kind"] == "tensor" else min(m, left + right)


def certifies(sequent: list[dict[str, Any]], certificate: dict[str, Any]) -> bool:
    """The sequent's par, the truncated sum of its formulas, falls below the top."""
    m, valuation = certificate["m"], certificate["valuation"]
    return sum(lukasiewicz(formula, valuation, m) for formula in sequent) < m


def two_valued(sequent: list[dict[str, Any]]) -> dict[str, int] | None:
    """The first valuation in binary order under which every formula is false; all valuations at once as bitsets."""
    names = names_of(sequent)
    size = 1 << len(names)
    full = (1 << size) - 1
    masks: dict[str, int] = {}
    for index, name in enumerate(names):
        half, length = 1 << index, 1 << (index + 1)
        mask = ((1 << half) - 1) << half
        while length < size:
            mask |= mask << length
            length <<= 1
        masks[name] = mask & full

    def bits(formula: dict[str, Any]) -> int:
        if formula["kind"] == "atom":
            return masks[formula["name"]] if formula["positive"] else full ^ masks[formula["name"]]
        left, right = bits(formula["left"]), bits(formula["right"])
        return left & right if formula["kind"] == "tensor" else left | right

    true_somewhere = 0
    for formula in sequent:
        true_somewhere |= bits(formula)
    if true_somewhere == full:
        return None
    missing = full ^ true_somewhere
    index = (missing & -missing).bit_length() - 1
    return {name: (index >> i) & 1 for i, name in enumerate(names)}


def countermodel(sequent: list[dict[str, Any]]) -> dict[str, Any] | None:
    """The first countermodel in chains of length m + 1 for m = 1..MAX_CHAIN, searched exhaustively where there
    are at most MAX_VALUATIONS valuations."""
    valuation = two_valued(sequent)
    if valuation is not None:
        return {"m": 1, "valuation": valuation}
    names = names_of(sequent)
    for m in range(2, MAX_CHAIN + 1):
        if (m + 1) ** len(names) > MAX_VALUATIONS:
            break
        for values in itertools.product(range(m + 1), repeat=len(names)):
            candidate = {"m": m, "valuation": dict(zip(names, values))}
            if certifies(sequent, candidate):
                return candidate
    return None


# Candidate negatives

def swaps(sequent: list[dict[str, Any]]) -> Iterator[tuple[dict[str, Any], list[dict[str, Any]]]]:
    positions = v1.connective_positions(sequent)
    tensors = [p for p in positions if node_at(sequent, p)["kind"] == "tensor"]
    pars = [p for p in positions if node_at(sequent, p)["kind"] == "par"]
    for tensor in tensors:
        for par in pars:
            yield {"family": "swap", "tensor": tensor, "par": par}, v1.flip_at(v1.flip_at(sequent, tensor), par)


def shuffles(sequent: list[dict[str, Any]], seed: int, start: int, stop: int) -> Iterator[tuple[dict[str, Any], list[dict[str, Any]]]]:
    rng = random.Random(seed)
    atoms = [(leaf["name"], leaf["positive"]) for leaf in leaves(sequent)]
    for index in range(stop):
        order = atoms[:]
        rng.shuffle(order)
        if index < start:
            continue
        shuffled = copy.deepcopy(sequent)
        for leaf, (name, positive) in zip(leaves(shuffled), order):
            leaf["name"], leaf["positive"] = name, positive
        yield {"family": "shuffle", "seed": seed, "index": index}, shuffled


def shuffle_seed(task: dict[str, Any]) -> int:
    return task["seed"] * 10 + v1.MODES.index(task["labelMode"])


def candidates(positive: dict[str, Any], start: int, stop: int) -> list[tuple[dict[str, Any], list[dict[str, Any]]]]:
    """Swaps then shuffles `start` to `stop - 1`; the swaps belong to the first batch only."""
    out = list(swaps(positive["sequent"])) if start == 0 else []
    return out + list(shuffles(positive["sequent"], shuffle_seed(positive), start, stop))


def decide_strict(sequents: list[list[dict[str, Any]]]) -> list[dict[str, Any]]:
    if not sequents:
        return []
    payload = "".join(json.dumps({"id": str(i), "sequent": s}, separators=(",", ":")) + "\n"
                      for i, s in enumerate(sequents))
    rows = v1.lake_exe("proofnet_ir_pruned_search", payload, "--budget-ms", str(CERTIFY_BUDGET_MS), "--strict-only")
    by_id = {row["id"]: row["focusedStrict"] for row in rows}
    return [by_id[str(i)] for i in range(len(sequents))]


def choose_negatives(positives: list[dict[str, Any]]) -> tuple[list[dict[str, Any]], dict[str, Any]]:
    """For each positive, the first unprovable candidate, with its certificate and what preceded it."""
    chosen: dict[str, dict[str, Any]] = {}
    history = {p["id"]: {"provable": 0, "timeout": 0} for p in positives}
    for start, stop in ((0, FIRST_SHUFFLES), (FIRST_SHUFFLES, MAX_SHUFFLES)):
        open_positives = [p for p in positives if p["id"] not in chosen]
        batches = {}
        to_decide: list[list[dict[str, Any]]] = []
        where: list[tuple[str, int]] = []
        for positive in open_positives:
            batch = candidates(positive, start, stop)
            models = []
            for index, (_, sequent) in enumerate(batch):
                model = countermodel(sequent)
                models.append(model)
                if model is not None:
                    break
            batches[positive["id"]] = (batch, models)
            for index, model in enumerate(models):
                if model is None:
                    to_decide.append(batch[index][1])
                    where.append((positive["id"], index))
        decisions: dict[tuple[str, int], dict[str, Any]] = dict(zip(where, decide_strict(to_decide)))
        for positive in open_positives:
            batch, models = batches[positive["id"]]
            for index, model in enumerate(models):
                mutation, sequent = batch[index]
                if model is not None:
                    certificate: dict[str, Any] = {"countermodel": model}
                else:
                    decision = decisions[(positive["id"], index)]
                    if decision["found"]:
                        history[positive["id"]]["provable"] += 1
                        continue
                    if decision["timeout"]:
                        history[positive["id"]]["timeout"] += 1
                        continue
                    certificate = {"search": {"arm": "focusedStrict", "budgetMs": CERTIFY_BUDGET_MS,
                                              "elapsedMs": round(decision["elapsedNs"] / 1e6, 3)}}
                chosen[positive["id"]] = {
                    **{k: positive[k] for k in ("baseId", "seed", "depth", "atoms", "labelMode")},
                    "id": positive["id"].replace("-positive", "-count-negative"),
                    "kind": "negative-count", "expectedProvable": False, "mutation": mutation,
                    "certificate": certificate, "before": dict(history[positive["id"]]), "sequent": sequent,
                }
                break
    missing = [p["id"] for p in positives if p["id"] not in chosen]
    report = {"positives": len(positives), "negatives": len(chosen), "withoutNegative": missing,
              "candidatesTimedOut": sum(h["timeout"] for h in history.values())}
    return [chosen[p["id"]] for p in positives if p["id"] in chosen], report


def with_kind(task: dict[str, Any]) -> dict[str, Any]:
    return {**task, "kind": "positive" if task["expectedProvable"] else "negative-flip"}


def stratum(task: dict[str, Any]) -> str:
    return f"atoms-{task['atoms']}:{task['labelMode']}:{task['kind']}"


# Running the arms

def stream_exe(name: str, tasks: list[dict[str, Any]], partial: Path | None) -> dict[str, dict[str, Any]]:
    payload = "".join(json.dumps({"id": t["id"], "sequent": t["sequent"]}, separators=(",", ":")) + "\n"
                      for t in tasks)
    process = subprocess.Popen([v1.find_lake(), "exe", name, "--budget-ms", str(BUDGET_MS)], cwd=ROOT,
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
                print(f"{name}: {len(rows)}/{len(tasks)}", flush=True)
    if sink:
        sink.close()
    if process.wait() != 0:
        raise SystemExit(f"{name} failed")
    return rows


def run_all(tasks: list[dict[str, Any]], partial_dir: Path | None) -> dict[str, dict[str, Any]]:
    old = stream_exe("proofnet_ir_matched_search", tasks, partial_dir / "v01-arms.partial" if partial_dir else None)
    new = stream_exe("proofnet_ir_pruned_search", tasks, partial_dir / "pruned-arms.partial" if partial_dir else None)
    return {t["id"]: {**old[t["id"]], **new[t["id"]]} for t in tasks}


def compute_results(tasks: list[dict[str, Any]], runs: dict[str, dict[str, Any]]) -> list[dict[str, Any]]:
    rows = []
    for task in tasks:
        run = runs[task["id"]]
        row = {k: task[k] for k in ("id", "baseId", "depth", "atoms", "labelMode", "kind", "expectedProvable")}
        row["stratum"] = stratum(task)
        if task["kind"] == "negative-count":
            row["family"] = task["mutation"]["family"]
            row["certifiedBy"] = "countermodel" if "countermodel" in task["certificate"] else "search"
        for arm in ARMS:
            result = run[arm]
            outcome = v1.outcome_of(result)
            row[arm] = {
                "outcome": outcome,
                "correct": outcome == ("found" if task["expectedProvable"] else "refuted"),
                "elapsedMs": result["elapsedNs"] / 1e6,
                **{k: v for k, v in result.items() if k not in ("found", "refuted", "timeout", "elapsedNs")},
            }
        rows.append(row)
    return rows


# Statistics

def sign_test(wins: int, losses: int) -> dict[str, float]:
    """Exact binomial tests on discordant pairs: one-sided for more wins, and two-sided."""
    n = wins + losses
    if n == 0:
        return {"oneSidedP": 1.0, "twoSidedP": 1.0}
    upper = sum(math.comb(n, k) for k in range(wins, n + 1)) / 2 ** n
    lower = sum(math.comb(n, k) for k in range(0, wins + 1)) / 2 ** n
    return {"oneSidedP": upper, "twoSidedP": min(1.0, 2 * min(upper, lower))}


def paired(members: list[dict[str, Any]], first: str, second: str, success: str) -> dict[str, Any]:
    """Tasks the first arm decides as `success` within the budget and the second does not, and vice versa."""
    hit = {arm: [m[arm]["outcome"] == success for m in members] for arm in (first, second)}
    wins = sum(1 for a, b in zip(hit[first], hit[second]) if a and not b)
    losses = sum(1 for a, b in zip(hit[first], hit[second]) if b and not a)
    return {"first": first, "second": second, "outcome": success, "tasks": len(members),
            "firstCount": sum(hit[first]), "secondCount": sum(hit[second]),
            "firstOnly": wins, "secondOnly": losses, **sign_test(wins, losses)}


def summarize(rows: list[dict[str, Any]], tasks: list[dict[str, Any]]) -> dict[str, Any]:
    strata: dict[str, list[dict[str, Any]]] = {}
    for row in rows:
        strata.setdefault(row["stratum"], []).append(row)
    per_stratum: dict[str, Any] = {}
    for name, members in sorted(strata.items()):
        entry: dict[str, Any] = {"tasks": len(members)}
        if name.endswith("negative-count"):
            entry["families"] = {f: sum(1 for m in members if m["family"] == f) for f in ("swap", "shuffle")}
            entry["certifiedBy"] = {c: sum(1 for m in members if m["certifiedBy"] == c) for c in ("countermodel", "search")}
        for arm in ARMS:
            outcomes = [m[arm]["outcome"] for m in members]
            elapsed = [m[arm]["elapsedMs"] for m in members]
            entry[arm] = {
                "found": outcomes.count("found"), "refuted": outcomes.count("refuted"),
                "timeout": outcomes.count("timeout"),
                "wrong": sum(1 for m in members if m[arm]["outcome"] != "timeout" and not m[arm]["correct"]),
                "medianElapsedMs": statistics.median(elapsed), "maxElapsedMs": max(elapsed),
            }
        per_stratum[name] = entry

    def members(name: str) -> list[dict[str, Any]]:
        return strata.get(name, [])

    def decided(entry: dict[str, Any], arm: str) -> int:
        return entry[arm]["found"] + entry[arm]["refuted"]

    repeated32 = ["atoms-32:two-label:positive", "atoms-32:one-label:positive"]
    h7_every = all(decided(e, "netsPruned") >= decided(e, "nets") for e in per_stratum.values())
    h7_tests = [paired(members(s), "netsPruned", "nets", "found") for s in repeated32]
    h7_more = all(t["firstCount"] > t["secondCount"] for t in h7_tests)
    h8_every = all(decided(e, "focusedStrict") >= decided(e, "focusedBalanced") for e in per_stratum.values())
    one32 = "atoms-32:one-label:positive"
    h9 = paired(members(one32), "focusedStrict", "netsPruned", "found")
    count_one32 = members("atoms-32:one-label:negative-count")
    refuted_by_nets = sum(1 for m in count_one32 if m["netsPruned"]["outcome"] == "refuted")

    flips = [t for t in tasks if t["kind"] == "negative-flip"]
    counted = [t for t in tasks if t["kind"] == "negative-count"]
    return {
        "experiment": "matched-search-v0.2",
        "preregistrationSha256": v1.sha256_file(PREREG) if PREREG.exists() else None,
        "corpusSha256": v1.sha256_file(CORPUS) if CORPUS.exists() else None,
        "budgetMs": BUDGET_MS,
        "tasks": len(rows),
        "wrongAnswers": {arm: sum(1 for r in rows if r[arm]["outcome"] != "timeout" and not r[arm]["correct"])
                         for arm in ARMS},
        "strata": per_stratum,
        "hypotheses": {
            "H68": {"decidedAtLeastEverywhere": h7_every, "morePositivesOnRepeated32": h7_more, "tests": h7_tests,
                   "supported": bool(h7_every and h7_more)},
            "H69": {"supported": h8_every, "test": paired(rows, "focusedStrict", "focusedBalanced", "found")
                   | {"refuted": paired(rows, "focusedStrict", "focusedBalanced", "refuted")}},
            "H70": {"supported": h9["firstCount"] > h9["secondCount"], "test": h9},
            "H71": {"negatives": len(count_one32), "refutedByNetsPruned": refuted_by_nets,
                    "supported": bool(count_one32) and 2 * refuted_by_nets < len(count_one32)},
        },
        "checks": {
            "C15": {"flipNegatives": len(flips),
                    "violatingCount": sum(1 for t in flips if not count_holds(t["sequent"])),
                    "refutedAtRootByNetsPruned": sum(1 for r in rows if r["kind"] == "negative-flip"
                                                     and r["netsPruned"].get("rootRefutation")),
                    "holds": all(not count_holds(t["sequent"]) for t in flips)},
            "C16": {"countNegatives": len(counted),
                    "holds": all(balanced(t["sequent"]) and count_holds(t["sequent"]) and (
                        certifies(t["sequent"], t["certificate"]["countermodel"])
                        if "countermodel" in t["certificate"] else t["certificate"]["search"]["arm"] == "focusedStrict")
                        for t in counted)},
            "C17": {"holds": all(r[arm]["outcome"] == "timeout" or r[arm]["correct"] for r in rows for arm in ARMS)},
        },
        "resultsSha256": v1.sha256_file(RESULTS) if RESULTS.exists() else None,
    }


# Corpus

def v01_tasks() -> list[dict[str, Any]]:
    return [with_kind(json.loads(line)) for line in v1.CORPUS.read_text(encoding="utf-8").splitlines() if line.strip()]


def dev_tasks() -> list[dict[str, Any]]:
    completed = subprocess.run([v1.find_lake(), "exe", "proofnet_ir_pruned_search", "--dev-bases",
                                str(DEV_SEED), str(DEV_PER_DEPTH)], cwd=ROOT, capture_output=True, text=True,
                               encoding="utf-8", check=True)
    bases = [json.loads(line) for line in completed.stdout.splitlines() if line.startswith("{")]
    positives, flips = [], []
    for base in bases:
        for mode in v1.MODES:
            sequent = [v1.rename(f, v1.name_map(base["sequent"], mode)) for f in base["sequent"]]
            positive = {"id": f"dev-{base['id'].split('-')[-1]}-{mode}-positive", "baseId": base["id"],
                        "seed": base["seed"], "depth": base["depth"],
                        "atoms": sum(v1.atom_count(f) for f in sequent), "labelMode": mode,
                        "kind": "positive", "expectedProvable": True, "sequent": sequent}
            positives.append(positive)
            path = v1.connective_positions(sequent)[0]
            flips.append({**{k: positive[k] for k in ("baseId", "seed", "depth", "atoms", "labelMode")},
                          "id": positive["id"].replace("-positive", "-flip-negative"), "kind": "negative-flip",
                          "expectedProvable": False, "sequent": v1.flip_at(sequent, path)})
    negatives, report = choose_negatives(positives)
    print(f"dev: {len(positives)} positives, {len(flips)} flips, {json.dumps(report)[:400]}")
    return positives + flips + negatives


def load_tasks() -> list[dict[str, Any]]:
    return [json.loads(line) for line in CORPUS.read_text(encoding="utf-8").splitlines() if line.strip()]


def build_corpus() -> None:
    old = v01_tasks()
    positives = [t for t in old if t["kind"] == "positive"]
    flips = [t for t in old if t["kind"] == "negative-flip"]
    negatives, report = choose_negatives(positives)
    tasks = positives + flips + negatives
    EXPERIMENT.mkdir(parents=True, exist_ok=True)
    v1.write_lf(CORPUS, "".join(json.dumps(t, separators=(",", ":")) + "\n" for t in tasks))
    print(json.dumps({"tasks": len(tasks), **report}))


def registration_payload(tasks: list[dict[str, Any]]) -> dict[str, Any]:
    strata: dict[str, int] = {}
    for task in tasks:
        strata[stratum(task)] = strata.get(stratum(task), 0) + 1
    counted = [t for t in tasks if t["kind"] == "negative-count"]
    return {
        "experiment": "matched-search-v0.2",
        "question": "when both search spaces get their standard pruning, does label repetition still reverse the "
                    "ranking of net-space and sequent search, and how do the searches fare on negatives that pass "
                    "the linear-time necessary conditions and are certified without the evaluated net searches",
        "arms": {
            "focused": "matched-search-v0.1's arm, unchanged",
            "focusedBalanced": "matched-search-v0.1's arm, unchanged",
            "nets": "matched-search-v0.1's arm, unchanged",
            "focusedStrict": "Andreoli-focused search: eager pars, a positive formula kept in focus through its "
                             "tensors, a positive atom in focus closing only against exactly its dual, negative "
                             "formulas released; every branch must be balanced per name and satisfy 2 * tensors + 2 "
                             "= atoms, and the context splits of a tensor are enumerated as multisets under both",
            "netsPruned": "axiom-linking search refuting unbalanced sequents and those with a tensor count other "
                          "than atoms / 2 - 1 at once; Danos's contraction applied after every axiom, abandoning a "
                          "partial net with a cycle in some switching; the unlinked atom with the fewest partners "
                          "outside its node linked first; each complete linking decided by "
                          "Certificate.unificationCheck",
        },
        "input": "every arm receives only the sequent",
        "budget": {"wallClockMsPerArmPerTask": BUDGET_MS,
                   "process": "proofnet_ir_matched_search runs the three v0.1 arms on every task, then "
                              "proofnet_ir_pruned_search runs netsPruned and focusedStrict; each process runs its "
                              "arms sequentially per task on one core",
                   "machine": "the run shares the machine with other experiments, among them proof-graphs' "
                              "search-v0.8 (eight Lean REPL workers and a local language-model server); outcomes "
                              "far from the budget do not depend on it, and timings are reported as measured"},
        "outcomes": "found, refuted (search exhausted without a proof), timeout",
        "corpus": {
            "path": "experiments/matched-search-v0.2/corpus.jsonl", "sha256": v1.sha256_file(CORPUS),
            "taskCount": len(tasks), "strata": dict(sorted(strata.items())),
            "positivesAndFlips": "matched-search-v0.1's corpus, unchanged",
            "countNegatives": "for each positive, the first unprovable candidate among the exchanges of one tensor "
                              "with one par (tensors, then pars, in preorder) and then up to "
                              f"{MAX_SHUFFLES} shuffles of its atom occurrences seeded by 10 * seed + label mode "
                              "index; unprovability certified by a countermodel in the Lukasiewicz chain {0..m}, "
                              f"m = 1..{MAX_CHAIN}, searched exhaustively over at most {MAX_VALUATIONS} valuations, "
                              f"or else by focusedStrict refuting the candidate within {CERTIFY_BUDGET_MS} ms",
            "countNegativeFamilies": {f: sum(1 for t in counted if t["mutation"]["family"] == f)
                                      for f in ("swap", "shuffle")},
            "countNegativeCertificates": {
                "countermodel": sum(1 for t in counted if "countermodel" in t["certificate"]),
                "search": sum(1 for t in counted if "search" in t["certificate"])},
            "candidatesTimedOutDuringCertification": sum(t["before"]["timeout"] for t in counted),
        },
        "implementationSha256": {name: v1.sha256_file(path) for name, path in IMPLEMENTATIONS.items()},
        "hypotheses": {
            "H7": "netsPruned decides at least as many tasks as nets in every stratum, and finds more positives "
                  "than nets in each of the 32-atom two-label and one-label strata",
            "H8": "focusedStrict decides at least as many tasks as focusedBalanced in every stratum",
            "H9": "in the 32-atom one-label positives, focusedStrict finds more tasks than netsPruned: label "
                  "repetition still reverses the ranking when both searches are pruned",
            "H10": "netsPruned refutes fewer than half of the 32-atom one-label count-preserving negatives",
        },
        "checks": {
            "C15": "every connective-flip negative violates 2 * tensors + 2 = atoms, so it is refutable in linear "
                   "time; netsPruned refutes each at its root check",
            "C16": "every count-preserving negative is balanced, satisfies the count, and carries a countermodel "
                   "that verifies or a focusedStrict refutation",
            "C17": "no arm gives a wrong answer",
        },
        "tests": "exact sign tests on discordant tasks for H7 and H9 are reported with the counts; the "
                 "hypotheses are decided by the counts as stated",
        "certificationNote": "focusedStrict certified the count-preserving negatives that have no countermodel, "
                             "before this registration; its refutations of those negatives are therefore not an "
                             "independent measurement, and no hypothesis rests on them",
        "developmentChecksBeforeRegistration": [
            "14 hand-made sequents through all five arms, every outcome correct",
            "a development set of 24 generated bases (seeds 900000 onward, eight per depth) in three label modes: "
            "all five arms, twice (before and after Danos's contraction was added to netsPruned), no wrong answer",
            "a forward-checking variant of netsPruned's partner choice, tried on the development positives and "
            "dropped (6 of 16 32-atom repeated-label positives without it, 5 with it)",
            "yields of candidate families on the development positives: swaps, polarity exchanges, and shuffles, "
            "decided by focusedStrict at 20 s without a timeout",
            "the final pipeline end to end on the development set: 213 tasks with 69 count-preserving negatives "
            "(3 one-label positives without one), no candidate timed out, no wrong answer",
        ],
        "resultsAbsentAtRegistration": True,
        "registeredLocalDate": "2026-09-27 America/Los_Angeles",
    }


def write_report(summary: dict[str, Any]) -> None:
    lines = ["# Matched search v0.2: pruned arms and count-preserving negatives", "",
             f"Five arms, the sequent as the only input, {summary['budgetMs']} ms of wall clock per arm per task; "
             "definitions, corpus, and hypotheses are frozen in",
             f"`preregistration.json` (SHA-256 `{summary['preregistrationSha256']}`).", "",
             f"Tasks: {summary['tasks']}. Wrong answers: {summary['wrongAnswers']}.", "",
             "Cells: found/refuted/timeout (median ms).", "",
             "| Stratum | Tasks | " + " | ".join(ARMS) + " |", "| --- | ---: |" + " --- |" * len(ARMS)]
    for name, entry in summary["strata"].items():
        cells = [f"{entry[a]['found']}/{entry[a]['refuted']}/{entry[a]['timeout']} ({entry[a]['medianElapsedMs']:.2f})"
                 for a in ARMS]
        lines.append(f"| {name} | {entry['tasks']} | " + " | ".join(cells) + " |")
    h = summary["hypotheses"]
    lines += ["", "## Hypotheses", "",
              "Registered as H7 to H10; relabeled H68 to H71 by `amendment-1.json`, statements unchanged.", "",
              f"- H68 (netsPruned decides at least as many as nets everywhere and finds more 32-atom repeated-label "
              f"positives): supported: {h['H68']['supported']}; tests: "
              + "; ".join(f"{t['firstCount']} vs {t['secondCount']} (one-sided p {t['oneSidedP']:.3g})" for t in h["H68"]["tests"]) + ".",
              f"- H69 (focusedStrict decides at least as many as focusedBalanced everywhere): supported: {h['H69']['supported']}.",
              f"- H70 (focusedStrict finds more 32-atom one-label positives than netsPruned): supported: "
              f"{h['H70']['supported']}; {h['H70']['test']['firstCount']} vs {h['H70']['test']['secondCount']} "
              f"(one-sided p {h['H70']['test']['oneSidedP']:.3g}).",
              f"- H71 (netsPruned refutes fewer than half of the 32-atom one-label count-preserving negatives): "
              f"supported: {h['H71']['supported']}; {h['H71']['refutedByNetsPruned']} of {h['H71']['negatives']}.",
              "", "## Checks", "", f"- C15: {summary['checks']['C15']}", f"- C16: {summary['checks']['C16']}",
              f"- C17: {summary['checks']['C17']}", "", "## Interpretation boundary", "",
              "Unit-free, cut-free MLL sequents under one budget on one machine. focusedStrict certified the",
              "count-preserving negatives that have no countermodel, so its refutations of those are not an",
              "independent measurement. Nothing here concerns proof assistants at the scale of Lean or Mathlib."]
    v1.write_lf(REPORT, "\n".join(lines) + "\n")


def verify_frozen() -> dict[str, Any]:
    prereg = json.loads(PREREG.read_text(encoding="utf-8"))
    if prereg["corpus"]["sha256"] != v1.sha256_file(CORPUS):
        raise SystemExit("corpus changed since registration")
    for name in ("prunedArms", "v01Arms", "baseGenerator"):
        if prereg["implementationSha256"][name] != v1.sha256_file(IMPLEMENTATIONS[name]):
            raise SystemExit(f"implementation {name} changed since registration")
    return prereg


def main() -> int:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--dev", action="store_true")
    mode.add_argument("--build-corpus", action="store_true")
    mode.add_argument("--register", action="store_true")
    mode.add_argument("--run", action="store_true")
    mode.add_argument("--check-committed", action="store_true")
    mode.add_argument("--summarize", action="store_true")
    args = parser.parse_args()

    if args.dev:
        tasks = dev_tasks()
        rows = compute_results(tasks, run_all(tasks, None))
        summary = summarize(rows, tasks)
        print(json.dumps({k: summary[k] for k in ("tasks", "wrongAnswers", "hypotheses", "checks")}, indent=1))
        for name, entry in summary["strata"].items():
            print(name, entry["tasks"], {arm: (entry[arm]["found"], entry[arm]["refuted"], entry[arm]["timeout"],
                                               round(entry[arm]["medianElapsedMs"], 2)) for arm in ARMS})
        return 0
    if args.build_corpus:
        if PREREG.exists():
            raise SystemExit("the corpus is frozen by the registration")
        build_corpus()
        return 0
    tasks = load_tasks()
    if args.register:
        if RESULTS.exists() or SUMMARY.exists():
            raise SystemExit("results already exist; registration must precede them")
        v1.write_lf(PREREG, json.dumps(registration_payload(tasks), indent=1, sort_keys=True) + "\n")
        print(f"registered {len(tasks)} tasks: {PREREG}")
        return 0
    verify_frozen()
    if args.summarize:
        rows = [json.loads(line) for line in RESULTS.read_text(encoding="utf-8").splitlines() if line.strip()]
        summary = summarize(rows, tasks)
        v1.write_lf(SUMMARY, json.dumps(summary, indent=1) + "\n")
        write_report(summary)
        print(json.dumps(summary["hypotheses"])[:2000])
        return 0
    if args.run:
        rows = compute_results(tasks, run_all(tasks, EXPERIMENT))
        v1.write_lf(RESULTS, "".join(json.dumps(r, separators=(",", ":")) + "\n" for r in rows))
        for partial in EXPERIMENT.glob("*.partial"):
            partial.unlink()
        summary = summarize(rows, tasks)
        v1.write_lf(SUMMARY, json.dumps(summary, indent=1) + "\n")
        write_report(summary)
        print(f"matched-search-v0.2: tasks={summary['tasks']} wrong={summary['wrongAnswers']}")
        return 0

    committed = [json.loads(line) for line in RESULTS.read_text(encoding="utf-8").splitlines() if line.strip()]
    if [row["id"] for row in committed] != [task["id"] for task in tasks]:
        raise SystemExit("committed result ids differ from the corpus")
    fast_ids = {row["id"] for row in committed if all(row[arm]["elapsedMs"] <= CHECK_MAX_ELAPSED_MS for arm in ARMS)}
    fast = [t for t in tasks if t["id"] in fast_ids]
    reruns = compute_results(fast, run_all(fast, None))
    by_id = {row["id"]: row for row in committed}
    for row in reruns:
        for arm in ARMS:
            if row[arm]["outcome"] != by_id[row["id"]][arm]["outcome"]:
                raise SystemExit(f"recomputed outcome differs for {row['id']} {arm}")
    summary = json.loads(SUMMARY.read_text(encoding="utf-8"))
    if summary != json.loads(json.dumps(summarize(committed, tasks))):
        raise SystemExit("the committed summary does not follow from the results")
    if not all(summary["checks"][c]["holds"] for c in ("C15", "C16", "C17")):
        raise SystemExit("a registered check fails")
    print(f"matched-search-v0.2-check-ok: tasks={len(committed)} rerun={len(fast)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
