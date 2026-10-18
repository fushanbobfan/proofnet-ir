#!/usr/bin/env python3
"""Revisit witness v0.2: branch-level witnesses for a sample of the focused search's splits revisits.

  python scripts/run_revisit_witness_v2.py --dev
  python scripts/run_revisit_witness_v2.py --register
  python scripts/run_revisit_witness_v2.py --run
  python scripts/run_revisit_witness_v2.py --summarize
  python scripts/run_revisit_witness_v2.py --check-committed

revisit-provenance-v0.1 put a revisit in the splits class when no earlier branch to its query applied the same rules
with the same splits and some earlier branch decomposed the same tensors, and read the class as excluding rule order,
which put the share of revisits that rule order accounts for at 66.7% or less. A query can have several earlier
branches, and the class speaks for one of them: on a sequent constructed outside the corpus (the review of
2026-10-18), the one splits revisit has a reordering witness against one earlier branch and an exclusion witness
against the other. `proofnet_ir_revisit_witness_splits` runs revisit-witness-v0.1's search with its control flow
unchanged and writes out a stratified sample of the splits revisits, which this script examines branch against
branch with revisit-witness-v0.1's code: reorder, exclusion, alike, or unresolved. With both non-permutation classes
examined, the identification interval for rule order runs from (permutations + tensors revisits x their reorder share
+ splits revisits x their reorder share) / revisits to (revisits - tensors revisits x their exclusion share - splits
revisits x their exclusion share) / revisits, the tensors revisits' shares from revisit-witness-v0.1's committed sample.

`--dev` runs the search on matched-search-v0.2's development set, none of it in the corpus, and on the constructed
sequent, and prints the checks and the counts of sampled and rebuilt revisits. `--check-committed` verifies hashes
and the summary, reruns the tasks that finished within 200 ms, and reruns the constructed sequent.
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
import run_revisit_witness as rw  # noqa: E402

ROOT = v1.ROOT
EXPERIMENT = ROOT / "experiments" / "revisit-witness-v0.2"
CORPUS = v2.CORPUS
REVISITS = rw.REVISITS
PROVENANCE = rw.PROVENANCE
WITNESS_V01 = rw.RESULTS
PREREG = EXPERIMENT / "preregistration.json"
CONSTRUCTED = EXPERIMENT / "constructed.json"
RESULTS = EXPERIMENT / "results.jsonl.gz"
SUMMARY = EXPERIMENT / "summary.json"
REPORT = EXPERIMENT / "report.md"
EXE = "proofnet_ir_revisit_witness_splits"
IMPLEMENTATIONS = {"search": ROOT / "ProofNetIRRevisitWitnessSplits.lean", "witness": ROOT / "scripts" / "run_revisit_witness.py",
                   "runner": Path(__file__).resolve()}
BUDGET_MS = rw.BUDGET_MS
CHECK_MAX_ELAPSED_MS = rw.CHECK_MAX_ELAPSED_MS
COUNTERS, CLASS_FIELDS, WITNESS, RATES = rw.COUNTERS, rw.CLASS_FIELDS, rw.WITNESS, rw.RATES
BOOTSTRAP_SEED = 20261018
BOOTSTRAP_RESAMPLES = rw.BOOTSTRAP_RESAMPLES


def atom(name: str, positive: bool) -> dict[str, Any]:
    return {"kind": "atom", "name": name, "positive": positive}


def tensor(left: dict[str, Any], right: dict[str, Any]) -> dict[str, Any]:
    return {"kind": "tensor", "left": left, "right": right}


# The review's sequent: (c- * d-), (a- * b-), (c+ * b+), a+, d+, (z+ * z-). Not provable: z+ * z- cannot be split.
CONSTRUCTED_TASK = {"id": "constructed-review-2026-10-18", "samplePerMille": 1000, "sequent": [
    tensor(atom("c", False), atom("d", False)), tensor(atom("a", False), atom("b", False)),
    tensor(atom("c", True), atom("b", True)), atom("a", True), atom("d", True),
    tensor(atom("z", True), atom("z", False))]}

QUESTION = ("of the focused search's splits revisits on the count-preserving negatives, how many have a reordering "
            "witness against some earlier branch to the same sub-sequent and how many contradict every earlier branch, "
            "and between which limits does rule order account for the revisits once both classes that are not "
            "permutations have been examined branch against branch")
HYPOTHESES = {
    "H125": "on the count-preserving negatives with unique labels (all sizes pooled), at least one sampled splits revisit "
            "has a reordering witness",
    "H126": "on the count-preserving negatives with unique labels (all sizes pooled), at least half of the sampled splits "
            "revisits whose branches can be compared (a witness other than alike) have an exclusion witness",
}
CHECKS = {
    "C55": "the search reproduces focused-revisits-v0.1's outcome and eight counters, and revisit-provenance-v0.1's six "
           "class counts, on every task",
    "C56": "every branch of every sampled splits revisit, rebuilt from the input sequent rule by rule, reaches the "
           "revisited query",
    "C57": "on the review's constructed sequent, outside the corpus, the search records two permutation, one splits and "
           "three tensors revisits, all in the sequent table, and the splits revisit has a reordering witness",
}
DEVELOPMENT_CHECKS = [
    "the constructed sequent of the review of 2026-10-18 was run through revisit-witness-v0.1's committed executable "
    "(class counts 2, 1, 3) and through this search, whose splits revisit was classed with revisit-witness-v0.1's code "
    "(witnesses reorder and exclusion against its two earlier branches, so reorder)",
]
KNOWN = ("before registration: revisit-provenance-v0.1's class counts by stratum, revisit-witness-v0.1's summary (its "
         "tensors revisits' witnesses), and the constructed sequent's classes; no splits revisit of the corpus had been "
         "sampled or classed")


# ---------------------------------------------------------------- running


def rate(task: dict[str, Any]) -> int:
    return rw.rate(task)


def stream(tasks: list[dict[str, Any]], partial: Path | None, exe: str = EXE) -> dict[str, dict[str, Any]]:
    payload = "".join(json.dumps({"id": t["id"], "sequent": t["sequent"],
                                  "samplePerMille": t.get("samplePerMille", rate(t) if "kind" in t else 0)},
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


def classed_samples(task: dict[str, Any], result: dict[str, Any]) -> list[dict[str, Any]]:
    multiplicity = Counter(k for f in task["sequent"] for k in rw.subformula_keys(f))
    out = []
    for record in result["samples"]:
        ok = rw.rebuilds(record, task, result["keys"])
        out.append(record | {"rebuilt": ok,
                             "witness": rw.classify(record, task, result["keys"], multiplicity) if ok else None})
    return out


def compute_results(tasks: list[dict[str, Any]], runs: dict[str, dict[str, Any]]) -> list[dict[str, Any]]:
    rows = []
    for task in tasks:
        result = runs[task["id"]]["strictMemo"]
        row = {k: task[k] for k in ("id", "baseId", "depth", "atoms", "labelMode", "kind", "expectedProvable")}
        row["stratum"] = v2.stratum(task)
        row["samplePerMille"] = rate(task)
        row["strictMemo"] = {"outcome": v1.outcome_of(result), "elapsedMs": result["elapsedNs"] / 1e6,
                             **{k: result[k] for k in (*COUNTERS, *CLASS_FIELDS, "splitsRevisits")},
                             "keys": result["keys"], "samples": classed_samples(task, result)}
        rows.append(row)
    return rows


def constructed_run() -> dict[str, Any]:
    result = stream([CONSTRUCTED_TASK], None)[CONSTRUCTED_TASK["id"]]["strictMemo"]
    return {"source": "the constructed sequent of the review of 2026-10-18, outside the corpus",
            "sequent": CONSTRUCTED_TASK["sequent"],
            "strictMemo": {**{k: result[k] for k in (*COUNTERS, *CLASS_FIELDS, "splitsRevisits")},
                           "keys": result["keys"], "samples": classed_samples(CONSTRUCTED_TASK, result)}}


def constructed_holds(record: dict[str, Any]) -> bool:
    m = record["strictMemo"]
    classes = tuple(m[k] for k in CLASS_FIELDS)
    return classes == (2, 1, 3, 0, 0, 0) and [s["witness"] for s in m["samples"]] == ["reorder"]


# ---------------------------------------------------------------- summary


def splits_shares(rows: list[dict[str, Any]]) -> tuple[dict[str, float | None], Counter]:
    """Each witness class's share of a group's sampled splits revisits, a task's sample weighted by the inverse of
    its rate, and the unweighted counts."""
    weighted: Counter = Counter()
    sampled: Counter = Counter()
    for r in rows:
        weight = 1000 / r["samplePerMille"] if r["samplePerMille"] else 0
        for s in r["strictMemo"]["samples"]:
            if s["rebuilt"]:
                weighted[s["witness"]] += weight
                sampled[s["witness"]] += 1
    total = sum(weighted.values())
    return {w: weighted[w] / total if total else None for w in WITNESS}, sampled


def group(rows: list[dict[str, Any]], v01_by_id: dict[str, dict[str, Any]]) -> dict[str, Any]:
    """The group's splits witnesses, and the interval for rule order with both classes examined."""
    shares, sampled = splits_shares(rows)
    tensors_side = rw.witness_shares([v01_by_id[r["id"]] for r in rows])
    t = tensors_side["witnessShares"]
    memo = [r["strictMemo"] for r in rows]
    revisits = sum(m["cacheHits"] for m in memo)
    tensors, permutations, splits = (sum(f(m) for m in memo) for f in (rw.tensors_of, rw.permutations_of,
                                                                       rw.splits_of))
    interval = None
    if revisits and (not tensors or t["reorder"] is not None) and (not splits or shares["reorder"] is not None):
        def part(share: float | None, count: int) -> float:
            return count * share if count else 0.0
        low = (permutations + part(t["reorder"], tensors) + part(shares["reorder"], splits)) / revisits
        high = (revisits - part(t["exclusion"], tensors) - part(shares["exclusion"], splits)) / revisits
        interval = [low, high]
    return {"tasks": len(rows), "revisits": revisits, "permutations": permutations, "splitsRevisits": splits,
            "tensorsRevisits": tensors, "sampled": sum(sampled.values()), "sampledByWitness": {w: sampled[w] for w in WITNESS},
            "witnessShares": shares, "tensorsWitnessShares": t, "ruleOrderInterval": interval,
            "intervalWithSplitsExcluded": tensors_side["ruleOrderInterval"]}


def comparable_exclusion(rows: list[dict[str, Any]]) -> float | None:
    shares, _ = splits_shares(rows)
    if shares["exclusion"] is None:
        return None
    comparable = sum(shares[w] for w in ("reorder", "exclusion", "unresolved"))
    return shares["exclusion"] / comparable if comparable else None


def bootstrap(rows: list[dict[str, Any]], statistic) -> list[float] | None:
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


def summarize(rows: list[dict[str, Any]], v01_rows: list[dict[str, Any]], provenance_rows: list[dict[str, Any]],
              witness_rows: list[dict[str, Any]], constructed: dict[str, Any]) -> dict[str, Any]:
    v01_by_id = {r["id"]: r for r in witness_rows}
    negatives = [r for r in rows if r["kind"] == "negative-count"]
    unique = [r for r in negatives if r["labelMode"] == "unique"]
    out: dict[str, Any] = {"experiment": "revisit-witness-v0.2", "tasks": len(rows), "negatives": group(negatives, v01_by_id),
                           "strata": {}, "byLabelMode": {}}
    for name in sorted({r["stratum"] for r in negatives}):
        out["strata"][name] = group([r for r in negatives if r["stratum"] == name], v01_by_id)
    for mode in ("unique", "two-label", "one-label"):
        out["byLabelMode"][mode] = group([r for r in negatives if r["labelMode"] == mode], v01_by_id)
    u = out["byLabelMode"]["unique"]
    exclusion = comparable_exclusion(unique)
    out["hypotheses"] = {
        "H125": {"reorder": u["sampledByWitness"]["reorder"], "sampled": u["sampled"],
                 "holds": u["sampledByWitness"]["reorder"] >= 1},
        "H126": {"exclusionShareOfComparable": exclusion, "sampledByWitness": u["sampledByWitness"],
                 "interval": bootstrap(unique, comparable_exclusion),
                 "holds": exclusion is not None and exclusion >= 0.5},
    }
    v01 = {r["id"]: r["strictMemo"] for r in v01_rows}
    prov = {r["id"]: r["strictMemo"] for r in provenance_rows}
    mismatches = [r["id"] for r in rows if r["strictMemo"]["outcome"] != v01[r["id"]]["outcome"]
                  or any(r["strictMemo"][k] != v01[r["id"]][k] for k in COUNTERS)
                  or any(r["strictMemo"][k] != prov[r["id"]][k] for k in CLASS_FIELDS)]
    unbuilt = [(r["id"], s["rank"]) for r in rows for s in r["strictMemo"]["samples"] if not s["rebuilt"]]
    out["checks"] = {
        "C55": {"compared": len(rows), "mismatches": mismatches[:20], "mismatchCount": len(mismatches),
                "holds": not mismatches},
        "C56": {"sampled": sum(len(r["strictMemo"]["samples"]) for r in rows), "notRebuilt": unbuilt[:20],
                "notRebuiltCount": len(unbuilt), "holds": not unbuilt},
        "C57": {"classes": {k: constructed["strictMemo"][k] for k in CLASS_FIELDS},
                "witnesses": [s["witness"] for s in constructed["strictMemo"]["samples"]],
                "holds": constructed_holds(constructed)},
    }
    return out


def write_report(summary: dict[str, Any]) -> None:
    def pct(x: float | None) -> str:
        return "n/a" if x is None else f"{100 * x:.1f}%"

    lines = ["# Splits revisits examined branch against branch (revisit-witness v0.2)", "",
             f"Tasks: {summary['tasks']}.", "",
             "| Count-preserving negatives | revisits | splits revisits | sampled | reorder | exclusion | alike | "
             "unresolved | rule order, both classes examined |", "|---|---:|---:|---:|---:|---:|---:|---:|---|"]
    for name, e in [("all", summary["negatives"]), *summary["strata"].items()]:
        s, iv = e["sampledByWitness"], e["ruleOrderInterval"]
        lines.append(f"| {name} | {e['revisits']} | {e['splitsRevisits']} | {e['sampled']} | {s['reorder']} | "
                     f"{s['exclusion']} | {s['alike']} | {s['unresolved']} | "
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


def registration_payload(tasks: list[dict[str, Any]], dev: dict[str, Any]) -> dict[str, Any]:
    return {
        "experiment": "revisit-witness-v0.2", "question": QUESTION,
        "registeredLocalDate": time.strftime("%Y-%m-%d") + " America/Los_Angeles",
        "corpus": {"path": "experiments/matched-search-v0.2/corpus.jsonl", "sha256": v1.sha256_file(CORPUS),
                   "tasks": len(tasks)},
        "comparedResults": {"focusedRevisits": v1.sha256_file(REVISITS), "revisitProvenance": v1.sha256_file(PROVENANCE),
                            "revisitWitnessV01": v1.sha256_file(WITNESS_V01)},
        "search": "revisit-witness-v0.1's search, copied into ProofNetIRRevisitWitnessSplits.lean with its control flow "
                  "unchanged; it writes out splits revisits where revisit-witness-v0.1 wrote out tensors revisits",
        "sample": {"rule": "a splits revisit is written out when splitmix64 of the task id's hash xor the mixed rank of "
                           "the revisit among the task's splits revisits, modulo 1000, is below the task's rate per "
                           "mille", "ratesPerMille": RATES, "tasks": "the count-preserving negatives only"},
        "definitions": "revisit-witness-v0.1's (reorder, exclusion, alike, unresolved), applied by its own code "
                       "(scripts/run_revisit_witness.py, compare and classify) to each sampled splits revisit",
        "measures": {"witnessShares": "each class's share of a group's sampled splits revisits, a task's sample weighted "
                                      "by the inverse of its rate",
                     "ruleOrderInterval": "from (permutations + tensors revisits x their reorder share + splits revisits x "
                                          "their reorder share) / revisits to (revisits - tensors revisits x their "
                                          "exclusion share - splits revisits x their exclusion share) / revisits; the "
                                          "tensors revisits' shares are revisit-witness-v0.1's, over the same tasks"},
        "budget": {"wallClockMsPerTask": BUDGET_MS, "process": f"{EXE} runs the tasks sequentially, on one core"},
        "hypotheses": HYPOTHESES, "checks": CHECKS,
        "tests": f"the hypotheses are decided by the rules as stated; shares are reported with percentile bootstrap "
                 f"intervals over tasks (seed {BOOTSTRAP_SEED}, {BOOTSTRAP_RESAMPLES} resamples), which do not decide",
        "implementationSha256": {name: v1.sha256_file(path) for name, path in IMPLEMENTATIONS.items()},
        "developmentChecksBeforeRegistration": DEVELOPMENT_CHECKS + [dev["note"]],
        "knownBeforeRegistration": KNOWN,
        "resultsAbsentAtRegistration": True,
    }


def dev_check() -> dict[str, Any]:
    tasks = v2.dev_tasks()
    rows = compute_results(tasks, stream(tasks, None))
    old = rw.stream(rw.V01_EXE, tasks, None)
    prov = rw.stream(rw.PROVENANCE_EXE, tasks, None)
    mismatches = [t["id"] for t, r in zip(tasks, rows)
                  if r["strictMemo"]["outcome"] != v1.outcome_of(old[t["id"]]["strictMemo"])
                  or any(r["strictMemo"][k] != old[t["id"]]["strictMemo"][k] for k in COUNTERS)
                  or any(r["strictMemo"][k] != prov[t["id"]]["strictMemo"][k] for k in CLASS_FIELDS)]
    sampled = sum(len(r["strictMemo"]["samples"]) for r in rows)
    unbuilt = sum(1 for r in rows for s in r["strictMemo"]["samples"] if not s["rebuilt"])
    constructed = constructed_run()
    note = (f"matched-search-v0.2's development set ({len(tasks)} tasks, none in the corpus) through this search, "
            f"revisit-provenance-v0.1's and focused-revisits-v0.1's: outcomes, counters, and class counts agree on "
            f"{len(tasks) - len(mismatches)} of {len(tasks)} tasks; {sampled} splits revisits were sampled and "
            f"{sampled - unbuilt} rebuilt; only these counts were printed, and no witness class of the development set "
            f"was looked at")
    return {"tasks": len(tasks), "mismatches": mismatches, "sampled": sampled, "notRebuilt": unbuilt,
            "constructedHolds": constructed_holds(constructed), "constructed": constructed, "note": note}


# ---------------------------------------------------------------- main


def main() -> int:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    for flag in ("--dev", "--register", "--run", "--summarize", "--check-committed"):
        mode.add_argument(flag, action="store_true")
    args = parser.parse_args()
    if args.dev:
        dev = dev_check()
        print(json.dumps({k: v for k, v in dev.items() if k != "constructed"}, indent=1))
        return 0
    tasks = v2.load_tasks()
    if args.register:
        if RESULTS.exists() or SUMMARY.exists():
            raise SystemExit("results already exist; registration must precede them")
        dev = dev_check()
        if dev["mismatches"] or dev["notRebuilt"] or not dev["constructedHolds"]:
            raise SystemExit(f"development checks fail: {json.dumps({k: v for k, v in dev.items() if k != 'constructed'})}")
        EXPERIMENT.mkdir(parents=True, exist_ok=True)
        v1.write_lf(CONSTRUCTED, json.dumps(dev["constructed"], indent=1, sort_keys=True) + "\n")
        v1.write_lf(PREREG, json.dumps(registration_payload(tasks, dev), indent=1, sort_keys=True) + "\n")
        print(f"registered {len(tasks)} tasks: {PREREG}")
        return 0
    prereg = json.loads(PREREG.read_text(encoding="utf-8"))
    if prereg["corpus"]["sha256"] != v1.sha256_file(CORPUS):
        raise SystemExit("corpus changed since registration")
    for name in ("search", "witness"):
        if prereg["implementationSha256"][name] != v1.sha256_file(IMPLEMENTATIONS[name]):
            raise SystemExit(f"the {name} code changed since registration")
    v01_rows, provenance_rows = rw.load_rows(REVISITS), rw.load_rows(PROVENANCE)
    witness_rows = rw.load_rows(WITNESS_V01)
    constructed = json.loads(CONSTRUCTED.read_text(encoding="utf-8"))
    if args.run:
        rows = compute_results(tasks, stream(tasks, EXPERIMENT / "search.partial"))
        RESULTS.write_bytes(gzip.compress("".join(json.dumps(r, separators=(",", ":")) + "\n" for r in rows)
                                          .encode("utf-8"), compresslevel=9, mtime=0))
        (EXPERIMENT / "search.partial").unlink(missing_ok=True)
    if args.run or args.summarize:
        summary = summarize(rw.load_rows(RESULTS), v01_rows, provenance_rows, witness_rows, constructed)
        v1.write_lf(SUMMARY, json.dumps(summary, indent=1) + "\n")
        write_report(summary)
        print(json.dumps({k: {"holds": v["holds"]} for k, v in summary["hypotheses"].items()}),
              json.dumps({k: v["holds"] for k, v in summary["checks"].items()}))
        return 0
    if constructed_run() != constructed:
        raise SystemExit("the constructed sequent no longer gives the committed record")
    if not RESULTS.exists():
        print("revisit-witness-v0.2: registered, no results yet")
        return 0
    committed = rw.load_rows(RESULTS)
    if [row["id"] for row in committed] != [task["id"] for task in tasks]:
        raise SystemExit("committed result ids differ from the corpus")
    fast = [t for t, row in zip(tasks, committed) if row["strictMemo"]["elapsedMs"] <= CHECK_MAX_ELAPSED_MS]
    by_id = {row["id"]: row for row in committed}
    for row in compute_results(fast, stream(fast, None)):
        old = by_id[row["id"]]["strictMemo"]
        if any(row["strictMemo"][k] != old[k] for k in ("outcome", *CLASS_FIELDS, "splitsRevisits")) \
                or row["strictMemo"]["samples"] != old["samples"]:
            raise SystemExit(f"recomputed results differ for {row['id']}")
    summary = json.loads(SUMMARY.read_text(encoding="utf-8"))
    if summary != json.loads(json.dumps(summarize(committed, v01_rows, provenance_rows, witness_rows, constructed))):
        raise SystemExit("the committed summary does not follow from the results")
    print(f"revisit-witness-v0.2-check-ok: tasks={len(committed)} rerun={len(fast)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
