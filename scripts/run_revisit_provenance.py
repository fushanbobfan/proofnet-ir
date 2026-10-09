#!/usr/bin/env python3
"""Revisit provenance v0.1: where the revisits of the strictly focused search come from.

  python scripts/run_revisit_provenance.py --dev
  python scripts/run_revisit_provenance.py --register
  python scripts/run_revisit_provenance.py --run
  python scripts/run_revisit_provenance.py --summarize
  python scripts/run_revisit_provenance.py --check-committed

focused-revisits-v0.1 found that most queries of a large focused refutation are revisits, answered from a memo table.
A revisit shows that a query recurred, not why. `proofnet_ir_revisit_provenance` runs that experiment's `strictMemo`
with its control flow unchanged and gives every query its branch: the tensor rules applied on the way to it, each with
the premise it enters and the multiset of formulas it sends to the other premise. A revisit is classed against the
branches that met the same query before: a permutation (an earlier branch applied the same rules with the same splits
in another order, the redundancy of commuting foci that proof nets and maximal multi-focusing remove), the same
tensors split differently, or other tensors.

`--dev` runs the search, and focused-revisits-v0.1's, on matched-search-v0.2's development bases, none of them in the
corpus, and prints only the checks and the decided counts. `--check-committed` verifies hashes, ids, and the summary,
and reruns the tasks that finished within 200 ms.
"""

from __future__ import annotations

import argparse
import json
import random
import statistics
import subprocess
import sys
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parent))
import run_matched_search as v1  # noqa: E402
import run_pruned_search as v2  # noqa: E402

ROOT = v1.ROOT
EXPERIMENT = ROOT / "experiments" / "revisit-provenance-v0.1"
CORPUS = v2.CORPUS
REVISITS = ROOT / "experiments" / "focused-revisits-v0.1" / "results.jsonl"
PREREG = EXPERIMENT / "preregistration.json"
RESULTS = EXPERIMENT / "results.jsonl"
SUMMARY = EXPERIMENT / "summary.json"
REPORT = EXPERIMENT / "report.md"
EXE = "proofnet_ir_revisit_provenance"
V01_EXE = "proofnet_ir_focused_revisits"
IMPLEMENTATIONS = {
    "search": ROOT / "ProofNetIRRevisitProvenance.lean",
    "runner": ROOT / "scripts" / "run_revisit_provenance.py",
}
BUDGET_MS = 5000
CHECK_MAX_ELAPSED_MS = 200
COUNTERS = ("proveCalls", "focusCalls", "cacheHits", "proveHits", "focusHits", "decides", "splits", "infeasible")
CLASSES = ("permutation", "splits", "tensors")
BOOTSTRAP_SEED = 20261009
BOOTSTRAP_RESAMPLES = 10_000

QUESTION = ("where the revisits of the strictly focused search come from: how many are permutations of an earlier "
            "branch, the same tensor rules with the same splits in another order, which is the redundancy of commuting "
            "foci that proof nets and maximal multi-focusing remove, and how many decompose the same tensors with other "
            "splits, or other tensors")
DEFINITIONS = {
    "query": "as in focused-revisits-v0.1: a call of prove (a sequent after eager par decomposition, as a sorted "
             "multiset of formula keys) or of focus on a tensor goal (its context and goal)",
    "branch": "the tensor rules applied between the input and a query, each recorded as the tensor, the premise the "
              "branch enters, and the multiset of formulas the rule sends to the other premise (a positive atom that "
              "closes against its dual sends that dual); pars, decided deterministically, are not recorded",
    "permutation": "a revisit for which some earlier branch to the same query recorded the same multiset of rules",
    "splits": "a revisit that is not a permutation, for which some earlier branch decomposed the same multiset of "
              "tensors",
    "tensors": "any other revisit: every earlier branch decomposed a different multiset of tensors",
    "identity": "branches are compared by two order-independent sums of 64-bit hashes (splitmix64-finalized) of their "
                "rules, and of their tensors; formulas are compared by their keys, as the memo tables compare them, so "
                "alike formulas are not told apart",
}
HYPOTHESES = {
    "H94": "over the count-preserving negatives, at least half of the revisits are permutations (pooled share of "
           "permutation revisits among all revisits >= 0.5)",
    "H95": "on the 32-atom count-preserving negatives with unique labels, where no two formulas are alike, at least "
           "half of the revisits are permutations",
    "H96": "on the 32-atom count-preserving negatives, the pooled share of permutations among revisits is lower with "
           "one label than with unique labels",
}
CHECKS = {
    "C35": "the search reproduces focused-revisits-v0.1's strictMemo on every task: the same outcome and the same "
           "eight counters (proveCalls, focusCalls, cacheHits, proveHits, focusHits, decides, splits, infeasible)",
    "C36": "on every task the three classes add up to the hits of each table",
}
MEASURES = {
    "revisits": "cacheHits, the queries answered from a table (proveHits + focusHits)",
    "queries": "proveCalls + focusCalls + cacheHits",
    "classShare": "a class's revisits over all revisits, pooled over a group of tasks (sums over sums), also by table",
    "permutationShareOfQueries": "permutation revisits over all queries, pooled: the queries a search that identified "
                                 "commuting foci would not have met again",
}


# Running

def stream(exe: str, tasks: list[dict[str, Any]], partial: Path | None) -> dict[str, dict[str, Any]]:
    payload = "".join(json.dumps({"id": t["id"], "sequent": t["sequent"]}, separators=(",", ":")) + "\n"
                      for t in tasks)
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
        row = {k: task[k] for k in ("id", "baseId", "depth", "atoms", "labelMode", "kind", "expectedProvable")}
        row["stratum"] = v2.stratum(task)
        row["strictMemo"] = {
            "outcome": outcome,
            "correct": outcome == ("found" if task["expectedProvable"] else "refuted"),
            "elapsedMs": result["elapsedNs"] / 1e6,
            **{k: v for k, v in result.items() if k not in ("found", "refuted", "timeout", "elapsedNs")},
        }
        rows.append(row)
    return rows


# Measures

def queries(entry: dict[str, Any]) -> int:
    return entry["proveCalls"] + entry["focusCalls"] + entry["cacheHits"]


def class_count(entry: dict[str, Any], cls: str, table: str | None = None) -> int:
    tables = (table,) if table else ("prove", "focus")
    return sum(entry[f"{t}{cls.capitalize()}"] for t in tables)


def pooled(rows: list[dict[str, Any]], cls: str, table: str | None = None) -> float | None:
    hits = sum(r["strictMemo"][f"{table}Hits"] if table else r["strictMemo"]["cacheHits"] for r in rows)
    return sum(class_count(r["strictMemo"], cls, table) for r in rows) / hits if hits else None


def bootstrap(rows: list[dict[str, Any]], cls: str) -> list[float] | None:
    if not rows:
        return None
    generator = random.Random(BOOTSTRAP_SEED)
    pairs = [(class_count(r["strictMemo"], cls), r["strictMemo"]["cacheHits"]) for r in rows]
    shares = []
    for _ in range(BOOTSTRAP_RESAMPLES):
        sample = [generator.choice(pairs) for _ in pairs]
        total = sum(h for _, h in sample)
        shares.append(sum(c for c, _ in sample) / total if total else 0.0)
    shares.sort()
    return [shares[int(0.025 * BOOTSTRAP_RESAMPLES)], shares[int(0.975 * BOOTSTRAP_RESAMPLES) - 1]]


def group_entry(rows: list[dict[str, Any]]) -> dict[str, Any]:
    memo = [r["strictMemo"] for r in rows]
    total_queries = sum(queries(m) for m in memo)
    entry: dict[str, Any] = {
        "tasks": len(rows),
        "decided": sum(m["outcome"] in ("found", "refuted") for m in memo),
        "timeouts": sum(m["outcome"] == "timeout" for m in memo),
        "queries": total_queries,
        "revisits": sum(m["cacheHits"] for m in memo),
        "classes": {cls: sum(class_count(m, cls) for m in memo) for cls in CLASSES},
        "classShares": {cls: pooled(rows, cls) for cls in CLASSES},
        "byTable": {table: {"revisits": sum(m[f"{table}Hits"] for m in memo),
                            "classShares": {cls: pooled(rows, cls, table) for cls in CLASSES}}
                    for table in ("prove", "focus")},
        "permutationShareOfQueries": (sum(class_count(m, "permutation") for m in memo) / total_queries
                                      if total_queries else None),
        "medianElapsedMs": statistics.median(m["elapsedMs"] for m in memo) if memo else None,
    }
    return entry


def summarize(rows: list[dict[str, Any]], v01_rows: list[dict[str, Any]]) -> dict[str, Any]:
    by_kind = {kind: [r for r in rows if r["kind"] == kind] for kind in ("positive", "negative-flip", "negative-count")}
    negatives = by_kind["negative-count"]
    out: dict[str, Any] = {"experiment": "revisit-provenance-v0.1", "tasks": len(rows),
                           "wrongAnswers": sum(not r["strictMemo"]["correct"]
                                               and r["strictMemo"]["outcome"] != "timeout" for r in rows),
                           "kinds": {kind: group_entry(members) for kind, members in by_kind.items()},
                           "strata": {}, "bySize": {}}
    for name in sorted({r["stratum"] for r in rows}):
        out["strata"][name] = group_entry([r for r in rows if r["stratum"] == name])
    for atoms in sorted({r["atoms"] for r in rows}):
        out["bySize"][f"atoms-{atoms}"] = {kind: group_entry([r for r in members if r["atoms"] == atoms])
                                           for kind, members in by_kind.items()}
    share94 = pooled(negatives, "permutation")
    unique32 = [r for r in negatives if r["atoms"] == 32 and r["labelMode"] == "unique"]
    one32 = [r for r in negatives if r["atoms"] == 32 and r["labelMode"] == "one-label"]
    share95 = pooled(unique32, "permutation")
    share96 = pooled(one32, "permutation")
    out["hypotheses"] = {
        "H94": {"permutationShare": share94, "interval": bootstrap(negatives, "permutation"), "tasks": len(negatives),
                "holds": share94 is not None and share94 >= 0.5},
        "H95": {"permutationShare": share95, "tasks": len(unique32),
                "holds": share95 is not None and share95 >= 0.5},
        "H96": {"oneLabel": share96, "uniqueLabels": share95, "tasks": {"one-label": len(one32), "unique": len(unique32)},
                "holds": share95 is not None and share96 is not None and share96 < share95},
    }
    v01 = {r["id"]: r["strictMemo"] for r in v01_rows}
    mismatches = [r["id"] for r in rows if r["strictMemo"]["outcome"] != v01[r["id"]]["outcome"]
                  or any(r["strictMemo"][k] != v01[r["id"]][k] for k in COUNTERS)]
    unbalanced = [r["id"] for r in rows
                  if any(class_count(r["strictMemo"], "permutation", t) + class_count(r["strictMemo"], "splits", t)
                         + class_count(r["strictMemo"], "tensors", t) != r["strictMemo"][f"{t}Hits"]
                         for t in ("prove", "focus"))]
    out["checks"] = {
        "C35": {"compared": len(rows), "mismatches": mismatches[:20], "mismatchCount": len(mismatches),
                "holds": not mismatches},
        "C36": {"unbalanced": unbalanced[:20], "holds": not unbalanced},
    }
    return out


def write_report(summary: dict[str, Any]) -> None:
    def pct(x: float | None) -> str:
        return "n/a" if x is None else f"{100 * x:.1f}%"

    lines = ["# revisit-provenance-v0.1", "",
             f"Tasks: {summary['tasks']}. Wrong answers: {summary['wrongAnswers']}.", "",
             "| Stratum | tasks | decided | revisits | permutation | splits | tensors | permutation of queries |",
             "|---|---:|---:|---:|---:|---:|---:|---:|"]
    for name, e in summary["strata"].items():
        shares = e["classShares"]
        lines.append(f"| {name} | {e['tasks']} | {e['decided']} | {e['revisits']} | {pct(shares['permutation'])} | "
                     f"{pct(shares['splits'])} | {pct(shares['tensors'])} | {pct(e['permutationShareOfQueries'])} |")
    lines += ["", "## Hypotheses", ""]
    for key, entry in summary["hypotheses"].items():
        lines.append(f"- {key} ({'holds' if entry['holds'] else 'fails'}): {HYPOTHESES[key]}. "
                     f"{json.dumps({k: v for k, v in entry.items() if k != 'holds'})}")
    lines += ["", "## Checks", ""]
    for key, entry in summary["checks"].items():
        lines.append(f"- {key} ({'holds' if entry['holds'] else 'fails'}): {CHECKS[key]}.")
    v1.write_lf(REPORT, "\n".join(lines) + "\n")


# Registration

DEVELOPMENT_CHECKS = [
    "the definitions, hypotheses, measures, and checks above were written into this runner before any development run",
    "ProofNetIRRevisitProvenance.lean is focused-revisits-v0.1's strictMemo with its control flow unchanged, the "
    "branch threaded through prove, focus, and the split search, and the classes counted at each memo hit; it builds "
    "with proofnet-ir's toolchain",
    "matched-search-v0.2's development set (24 generated bases, seeds 900000 onward, eight per depth, in three label "
    "modes, with their connective flips and count-preserving negatives: 213 tasks, none in the corpus) through this "
    "search and through focused-revisits-v0.1's strictMemo: the outcomes and the eight counters agree on every task, "
    "the classes add up on every task, and no answer is wrong; only these checks and the decided counts were printed, "
    "and no class count or share was looked at",
]


def registration_payload(tasks: list[dict[str, Any]]) -> dict[str, Any]:
    return {
        "experiment": "revisit-provenance-v0.1",
        "question": QUESTION,
        "registeredLocalDate": "2026-10-09 America/Los_Angeles",
        "corpus": {"path": "experiments/matched-search-v0.2/corpus.jsonl", "sha256": v1.sha256_file(CORPUS),
                   "tasks": len(tasks), "kinds": {k: sum(t["kind"] == k for t in tasks)
                                                  for k in ("positive", "negative-flip", "negative-count")}},
        "comparedResults": {"path": "experiments/focused-revisits-v0.1/results.jsonl",
                            "sha256": v1.sha256_file(REVISITS)},
        "search": "focused-revisits-v0.1's strictMemo, copied into ProofNetIRRevisitProvenance.lean with its control "
                  "flow unchanged; every query carries its branch, and every memo hit is classed against the branches "
                  "that met the same query before",
        "definitions": DEFINITIONS,
        "input": "the search receives only the sequent",
        "budget": {"wallClockMsPerTask": BUDGET_MS, "process": f"{EXE} runs the tasks sequentially, on one core"},
        "outcomes": "found, refuted (search exhausted without a proof), timeout",
        "measures": MEASURES,
        "hypotheses": HYPOTHESES,
        "checks": CHECKS,
        "tests": ("the hypotheses are decided by the rules as stated; H94's pooled share is reported with a percentile "
                  f"bootstrap interval over tasks (seed {BOOTSTRAP_SEED}, {BOOTSTRAP_RESAMPLES} resamples), which does "
                  "not decide it"),
        "implementationSha256": {name: v1.sha256_file(path) for name, path in IMPLEMENTATIONS.items()},
        "disclosure": ("focused-revisits-v0.1's results, with every task's hits per table, were committed and reported "
                       "before this registration; no branch, class, or share of this registration was computed before "
                       "it"),
        "developmentChecksBeforeRegistration": DEVELOPMENT_CHECKS,
        "resultsAbsentAtRegistration": True,
    }


def verify_frozen() -> dict[str, Any]:
    prereg = json.loads(PREREG.read_text(encoding="utf-8"))
    if prereg["corpus"]["sha256"] != v1.sha256_file(CORPUS):
        raise SystemExit("corpus changed since registration")
    if prereg["comparedResults"]["sha256"] != v1.sha256_file(REVISITS):
        raise SystemExit("focused-revisits-v0.1's results changed since registration")
    if prereg["implementationSha256"]["search"] != v1.sha256_file(IMPLEMENTATIONS["search"]):
        raise SystemExit("the search changed since registration")
    return prereg


def load_rows(path: Path) -> list[dict[str, Any]]:
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]


def dev() -> int:
    tasks = v2.dev_tasks()
    rows = compute_results(tasks, stream(EXE, tasks, None))
    old = stream(V01_EXE, tasks, None)
    v01_rows = [{"id": t["id"], "strictMemo": {"outcome": v1.outcome_of(old[t["id"]]["strictMemo"]),
                                               **{k: old[t["id"]]["strictMemo"][k] for k in COUNTERS}}}
                for t in tasks]
    summary = summarize(rows, v01_rows)
    print(json.dumps({"tasks": summary["tasks"], "wrongAnswers": summary["wrongAnswers"],
                      "checks": {k: {"holds": v["holds"]} for k, v in summary["checks"].items()}}, indent=1))
    for name, e in summary["strata"].items():
        print(name, e["tasks"], "decided", e["decided"], "timeouts", e["timeouts"])
    return 0


def main() -> int:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    for flag in ("--dev", "--register", "--run", "--summarize", "--check-committed"):
        mode.add_argument(flag, action="store_true")
    args = parser.parse_args()
    if args.dev:
        return dev()
    tasks = v2.load_tasks()
    if args.register:
        if RESULTS.exists() or SUMMARY.exists():
            raise SystemExit("results already exist; registration must precede them")
        EXPERIMENT.mkdir(parents=True, exist_ok=True)
        v1.write_lf(PREREG, json.dumps(registration_payload(tasks), indent=1, sort_keys=True) + "\n")
        print(f"registered {len(tasks)} tasks: {PREREG}")
        return 0
    verify_frozen()
    v01_rows = load_rows(REVISITS)
    if args.run:
        rows = compute_results(tasks, stream(EXE, tasks, EXPERIMENT / "search.partial"))
        v1.write_lf(RESULTS, "".join(json.dumps(r, separators=(",", ":")) + "\n" for r in rows))
        (EXPERIMENT / "search.partial").unlink(missing_ok=True)
    if args.run or args.summarize:
        rows = load_rows(RESULTS)
        summary = summarize(rows, v01_rows)
        v1.write_lf(SUMMARY, json.dumps(summary, indent=1) + "\n")
        write_report(summary)
        print(json.dumps({k: {"holds": v["holds"]} for k, v in summary["hypotheses"].items()}),
              json.dumps({k: v["holds"] for k, v in summary["checks"].items()}))
        return 0
    if not RESULTS.exists():
        print("revisit-provenance-v0.1: registered, no results yet")
        return 0
    committed = load_rows(RESULTS)
    if [row["id"] for row in committed] != [task["id"] for task in tasks]:
        raise SystemExit("committed result ids differ from the corpus")
    fast_ids = {row["id"] for row in committed if row["strictMemo"]["elapsedMs"] <= CHECK_MAX_ELAPSED_MS}
    fast = [t for t in tasks if t["id"] in fast_ids]
    by_id = {row["id"]: row for row in committed}
    for row in compute_results(fast, stream(EXE, fast, None)):
        old = by_id[row["id"]]["strictMemo"]
        if row["strictMemo"]["outcome"] != old["outcome"]:
            raise SystemExit(f"recomputed outcome differs for {row['id']}")
        if any(row["strictMemo"][f"{t}{c.capitalize()}"] != old[f"{t}{c.capitalize()}"]
               for t in ("prove", "focus") for c in CLASSES):
            raise SystemExit(f"recomputed classes differ for {row['id']}")
    summary = json.loads(SUMMARY.read_text(encoding="utf-8"))
    if summary != json.loads(json.dumps(summarize(committed, v01_rows))):
        raise SystemExit("the committed summary does not follow from the results")
    if not all(summary["checks"][c]["holds"] for c in CHECKS):
        raise SystemExit("a registered check fails")
    print(f"revisit-provenance-v0.1-check-ok: tasks={len(committed)} rerun={len(fast)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
