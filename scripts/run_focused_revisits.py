#!/usr/bin/env python3
"""Focused revisits v0.1: how much of the redundancy that strict focusing leaves does a focused search meet.

  python scripts/run_focused_revisits.py --dev
  python scripts/run_focused_revisits.py --register
  python scripts/run_focused_revisits.py --run
  python scripts/run_focused_revisits.py --summarize
  python scripts/run_focused_revisits.py --check-committed

The tasks are matched-search-v0.2's 983 sequents. `proofnet_ir_focused_revisits` runs matched-search-v0.2's
`focusedStrict` twice on each: `strictMemo` with its two memo tables, as registered there, and `strictNoMemo` without
them. A query (a sequent to prove, or a tensor in focus with its context) answered from a memo table is a revisit:
the search met that query before, along a different sequence of foci and splits. Without the tables every revisit is
explored again, and a set of the queries met so far counts them without pruning anything.

`--dev` runs both arms, and matched-search-v0.2's `focusedStrict`, on generated bases with seeds disjoint from the
corpus and writes nothing under `experiments/`. `--check-committed` verifies hashes, ids, and the summary, and reruns
the tasks on which both arms finished within 200 ms.
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
EXPERIMENT = ROOT / "experiments" / "focused-revisits-v0.1"
CORPUS = v2.CORPUS
V2_RESULTS = v2.RESULTS
PREREG = EXPERIMENT / "preregistration.json"
RESULTS = EXPERIMENT / "results.jsonl"
SUMMARY = EXPERIMENT / "summary.json"
REPORT = EXPERIMENT / "report.md"
EXE = "proofnet_ir_focused_revisits"
IMPLEMENTATIONS = {
    "arms": ROOT / "ProofNetIRFocusedRevisits.lean",
    "runner": ROOT / "scripts" / "run_focused_revisits.py",
}
ARMS = ("strictMemo", "strictNoMemo")
BUDGET_MS = 5000
CHECK_MAX_ELAPSED_MS = 200
COUNTERS = ("proveCalls", "focusCalls", "cacheHits", "decides", "splits", "infeasible")
BOOTSTRAP_SEED = 20261003
BOOTSTRAP_RESAMPLES = 10_000

QUESTION = ("how much of the rule-order redundancy that strict focusing leaves does matched-search-v0.2's strictly "
            "focused search meet, as queries it has already met along another sequence of foci and splits, and what "
            "does merging them in its memo tables buy within the same budget")
HYPOTHESES = {
    "H83": "over the count-preserving negatives, at least half of strictMemo's queries are revisits (pooled share of "
           "memo hits among all queries >= 0.5)",
    "H84": "at 16 and at 32 atoms, the pooled revisit share of strictMemo is higher on the count-preserving negatives "
           "than on the positives",
    "H85": "strictNoMemo decides fewer of the 32-atom count-preserving negatives than strictMemo",
    "H86": "on the count-preserving negatives that both arms decide, the median ratio of strictNoMemo's explored "
           "queries to strictMemo's exceeds 2",
}
CHECKS = {
    "C26": "strictMemo reproduces matched-search-v0.2's focusedStrict on every task: the same outcome and the same six "
           "counters (proveCalls, focusCalls, cacheHits, decides, splits, infeasible)",
    "C27": "no arm gives a wrong answer",
}
MEASURES = {
    "queries": "strictMemo: proveCalls + focusCalls + cacheHits (every call of prove, and of focus on a tensor goal); "
               "strictNoMemo: proveCalls + focusCalls",
    "revisitShare": "strictMemo: cacheHits / queries, per task and pooled over a group of tasks (sums of hits over sums "
                    "of queries); strictNoMemo: (proveRevisits + focusRevisits) / queries",
    "explored": "proveCalls + focusCalls, the queries a search did not answer from a table",
    "workRatio": "strictNoMemo's explored queries over strictMemo's, on a task both arms decide",
    "decided": "found or refuted within the budget",
}


# Running

def stream(tasks: list[dict[str, Any]], partial: Path | None) -> dict[str, dict[str, Any]]:
    payload = "".join(json.dumps({"id": t["id"], "sequent": t["sequent"]}, separators=(",", ":")) + "\n"
                      for t in tasks)
    process = subprocess.Popen([v1.find_lake(), "exe", EXE, "--budget-ms", str(BUDGET_MS)], cwd=ROOT,
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
                print(f"{EXE}: {len(rows)}/{len(tasks)}", flush=True)
    if sink:
        sink.close()
    if process.wait() != 0:
        raise SystemExit(f"{EXE} failed")
    return rows


def compute_results(tasks: list[dict[str, Any]], runs: dict[str, dict[str, Any]]) -> list[dict[str, Any]]:
    rows = []
    for task in tasks:
        run = runs[task["id"]]
        row = {k: task[k] for k in ("id", "baseId", "depth", "atoms", "labelMode", "kind", "expectedProvable")}
        row["stratum"] = v2.stratum(task)
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


# Measures

def queries(entry: dict[str, Any], arm: str) -> int:
    return entry["proveCalls"] + entry["focusCalls"] + (entry["cacheHits"] if arm == "strictMemo" else 0)


def revisits(entry: dict[str, Any], arm: str) -> int:
    return entry["cacheHits"] if arm == "strictMemo" else entry["proveRevisits"] + entry["focusRevisits"]


def explored(entry: dict[str, Any]) -> int:
    return entry["proveCalls"] + entry["focusCalls"]


def decided(entry: dict[str, Any]) -> bool:
    return entry["outcome"] in ("found", "refuted")


def pooled_share(rows: list[dict[str, Any]], arm: str) -> float | None:
    total = sum(queries(r[arm], arm) for r in rows)
    return sum(revisits(r[arm], arm) for r in rows) / total if total else None


def bootstrap_share(rows: list[dict[str, Any]], arm: str) -> list[float] | None:
    if not rows:
        return None
    generator = random.Random(BOOTSTRAP_SEED)
    pairs = [(revisits(r[arm], arm), queries(r[arm], arm)) for r in rows]
    shares = []
    for _ in range(BOOTSTRAP_RESAMPLES):
        sample = [generator.choice(pairs) for _ in pairs]
        total = sum(q for _, q in sample)
        shares.append(sum(h for h, _ in sample) / total if total else 0.0)
    shares.sort()
    return [shares[int(0.025 * BOOTSTRAP_RESAMPLES)], shares[int(0.975 * BOOTSTRAP_RESAMPLES) - 1]]


def group_entry(rows: list[dict[str, Any]]) -> dict[str, Any]:
    entry: dict[str, Any] = {"tasks": len(rows)}
    for arm in ARMS:
        entry[arm] = {
            "decided": sum(decided(r[arm]) for r in rows),
            "timeouts": sum(r[arm]["outcome"] == "timeout" for r in rows),
            "queries": sum(queries(r[arm], arm) for r in rows),
            "revisits": sum(revisits(r[arm], arm) for r in rows),
            "pooledRevisitShare": pooled_share(rows, arm),
            "medianElapsedMs": statistics.median(r[arm]["elapsedMs"] for r in rows) if rows else None,
        }
    both = [r for r in rows if decided(r["strictMemo"]) and decided(r["strictNoMemo"])]
    ratios = [explored(r["strictNoMemo"]) / explored(r["strictMemo"]) for r in both if explored(r["strictMemo"])]
    entry["bothDecided"] = len(both)
    entry["medianWorkRatio"] = statistics.median(ratios) if ratios else None
    return entry


def summarize(rows: list[dict[str, Any]], v2_rows: list[dict[str, Any]]) -> dict[str, Any]:
    by_kind = {kind: [r for r in rows if r["kind"] == kind] for kind in ("positive", "negative-flip", "negative-count")}
    count_negatives = by_kind["negative-count"]
    out: dict[str, Any] = {"experiment": "focused-revisits-v0.1", "tasks": len(rows),
                           "wrongAnswers": {arm: sum(not r[arm]["correct"] and decided(r[arm]) for r in rows)
                                            for arm in ARMS},
                           "kinds": {kind: group_entry(members) for kind, members in by_kind.items()},
                           "strata": {}, "bySize": {}}
    for name in sorted({r["stratum"] for r in rows}):
        out["strata"][name] = group_entry([r for r in rows if r["stratum"] == name])
    for atoms in sorted({r["atoms"] for r in rows}):
        out["bySize"][f"atoms-{atoms}"] = {kind: group_entry([r for r in members if r["atoms"] == atoms])
                                           for kind, members in by_kind.items()}

    share83 = pooled_share(count_negatives, "strictMemo")
    h84 = {}
    for atoms in (16, 32):
        negative = pooled_share([r for r in count_negatives if r["atoms"] == atoms], "strictMemo")
        positive = pooled_share([r for r in by_kind["positive"] if r["atoms"] == atoms], "strictMemo")
        h84[f"atoms-{atoms}"] = {"countNegatives": negative, "positives": positive}
    thirty_two = [r for r in count_negatives if r["atoms"] == 32]
    decided85 = {arm: sum(decided(r[arm]) for r in thirty_two) for arm in ARMS}
    both86 = [r for r in count_negatives if decided(r["strictMemo"]) and decided(r["strictNoMemo"])]
    ratios86 = [explored(r["strictNoMemo"]) / explored(r["strictMemo"]) for r in both86 if explored(r["strictMemo"])]
    median86 = statistics.median(ratios86) if ratios86 else None
    out["hypotheses"] = {
        "H83": {"pooledRevisitShare": share83, "interval": bootstrap_share(count_negatives, "strictMemo"),
                "tasks": len(count_negatives), "holds": share83 is not None and share83 >= 0.5},
        "H84": {**h84, "holds": all(e["countNegatives"] is not None and e["positives"] is not None
                                    and e["countNegatives"] > e["positives"] for e in h84.values())},
        "H85": {"tasks": len(thirty_two), "decided": decided85,
                "holds": decided85["strictNoMemo"] < decided85["strictMemo"]},
        "H86": {"bothDecided": len(both86), "medianWorkRatio": median86,
                "holds": median86 is not None and median86 > 2},
    }
    v2_by_id = {r["id"]: r["focusedStrict"] for r in v2_rows}
    mismatches = [r["id"] for r in rows
                  if r["strictMemo"]["outcome"] != v2_by_id[r["id"]]["outcome"]
                  or any(r["strictMemo"][k] != v2_by_id[r["id"]][k] for k in COUNTERS)]
    out["checks"] = {
        "C26": {"compared": len(rows), "mismatches": mismatches[:20], "mismatchCount": len(mismatches),
                "holds": not mismatches},
        "C27": {"wrongAnswers": out["wrongAnswers"], "holds": not any(out["wrongAnswers"].values())},
    }
    return out


def write_report(summary: dict[str, Any]) -> None:
    def pct(x: float | None) -> str:
        return "n/a" if x is None else f"{100 * x:.1f}%"

    lines = ["# focused-revisits-v0.1", "",
             f"Tasks: {summary['tasks']}. Wrong answers: {summary['wrongAnswers']}.", "",
             "| Stratum | tasks | memo decided | memo revisit share | no-memo decided | no-memo revisit share | "
             "median work ratio |",
             "|---|---:|---:|---:|---:|---:|---:|"]
    for name, e in summary["strata"].items():
        ratio = e["medianWorkRatio"]
        lines.append(f"| {name} | {e['tasks']} | {e['strictMemo']['decided']} | "
                     f"{pct(e['strictMemo']['pooledRevisitShare'])} | {e['strictNoMemo']['decided']} | "
                     f"{pct(e['strictNoMemo']['pooledRevisitShare'])} | "
                     f"{'n/a' if ratio is None else f'{ratio:.2f}'} |")
    lines += ["", "## Hypotheses", ""]
    for key, entry in summary["hypotheses"].items():
        lines.append(f"- {key} ({'holds' if entry['holds'] else 'fails'}): {HYPOTHESES[key]}. "
                     f"{json.dumps({k: v for k, v in entry.items() if k != 'holds'})}")
    lines += ["", "## Checks", ""]
    for key, entry in summary["checks"].items():
        lines.append(f"- {key} ({'holds' if entry['holds'] else 'fails'}): {CHECKS[key]}.")
    v1.write_lf(REPORT, "\n".join(lines) + "\n")


# Registration

def registration_payload(tasks: list[dict[str, Any]]) -> dict[str, Any]:
    return {
        "experiment": "focused-revisits-v0.1",
        "question": QUESTION,
        "registeredLocalDate": "2026-10-03 America/Los_Angeles",
        "corpus": {"path": "experiments/matched-search-v0.2/corpus.jsonl", "sha256": v1.sha256_file(CORPUS),
                   "tasks": len(tasks), "kinds": {k: sum(t["kind"] == k for t in tasks)
                                                  for k in ("positive", "negative-flip", "negative-count")}},
        "comparedResults": {"path": "experiments/matched-search-v0.2/results.jsonl",
                            "sha256": v1.sha256_file(V2_RESULTS)},
        "arms": {
            "strictMemo": "matched-search-v0.2's focusedStrict, copied unchanged into ProofNetIRFocusedRevisits.lean, "
                          "with its memo tables for sequents and for a tensor in focus with its context; hits are "
                          "counted for each table",
            "strictNoMemo": "the same search with both tables neither consulted nor filled; a set of the queries met so "
                            "far counts revisits and prunes nothing",
        },
        "input": "every arm receives only the sequent",
        "budget": {"wallClockMsPerArmPerTask": BUDGET_MS,
                   "process": f"{EXE} runs strictMemo then strictNoMemo on each task, sequentially, on one core"},
        "outcomes": "found, refuted (search exhausted without a proof), timeout",
        "measures": MEASURES,
        "hypotheses": HYPOTHESES,
        "checks": CHECKS,
        "tests": ("the hypotheses are decided by the rules as stated; H83's pooled share is reported with a "
                  f"percentile bootstrap interval over tasks (seed {BOOTSTRAP_SEED}, {BOOTSTRAP_RESAMPLES} resamples), "
                  "which does not decide it"),
        "implementationSha256": {name: v1.sha256_file(path) for name, path in IMPLEMENTATIONS.items()},
        "disclosure": ("matched-search-v0.2 recorded focusedStrict's cacheHits, proveCalls, and focusCalls for every "
                       "task; no revisit share or other quantity of this registration was computed from them before "
                       "it, and the hypotheses were written before the development run below"),
        "developmentChecksBeforeRegistration": DEVELOPMENT_CHECKS,
        "resultsAbsentAtRegistration": True,
    }


DEVELOPMENT_CHECKS = [
    "the hypotheses, measures, and checks above were written into this runner before any development run",
    "ProofNetIRFocusedRevisits.lean is matched-search-v0.2's focusedStrict copied unchanged, with the memo switch and "
    "the hit and revisit counters added; it builds with proofnet-ir's toolchain",
    "matched-search-v0.2's development set (24 generated bases, seeds 900000 onward, eight per depth, in three label "
    "modes, with their connective flips and count-preserving negatives: 213 tasks, none in the corpus) through both "
    "arms and through matched-search-v0.2's focusedStrict: strictMemo reproduced its outcome and its six counters on "
    "every task, no arm gave a wrong answer, and strictNoMemo timed out on 2 of the 15 32-atom repeated-label "
    "count-preserving negatives and on no other task; only decided, timeout, and median-time counts were printed, and "
    "no revisit share or other hypothesis quantity was looked at",
]


def verify_frozen() -> dict[str, Any]:
    prereg = json.loads(PREREG.read_text(encoding="utf-8"))
    if prereg["corpus"]["sha256"] != v1.sha256_file(CORPUS):
        raise SystemExit("corpus changed since registration")
    if prereg["comparedResults"]["sha256"] != v1.sha256_file(V2_RESULTS):
        raise SystemExit("matched-search-v0.2's results changed since registration")
    if prereg["implementationSha256"]["arms"] != v1.sha256_file(IMPLEMENTATIONS["arms"]):
        raise SystemExit("the arms changed since registration")
    return prereg


def load_rows(path: Path) -> list[dict[str, Any]]:
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]


def dev() -> int:
    tasks = v2.dev_tasks()
    rows = compute_results(tasks, stream(tasks, None))
    payload = "".join(json.dumps({"id": t["id"], "sequent": t["sequent"]}, separators=(",", ":")) + "\n"
                      for t in tasks)
    old = {r["id"]: r["focusedStrict"] for r in
           v1.lake_exe("proofnet_ir_pruned_search", payload, "--budget-ms", str(BUDGET_MS), "--strict-only")}
    v2_rows = [{"id": t["id"], "focusedStrict": {"outcome": v1.outcome_of(old[t["id"]]),
                                                 **{k: old[t["id"]][k] for k in COUNTERS}}} for t in tasks]
    summary = summarize(rows, v2_rows)
    print(json.dumps({k: summary[k] for k in ("tasks", "wrongAnswers", "checks")}, indent=1))
    for name, e in summary["strata"].items():
        print(name, e["tasks"], {arm: (e[arm]["decided"], e[arm]["timeouts"], round(e[arm]["medianElapsedMs"], 2))
                                 for arm in ARMS})
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
    v2_rows = load_rows(V2_RESULTS)
    if args.run:
        rows = compute_results(tasks, stream(tasks, EXPERIMENT / "arms.partial"))
        v1.write_lf(RESULTS, "".join(json.dumps(r, separators=(",", ":")) + "\n" for r in rows))
        (EXPERIMENT / "arms.partial").unlink(missing_ok=True)
    if args.run or args.summarize:
        rows = load_rows(RESULTS)
        summary = summarize(rows, v2_rows)
        v1.write_lf(SUMMARY, json.dumps(summary, indent=1) + "\n")
        write_report(summary)
        print(json.dumps({k: {"holds": v["holds"]} for k, v in summary["hypotheses"].items()}),
              json.dumps({k: v["holds"] for k, v in summary["checks"].items()}))
        return 0
    if not RESULTS.exists():
        print("focused-revisits-v0.1: registered, no results yet")
        return 0
    committed = load_rows(RESULTS)
    if [row["id"] for row in committed] != [task["id"] for task in tasks]:
        raise SystemExit("committed result ids differ from the corpus")
    fast_ids = {row["id"] for row in committed if all(row[arm]["elapsedMs"] <= CHECK_MAX_ELAPSED_MS for arm in ARMS)}
    fast = [t for t in tasks if t["id"] in fast_ids]
    by_id = {row["id"]: row for row in committed}
    for row in compute_results(fast, stream(fast, None)):
        for arm in ARMS:
            if row[arm]["outcome"] != by_id[row["id"]][arm]["outcome"]:
                raise SystemExit(f"recomputed outcome differs for {row['id']} {arm}")
            if row[arm]["proveCalls"] != by_id[row["id"]][arm]["proveCalls"]:
                raise SystemExit(f"recomputed counters differ for {row['id']} {arm}")
    summary = json.loads(SUMMARY.read_text(encoding="utf-8"))
    if summary != json.loads(json.dumps(summarize(committed, v2_rows))):
        raise SystemExit("the committed summary does not follow from the results")
    if not all(summary["checks"][c]["holds"] for c in CHECKS):
        raise SystemExit("a registered check fails")
    print(f"focused-revisits-v0.1-check-ok: tasks={len(committed)} rerun={len(fast)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
