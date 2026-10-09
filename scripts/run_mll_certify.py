#!/usr/bin/env python3
"""MLL certify v0.1: the matched-search corpus decided by a prover independent of the searches it compares.

  python scripts/run_mll_certify.py --dev
  python scripts/run_mll_certify.py --register
  python scripts/run_mll_certify.py --run [--workers 4]
  python scripts/run_mll_certify.py --check-committed

matched-search-v0.2's corpus has 343 count-preserving negatives. Their unprovability was certified by a countermodel
in a finite Lukasiewicz chain for 90 of them and, for the other 253, by the focused search that the experiment then
evaluated, so that search's refutations of those 253 are not an independent measurement. This experiment decides
every task of the corpus with `mll_independent_prover`, an exhaustive prover for the plain sequent calculus written
apart from the library's searches (no focusing, its own formulas, splits enumerated by a dynamic program over the
counting vectors), and compares its answers with the corpus's expected status.

`--dev` runs the prover on matched-search-v0.2's development tasks, none of them in the corpus, and prints only
correctness and time.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import json
import statistics
import sys
import time
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parent))
import mll_independent_prover as prover  # noqa: E402
import run_matched_search as v1  # noqa: E402
import run_pruned_search as v2  # noqa: E402

ROOT = v1.ROOT
EXPERIMENT = ROOT / "experiments" / "mll-certify-v0.1"
CORPUS = v2.CORPUS
PREREG = EXPERIMENT / "preregistration.json"
RESULTS = EXPERIMENT / "results.jsonl"
SUMMARY = EXPERIMENT / "summary.json"
REPORT = EXPERIMENT / "report.md"
IMPLEMENTATIONS = {"prover": ROOT / "scripts" / "mll_independent_prover.py",
                   "runner": ROOT / "scripts" / "run_mll_certify.py"}
SECONDS = 600
NODE_LIMIT = 50_000_000

QUESTION = ("does a prover written independently of the searches matched-search-v0.2 compares confirm the status of "
            "every task of its corpus, in particular the unprovability of the 253 count-preserving negatives that the "
            "focused search itself had certified")
HYPOTHESES = {
    "H107": "the independent prover refutes all 253 count-preserving negatives that the focused search certified",
    "H108": "the independent prover's answer agrees with the expected status on all 983 tasks",
}
CHECKS = {"C42": f"the independent prover decides every task within {SECONDS} s"}


def decide(task: dict[str, Any]) -> dict[str, Any]:
    started = time.monotonic()
    out = prover.decide(task["sequent"], NODE_LIMIT, SECONDS)
    return {"id": task["id"], "provable": out["provable"], "calls": out["calls"],
            "seconds": round(time.monotonic() - started, 3)}


def run(tasks: list[dict[str, Any]], workers: int) -> list[dict[str, Any]]:
    with concurrent.futures.ProcessPoolExecutor(max_workers=workers) as pool:
        decided = list(pool.map(decide, tasks, chunksize=4))
    rows = []
    for task, out in zip(tasks, decided):
        certificate = task.get("certificate") or {}
        rows.append({k: task[k] for k in ("id", "atoms", "labelMode", "kind", "expectedProvable")}
                    | {"certifiedBy": sorted(certificate)} | {k: out[k] for k in ("provable", "calls", "seconds")})
    return rows


def summarize(rows: list[dict[str, Any]]) -> dict[str, Any]:
    def entry(members: list[dict[str, Any]]) -> dict[str, Any]:
        seconds = [r["seconds"] for r in members]
        return {"tasks": len(members), "agree": sum(r["provable"] == r["expectedProvable"] for r in members),
                "disagree": sum(r["provable"] is not None and r["provable"] != r["expectedProvable"] for r in members),
                "undecided": sum(r["provable"] is None for r in members),
                "medianSeconds": statistics.median(seconds) if seconds else None,
                "maxSeconds": max(seconds) if seconds else None}

    search_certified = [r for r in rows if r["kind"] == "negative-count" and "search" in r["certifiedBy"]]
    model_certified = [r for r in rows if r["kind"] == "negative-count" and "countermodel" in r["certifiedBy"]]
    kinds = {k: entry([r for r in rows if r["kind"] == k]) for k in ("positive", "negative-flip", "negative-count")}
    strata = {f"atoms-{a}:{m}:{k}": entry([r for r in rows if (r["atoms"], r["labelMode"], r["kind"]) == (a, m, k)])
              for a, m, k in sorted({(r["atoms"], r["labelMode"], r["kind"]) for r in rows})}
    total = entry(rows)
    return {"experiment": "mll-certify-v0.1", "preregistrationSha256": v1.sha256_file(PREREG), "tasks": len(rows),
            "all": total, "kinds": kinds, "strata": strata,
            "searchCertified": entry(search_certified), "countermodelCertified": entry(model_certified),
            "hypotheses": {
                "H107": {"tasks": len(search_certified),
                         "refuted": sum(r["provable"] is False for r in search_certified),
                         "holds": bool(search_certified) and all(r["provable"] is False for r in search_certified)},
                "H108": {"agree": total["agree"], "tasks": len(rows), "holds": total["agree"] == len(rows)}},
            "checks": {"C42": {"undecided": total["undecided"], "holds": total["undecided"] == 0}},
            "resultsSha256": v1.sha256_file(RESULTS)}


def write_report(s: dict[str, Any]) -> None:
    lines = ["# mll-certify-v0.1", "", f"Tasks: {s['tasks']}; agree {s['all']['agree']}, disagree "
             f"{s['all']['disagree']}, undecided {s['all']['undecided']}.", "",
             "| Stratum | tasks | agree | undecided | median s | max s |", "|---|---:|---:|---:|---:|---:|"]
    for name, e in s["strata"].items():
        lines.append(f"| {name} | {e['tasks']} | {e['agree']} | {e['undecided']} | {e['medianSeconds']:.3f} | "
                     f"{e['maxSeconds']:.2f} |")
    lines += ["", "## Hypotheses", ""]
    for key, e in s["hypotheses"].items():
        lines.append(f"- {key} ({'holds' if e['holds'] else 'fails'}): {HYPOTHESES[key]}.")
    lines += ["", "## Checks", ""]
    for key, e in s["checks"].items():
        lines.append(f"- {key} ({'holds' if e['holds'] else 'fails'}): {CHECKS[key]}.")
    v1.write_lf(REPORT, "\n".join(lines) + "\n")


DEVELOPMENT_CHECKS = [
    "the hypotheses and the check were written into this runner before the development run",
    "matched-search-v0.2's development set (24 generated bases, seeds 900000 onward, with their flips and "
    "count-preserving negatives: 213 tasks, none in the corpus): the prover agreed with the expected status on all, "
    "decided each, the slowest in 3.9 s (32-atom count-preserving negatives, median 0.44 s); only correctness and time "
    "were printed",
]


def registration_payload(tasks: list[dict[str, Any]]) -> dict[str, Any]:
    return {
        "experiment": "mll-certify-v0.1",
        "question": QUESTION,
        "registeredLocalDate": "2026-10-09 America/Los_Angeles",
        "corpus": {"path": "experiments/matched-search-v0.2/corpus.jsonl", "sha256": v1.sha256_file(CORPUS),
                   "tasks": len(tasks),
                   "countPreservingNegatives": {"countermodel": sum(1 for t in tasks if t["kind"] == "negative-count"
                                                                    and "countermodel" in (t.get("certificate") or {})),
                                                "search": sum(1 for t in tasks if t["kind"] == "negative-count"
                                                              and "search" in (t.get("certificate") or {}))}},
        "prover": "mll_independent_prover.py: the plain one-sided sequent calculus of unit-free MLL; pars decomposed "
                  "first (par is invertible); every distinct tensor tried as the last rule with every multiset split "
                  "of the rest whose premises keep per-name atom balance and 2t + 2 = a; sequents memoized as sorted "
                  "multisets; no code shared with focusedStrict or the net searches",
        "budget": {"secondsPerTask": SECONDS, "distinctSequentsPerTask": NODE_LIMIT,
                   "process": "four worker processes on the CPU"},
        "hypotheses": HYPOTHESES, "checks": CHECKS,
        "implementationSha256": {name: v1.sha256_file(path) for name, path in IMPLEMENTATIONS.items()},
        "developmentChecksBeforeRegistration": DEVELOPMENT_CHECKS,
        "resultsAbsentAtRegistration": True,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    for flag in ("--dev", "--register", "--run", "--check-committed"):
        mode.add_argument(flag, action="store_true")
    parser.add_argument("--workers", type=int, default=4)
    args = parser.parse_args()
    if args.dev:
        rows = run(v2.dev_tasks(), args.workers)
        print(json.dumps({"tasks": len(rows), "wrong": sum(r["provable"] is not None and
                                                           r["provable"] != r["expectedProvable"] for r in rows),
                          "undecided": sum(r["provable"] is None for r in rows),
                          "maxSeconds": max(r["seconds"] for r in rows)}))
        return 0
    tasks = v2.load_tasks()
    if args.register:
        if RESULTS.exists():
            raise SystemExit("results already exist; registration must precede them")
        EXPERIMENT.mkdir(parents=True, exist_ok=True)
        v1.write_lf(PREREG, json.dumps(registration_payload(tasks), indent=1, sort_keys=True) + "\n")
        print(f"registered {len(tasks)} tasks: {PREREG}")
        return 0
    prereg = json.loads(PREREG.read_text(encoding="utf-8"))
    if prereg["corpus"]["sha256"] != v1.sha256_file(CORPUS) or \
            prereg["implementationSha256"]["prover"] != v1.sha256_file(IMPLEMENTATIONS["prover"]):
        raise SystemExit("the corpus or the prover changed since registration")
    if args.run:
        rows = run(tasks, args.workers)
        v1.write_lf(RESULTS, "".join(json.dumps(r, separators=(",", ":")) + "\n" for r in rows))
        summary = summarize(rows)
        v1.write_lf(SUMMARY, json.dumps(summary, indent=1) + "\n")
        write_report(summary)
        print(json.dumps({k: v["holds"] for k, v in summary["hypotheses"].items()}),
              json.dumps({k: v["holds"] for k, v in summary["checks"].items()}))
        return 0
    if not RESULTS.exists():
        print("mll-certify-v0.1: registered, no results yet")
        return 0
    rows = [json.loads(l) for l in RESULTS.read_text(encoding="utf-8").splitlines() if l.strip()]
    if [r["id"] for r in rows] != [t["id"] for t in tasks]:
        raise SystemExit("committed ids differ from the corpus")
    fast = [t for t, r in zip(tasks, rows) if r["seconds"] <= 1.0]
    for t, r in zip(fast, run(fast, 2)):
        old = next(x for x in rows if x["id"] == t["id"])
        if r["provable"] != old["provable"]:
            raise SystemExit(f"recomputed answer differs for {t['id']}")
    if json.loads(SUMMARY.read_text(encoding="utf-8")) != json.loads(json.dumps(summarize(rows))):
        raise SystemExit("the committed summary does not follow from the results")
    print(f"mll-certify-v0.1-check-ok: tasks={len(rows)} rerun={len(fast)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
