#!/usr/bin/env python3
"""Search-redundancy experiment (v0.11 step 1): register, run, or check.

  python scripts/run_redundancy_experiment.py --register
  python scripts/run_redundancy_experiment.py --run
  python scripts/run_redundancy_experiment.py --check-committed

`--register` freezes the corpora, the counting implementations, the budgets,
the strata, and the hypotheses into `experiments/redundancy-v0.1/preregistration.json`
before any count exists. `--run` computes the exact counts with the Lean
executable, cross-checks every task with at most 16 atom occurrences and at most
1,000 candidate linkings against the independent brute-force enumerator, and writes `results.jsonl`,
`summary.json`, and `report.md`. `--check-committed` recomputes the counts of every task whose
committed recursion stayed within the fast budget and compares them with the
committed results; the slow budget-bound tasks and the brute-force cross-check
are verified by hash.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import statistics
import subprocess
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
EXPERIMENT = ROOT / "experiments" / "redundancy-v0.1"
PREREG = EXPERIMENT / "preregistration.json"
RESULTS = EXPERIMENT / "results.jsonl"
SUMMARY = EXPERIMENT / "summary.json"
REPORT = EXPERIMENT / "report.md"
CORPORA = {
    "matched": ROOT / "experiments" / "matched-v0.1" / "corpus.jsonl",
    "model": ROOT / "experiments" / "model-v0.2" / "corpus.jsonl",
}
IMPLEMENTATIONS = {
    "leanCounter": ROOT / "ProofNetIRRedundancyCount.lean",
    "bruteForce": ROOT / "scripts" / "redundancy_bruteforce.py",
    "runner": ROOT / "scripts" / "run_redundancy_experiment.py",
}
CROSS_CHECK_MAX_ATOMS = 16
CROSS_CHECK_MAX_LINKINGS = 1000
CHECK_MAX_STATES = 100_000
COUNT_FIELDS = ("dAll", "dWeak", "dFoc", "nets", "linkings")


def sha256_file(path: Path) -> str:
    """Hash with line endings normalized, so a Windows checkout matches CI."""
    return hashlib.sha256(path.read_bytes().replace(b"\r\n", b"\n")).hexdigest()


def write_lf(path: Path, text: str) -> None:
    path.write_bytes(text.encode("utf-8"))


def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def find_lake() -> str:
    import shutil

    on_path = shutil.which("lake")
    if on_path:
        return on_path
    for name in ("lake", "lake.exe"):
        candidate = Path.home() / ".elan" / "bin" / name
        if candidate.is_file():
            return str(candidate)
    raise FileNotFoundError("lake not found")


def atom_count(formula: dict[str, Any]) -> int:
    if formula["kind"] == "atom":
        return 1
    return atom_count(formula["left"]) + atom_count(formula["right"])


def atom_names(formula: dict[str, Any], acc: set[str]) -> set[str]:
    if formula["kind"] == "atom":
        acc.add(formula["name"])
    else:
        atom_names(formula["left"], acc)
        atom_names(formula["right"], acc)
    return acc


def load_tasks() -> list[dict[str, Any]]:
    tasks = []
    for corpus, path in CORPORA.items():
        for line in path.read_text(encoding="utf-8").splitlines():
            if not line.strip():
                continue
            row = json.loads(line)
            sequent = row["sequent"]
            atoms = sum(atom_count(f) for f in sequent)
            names: set[str] = set()
            for f in sequent:
                atom_names(f, names)
            tasks.append({
                "id": row["id"],
                "corpus": corpus,
                "depth": row.get("depth"),
                "labelMode": row.get("labelMode", "unique" if 2 * len(names) == atoms else "repeated"),
                "expectedProvable": row.get("expectedProvable", True),
                "atoms": atoms,
                "names": len(names),
                "conclusions": len(sequent),
                "sequent": sequent,
            })
    return tasks


def stratum(task: dict[str, Any]) -> str:
    if task["corpus"] == "matched":
        return f"matched:atoms-{task['atoms']}"
    sign = "positive" if task["expectedProvable"] else "negative"
    return f"model:depth-{task['depth']}:{task['labelMode']}:{sign}"


def registration_payload(tasks: list[dict[str, Any]]) -> dict[str, Any]:
    strata: dict[str, int] = {}
    for task in tasks:
        strata[stratum(task)] = strata.get(stratum(task), 0) + 1
    return {
        "experiment": "redundancy-v0.1",
        "question": "how many cut-free sequent derivations denote one proof net, for the "
                    "plain calculus, the committed focused baseline, and the "
                    "tensor-persistent focused calculus, on the committed MLL corpora",
        "quantities": {
            "dAll": "derivations in the plain calculus over the frozen occurrence forest, "
                    "exchange absorbed, every occurrence distinct",
            "dWeak": "derivations of scripts/focused_search.py: one deterministic par phase, "
                     "then a tensor choice and every balanced context split",
            "dFoc": "derivations with the focus persisting through the positive subformulas "
                    "of the chosen tensor and released at an atom or a par",
            "nets": "axiom linkings of the forest accepted by Certificate.unificationCheck, "
                    "which equals Certificate.check by theorem",
            "ratios": ["dAll/nets", "dWeak/nets", "dFoc/nets", "dFoc/dWeak"],
        },
        "corpora": {name: {"path": str(path.relative_to(ROOT)).replace("\\", "/"),
                           "sha256": sha256_file(path)} for name, path in CORPORA.items()},
        "taskCount": len(tasks),
        "strata": dict(sorted(strata.items())),
        "implementationSha256": {name: sha256_file(path) for name, path in IMPLEMENTATIONS.items()},
        "budgets": {
            "memoizedStatesPerCountPerTask": 3_000_000,
            "candidateLinkingsPerTask": 1_000_000,
            "crossCheckMaxAtoms": CROSS_CHECK_MAX_ATOMS,
            "crossCheckMaxLinkings": CROSS_CHECK_MAX_LINKINGS,
        },
        "exclusionPolicy": "a count over its state budget is reported as excluded with the "
                           "partial value; a task over the linking budget has no nets count "
                           "and no ratio; negatives must count zero everywhere and enter no "
                           "ratio; nothing is dropped silently",
        "hypotheses": {
            "H1": "on more than half of the ratio-bearing tasks, dFoc/nets > 1",
            "H2": "over the matched strata, median(dAll/nets) more than doubles from 8 to "
                  "16 atoms and again from 16 to 32 atoms",
            "H3": "on more than half of the ratio-bearing tasks, dFoc < dWeak",
        },
        "report": "per stratum: task count, exclusions, median and quartiles of each ratio, "
                  "fraction of tasks with each ratio equal to one; the hypotheses answered "
                  "as stated; no advantage claim of any method",
        "developmentChecksBeforeRegistration": "six hand-checked fixtures and 120 generated "
                                                "development sequents (seeds 5000-5039, depths "
                                                "2-4, not corpus tasks) were counted; the Lean "
                                                "counter and the brute-force enumerator agree on "
                                                "the fixtures and on the development sequents "
                                                "with at most 16 atoms; no corpus count existed",
        "resultsAbsentAtRegistration": True,
        "registeredLocalDate": "2026-09-21 America/Los_Angeles",
    }


def run_lean(tasks: list[dict[str, Any]]) -> dict[str, dict[str, Any]]:
    payload = "".join(json.dumps({"id": t["id"], "sequent": t["sequent"]}, separators=(",", ":")) + "\n"
                      for t in tasks)
    completed = subprocess.run(
        [find_lake(), "exe", "proofnet_ir_redundancy_count"], cwd=ROOT, input=payload,
        capture_output=True, text=True, encoding="utf-8", check=True,
    )
    results = {}
    for line in completed.stdout.splitlines():
        if line.startswith("{"):
            row = json.loads(line)
            results[row["id"]] = row
    return results


def run_brute_force(tasks: list[dict[str, Any]]) -> dict[str, dict[str, Any]]:
    payload = "".join(json.dumps({"id": t["id"], "sequent": t["sequent"]}, separators=(",", ":")) + "\n"
                      for t in tasks)
    completed = subprocess.run(
        [sys.executable, str(IMPLEMENTATIONS["bruteForce"])], cwd=ROOT, input=payload,
        capture_output=True, text=True, encoding="utf-8", check=True,
    )
    return {json.loads(line)["id"]: json.loads(line) for line in completed.stdout.splitlines() if line.strip()}


def ratio(numerator: str, denominator: str) -> float | None:
    d = int(denominator)
    return None if d == 0 else int(numerator) / d


def compute_results(tasks: list[dict[str, Any]], lean: dict[str, dict[str, Any]],
                    brute: dict[str, dict[str, Any]]) -> list[dict[str, Any]]:
    rows = []
    for task in tasks:
        count = lean[task["id"]]
        row = {k: task[k] for k in ("id", "corpus", "depth", "labelMode", "expectedProvable",
                                    "atoms", "names", "conclusions")}
        row["stratum"] = stratum(task)
        for field in ("occurrences", "dAll", "dAllExcluded", "dAllStates", "dWeak", "dWeakExcluded",
                      "dWeakStates", "dFoc", "dFocExcluded", "dFocStates", "linkings", "nets",
                      "netsExcluded"):
            row[field] = count[field]
        complete = not (count["dAllExcluded"] or count["dWeakExcluded"] or count["dFocExcluded"]
                        or count["netsExcluded"])
        row["complete"] = complete
        row["ratioAll"] = ratio(count["dAll"], count["nets"]) if complete else None
        row["ratioWeak"] = ratio(count["dWeak"], count["nets"]) if complete else None
        row["ratioFoc"] = ratio(count["dFoc"], count["nets"]) if complete else None
        row["ratioFocWeak"] = ratio(count["dFoc"], count["dWeak"]) if complete else None
        if task["id"] in brute:
            row["crossChecked"] = all(brute[task["id"]][f] == count[f] for f in COUNT_FIELDS)
        else:
            row["crossChecked"] = None
        rows.append(row)
    return rows


def quantiles(values: list[float]) -> dict[str, float] | None:
    if not values:
        return None
    ordered = sorted(values)
    q = statistics.quantiles(ordered, n=4) if len(ordered) >= 2 else [ordered[0]] * 3
    return {"min": ordered[0], "q1": q[0], "median": statistics.median(ordered), "q3": q[2],
            "max": ordered[-1], "count": len(ordered)}


def summarize(rows: list[dict[str, Any]]) -> dict[str, Any]:
    strata: dict[str, list[dict[str, Any]]] = {}
    for row in rows:
        strata.setdefault(row["stratum"], []).append(row)
    per_stratum = {}
    for name, members in sorted(strata.items()):
        bearing = [m for m in members if m["ratioAll"] is not None]
        per_stratum[name] = {
            "tasks": len(members),
            "complete": sum(1 for m in members if m["complete"]),
            "ratioBearing": len(bearing),
            "crossChecked": sum(1 for m in members if m["crossChecked"] is True),
            "crossCheckFailures": sum(1 for m in members if m["crossChecked"] is False),
            "ratioAll": quantiles([m["ratioAll"] for m in bearing]),
            "ratioWeak": quantiles([m["ratioWeak"] for m in bearing]),
            "ratioFoc": quantiles([m["ratioFoc"] for m in bearing]),
            "ratioFocWeak": quantiles([m["ratioFocWeak"] for m in bearing]),
            "fractionAllEqualsOne": (sum(1 for m in bearing if m["ratioAll"] == 1) / len(bearing)) if bearing else None,
            "fractionFocEqualsOne": (sum(1 for m in bearing if m["ratioFoc"] == 1) / len(bearing)) if bearing else None,
            "negativesAllZero": all(m["dAll"] == "0" and m["nets"] == "0" for m in members
                                    if not m["expectedProvable"]),
        }
    bearing = [r for r in rows if r["ratioAll"] is not None and r["expectedProvable"]]
    h1_fraction = sum(1 for r in bearing if r["ratioFoc"] > 1) / len(bearing) if bearing else None
    h3_fraction = sum(1 for r in bearing if int(r["dFoc"]) < int(r["dWeak"])) / len(bearing) if bearing else None
    medians = {}
    for atoms in (8, 16, 32):
        entry = per_stratum.get(f"matched:atoms-{atoms}")
        medians[str(atoms)] = entry["ratioAll"]["median"] if entry and entry["ratioAll"] else None
    h2 = None
    if all(medians[k] is not None for k in ("8", "16", "32")):
        h2 = medians["16"] > 2 * medians["8"] and medians["32"] > 2 * medians["16"]
    return {
        "experiment": "redundancy-v0.1",
        "preregistrationSha256": sha256_file(PREREG),
        "tasks": len(rows),
        "complete": sum(1 for r in rows if r["complete"]),
        "excluded": sum(1 for r in rows if not r["complete"]),
        "crossChecked": sum(1 for r in rows if r["crossChecked"] is True),
        "crossCheckFailures": sum(1 for r in rows if r["crossChecked"] is False),
        "strata": per_stratum,
        "hypotheses": {
            "H1": {"fractionFocAboveOne": h1_fraction, "supported": (h1_fraction > 0.5) if h1_fraction is not None else None},
            "H2": {"matchedMediansAllOverNets": medians, "supported": h2},
            "H3": {"fractionFocBelowWeak": h3_fraction, "supported": (h3_fraction > 0.5) if h3_fraction is not None else None},
        },
        "resultsSha256": sha256_file(RESULTS),
    }


def write_report(summary: dict[str, Any]) -> None:
    lines = ["# Search-redundancy experiment (v0.11 step 1)", "",
             "Exact counts of cut-free derivations per proof net on the committed MLL",
             "corpora; definitions, budgets, and hypotheses are frozen in",
             "`preregistration.json` (SHA-256 `" + summary["preregistrationSha256"] + "`).", "",
             f"Tasks: {summary['tasks']}; complete: {summary['complete']}; excluded: "
             f"{summary['excluded']}; cross-checked against the brute-force enumerator: "
             f"{summary['crossChecked']} with {summary['crossCheckFailures']} disagreements.", "",
             "| Stratum | Tasks | Ratio-bearing | dAll/nets median (q1, q3, max) | dWeak/nets median | dFoc/nets median | dFoc/dWeak median | dFoc/nets = 1 |",
             "| --- | ---: | ---: | --- | ---: | ---: | ---: | ---: |"]
    for name, entry in summary["strata"].items():
        def fmt(q: dict[str, float] | None, full: bool = False) -> str:
            if q is None:
                return "n/a"
            if full:
                return f"{q['median']:.6g} ({q['q1']:.6g}, {q['q3']:.6g}, {q['max']:.6g})"
            return f"{q['median']:.6g}"
        frac = entry["fractionFocEqualsOne"]
        lines.append(f"| {name} | {entry['tasks']} | {entry['ratioBearing']} | {fmt(entry['ratioAll'], True)} | "
                     f"{fmt(entry['ratioWeak'])} | {fmt(entry['ratioFoc'])} | {fmt(entry['ratioFocWeak'])} | "
                     f"{'n/a' if frac is None else f'{frac:.1%}'} |")
    h = summary["hypotheses"]
    lines += ["", "## Hypotheses", "",
              f"- H1 (dFoc/nets > 1 on more than half of the ratio-bearing tasks): fraction "
              f"{h['H1']['fractionFocAboveOne']:.3f}; supported: {h['H1']['supported']}.",
              f"- H2 (median dAll/nets more than doubles from 8 to 16 and from 16 to 32 atoms): "
              f"medians {h['H2']['matchedMediansAllOverNets']}; supported: {h['H2']['supported']}.",
              f"- H3 (dFoc < dWeak on more than half of the ratio-bearing tasks): fraction "
              f"{h['H3']['fractionFocBelowWeak']:.3f}; supported: {h['H3']['supported']}.", "",
              "## Interpretation boundary", "",
              "The ratios measure how many derivations of each calculus denote one proof net",
              "on these corpora. They are properties of the search spaces, not of any search",
              "procedure's running time, and they claim no advantage for any method; the",
              "matched corpus is derivation-generated with mostly unique labels, and the",
              "model corpus adds repeated labels and negatives."]
    write_lf(REPORT, "\n".join(lines) + "\n")


def main() -> int:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--register", action="store_true")
    mode.add_argument("--run", action="store_true")
    mode.add_argument("--check-committed", action="store_true")
    args = parser.parse_args()
    tasks = load_tasks()

    if args.register:
        if RESULTS.exists() or SUMMARY.exists():
            raise SystemExit("results already exist; registration must precede them")
        EXPERIMENT.mkdir(parents=True, exist_ok=True)
        write_lf(PREREG, json.dumps(registration_payload(tasks), indent=1, sort_keys=True) + "\n")
        print(f"registered {len(tasks)} tasks: {PREREG}")
        return 0

    prereg = json.loads(PREREG.read_text(encoding="utf-8"))
    for name, path in CORPORA.items():
        if prereg["corpora"][name]["sha256"] != sha256_file(path):
            raise SystemExit(f"corpus {name} changed since registration")
    for name in ("leanCounter", "bruteForce"):
        if prereg["implementationSha256"][name] != sha256_file(IMPLEMENTATIONS[name]):
            raise SystemExit(f"implementation {name} changed since registration")
    if args.run:
        lean = run_lean(tasks)
        small = [t for t in tasks if t["atoms"] <= CROSS_CHECK_MAX_ATOMS
                 and int(lean[t["id"]]["linkings"]) <= CROSS_CHECK_MAX_LINKINGS]
        brute = run_brute_force(small)
        rows = compute_results(tasks, lean, brute)
        write_lf(RESULTS, "".join(json.dumps(r, separators=(",", ":")) + "\n" for r in rows))
        summary = summarize(rows)
        write_lf(SUMMARY, json.dumps(summary, indent=1) + "\n")
        write_report(summary)
        failures = summary["crossCheckFailures"]
        print(f"redundancy-run: tasks={summary['tasks']} complete={summary['complete']} "
              f"excluded={summary['excluded']} crossChecked={summary['crossChecked']} "
              f"crossCheckFailures={failures}")
        return 1 if failures else 0

    # Check mode: the committed counts are recomputed for every task whose
    # committed recursion stayed within the fast budget; the brute-force
    # cross-check and the budget-bound tasks are not rerun, and their committed
    # outcome is verified by hash instead.
    committed = [json.loads(line) for line in RESULTS.read_text(encoding="utf-8").splitlines() if line.strip()]
    if [row["id"] for row in committed] != [task["id"] for task in tasks]:
        raise SystemExit("committed result ids differ from the corpora")
    fast_ids = {row["id"] for row in committed
                if max(int(row["dAllStates"]), int(row["dWeakStates"]), int(row["dFocStates"])) <= CHECK_MAX_STATES}
    lean = run_lean([task for task in tasks if task["id"] in fast_ids])
    for row in committed:
        if row["id"] not in fast_ids:
            continue
        count = lean[row["id"]]
        for field in COUNT_FIELDS + ("dAllExcluded", "dWeakExcluded", "dFocExcluded", "netsExcluded"):
            if row[field] != count[field]:
                raise SystemExit(f"recomputed {field} differs for {row['id']}: {row[field]} vs {count[field]}")
    summary = json.loads(SUMMARY.read_text(encoding="utf-8"))
    if summary["resultsSha256"] != sha256_file(RESULTS) or summary["preregistrationSha256"] != sha256_file(PREREG):
        raise SystemExit("summary hashes do not match the committed files")
    if summary["crossCheckFailures"] or sum(1 for row in committed if row["crossChecked"] is False):
        raise SystemExit("committed cross-check failures")
    print(f"redundancy-check-ok: tasks={len(committed)} recomputed={len(fast_ids)} "
          f"crossChecked={summary['crossChecked']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
