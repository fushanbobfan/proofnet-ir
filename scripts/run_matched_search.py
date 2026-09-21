#!/usr/bin/env python3
"""Equal-information matched search (v0.11 step 2): build, register, run, check.

  python scripts/run_matched_search.py --build-corpus
  python scripts/run_matched_search.py --register
  python scripts/run_matched_search.py --run
  python scripts/run_matched_search.py --check-committed

`--build-corpus` takes the held-out bases from `proofnet_ir_search_corpus`,
collapses their atom labels into the unique, two-label, and one-label modes,
derives one connective-flip negative per positive when exhaustive net-space
search refutes it within a generous budget, and writes `corpus.jsonl`. `--register` freezes the
corpus, the arms, the budget, and the hypotheses. `--run` executes the three
arms of `proofnet_ir_matched_search` on every task and writes the results,
summary, and report. `--check-committed` verifies the artifact hashes and
reruns the tasks that finished quickly.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import statistics
import subprocess
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
EXPERIMENT = ROOT / "experiments" / "matched-search-v0.1"
CORPUS = EXPERIMENT / "corpus.jsonl"
PREREG = EXPERIMENT / "preregistration.json"
RESULTS = EXPERIMENT / "results.jsonl"
SUMMARY = EXPERIMENT / "summary.json"
REPORT = EXPERIMENT / "report.md"
IMPLEMENTATIONS = {
    "searchArms": ROOT / "ProofNetIRMatchedSearch.lean",
    "baseGenerator": ROOT / "ProofNetIRSearchCorpus.lean",
    "runner": ROOT / "scripts" / "run_matched_search.py",
}
BUDGET_MS = 5000
CERTIFY_BUDGET_MS = 20000
ARMS = ("focused", "focusedBalanced", "nets")
MODES = ("unique", "two-label", "one-label")
CHECK_MAX_ELAPSED_MS = 200


def sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes().replace(b"\r\n", b"\n")).hexdigest()


def write_lf(path: Path, text: str) -> None:
    path.write_bytes(text.encode("utf-8"))


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


def lake_exe(name: str, payload: str, *args: str) -> list[dict[str, Any]]:
    completed = subprocess.run(
        [find_lake(), "exe", name, *args], cwd=ROOT, input=payload, capture_output=True,
        text=True, encoding="utf-8", check=True,
    )
    return [json.loads(line) for line in completed.stdout.splitlines() if line.startswith("{")]


def atom_count(formula: dict[str, Any]) -> int:
    if formula["kind"] == "atom":
        return 1
    return atom_count(formula["left"]) + atom_count(formula["right"])


def atom_names(formula: dict[str, Any], acc: list[str]) -> list[str]:
    if formula["kind"] == "atom":
        if formula["name"] not in acc:
            acc.append(formula["name"])
    else:
        atom_names(formula["left"], acc)
        atom_names(formula["right"], acc)
    return acc


def rename(formula: dict[str, Any], names: dict[str, str]) -> dict[str, Any]:
    if formula["kind"] == "atom":
        return {"kind": "atom", "name": names[formula["name"]], "positive": formula["positive"]}
    return {"kind": formula["kind"], "left": rename(formula["left"], names),
            "right": rename(formula["right"], names)}


def name_map(sequent: list[dict[str, Any]], mode: str) -> dict[str, str]:
    original: list[str] = []
    for formula in sequent:
        atom_names(formula, original)
    original = sorted(original)
    if mode == "unique":
        return {name: f"r{index}" for index, name in enumerate(original)}
    if mode == "two-label":
        return {name: f"r{index % 2}" for index, name in enumerate(original)}
    return {name: "r0" for name in original}


def connective_positions(sequent: list[dict[str, Any]]) -> list[list[int]]:
    """Preorder paths of every connective occurrence, as conclusion index then
    left/right steps (0 or 1)."""
    positions: list[list[int]] = []

    def walk(formula: dict[str, Any], path: list[int]) -> None:
        if formula["kind"] == "atom":
            return
        positions.append(path)
        walk(formula["left"], path + [0])
        walk(formula["right"], path + [1])

    for index, formula in enumerate(sequent):
        walk(formula, [index])
    return positions


def flip_at(sequent: list[dict[str, Any]], path: list[int]) -> list[dict[str, Any]]:
    flipped = copy.deepcopy(sequent)
    node = flipped[path[0]]
    for step in path[1:]:
        node = node["left"] if step == 0 else node["right"]
    node["kind"] = "par" if node["kind"] == "tensor" else "tensor"
    return flipped


def build_corpus() -> None:
    bases = lake_exe("proofnet_ir_search_corpus", "")
    positives = []
    for base in bases:
        for mode in MODES:
            sequent = [rename(f, name_map(base["sequent"], mode)) for f in base["sequent"]]
            positives.append({
                "id": f"search-{base['id'].split('-')[-1]}-{mode}-positive",
                "baseId": base["id"], "seed": base["seed"], "depth": base["depth"],
                "atoms": sum(atom_count(f) for f in sequent), "labelMode": mode,
                "expectedProvable": True, "flipPath": None, "sequent": sequent,
            })
    # Candidate negatives: connective flips of each positive in preorder,
    # certified unprovable by exhaustive net-space search (the `nets` arm with a
    # generous budget refuting the flip). The first certified flip is kept; a
    # positive whose first flip already exhausts the budget gets no negative,
    # because flips do not change the linking space.
    negatives = []
    certified_ids: set[str] = set()
    for positive in positives:
        for path in connective_positions(positive["sequent"]):
            flipped = flip_at(positive["sequent"], path)
            payload = json.dumps({"id": positive["id"], "sequent": flipped}, separators=(",", ":")) + "\n"
            outcome = lake_exe("proofnet_ir_matched_search", payload, "--budget-ms",
                               str(CERTIFY_BUDGET_MS), "--nets-only")[0]["nets"]
            if outcome["timeout"]:
                break
            if outcome["found"]:
                continue
            certified_ids.add(positive["id"])
            negatives.append({
                **{k: positive[k] for k in ("baseId", "seed", "depth", "atoms", "labelMode")},
                "id": positive["id"].replace("-positive", "-negative"),
                "expectedProvable": False, "flipPath": path, "sequent": flipped,
            })
            break
    tasks = positives + negatives
    EXPERIMENT.mkdir(parents=True, exist_ok=True)
    write_lf(CORPUS, "".join(json.dumps(t, separators=(",", ":")) + "\n" for t in tasks))
    uncertified = [p["id"] for p in positives if p["id"] not in certified_ids]
    print(f"corpus: {len(positives)} positives, {len(negatives)} certified negatives, "
          f"{len(uncertified)} positives without a certified negative")


def load_tasks() -> list[dict[str, Any]]:
    return [json.loads(line) for line in CORPUS.read_text(encoding="utf-8").splitlines() if line.strip()]


def stratum(task: dict[str, Any]) -> str:
    sign = "positive" if task["expectedProvable"] else "negative"
    return f"atoms-{task['atoms']}:{task['labelMode']}:{sign}"


def registration_payload(tasks: list[dict[str, Any]]) -> dict[str, Any]:
    strata: dict[str, int] = {}
    for task in tasks:
        strata[stratum(task)] = strata.get(stratum(task), 0) + 1
    return {
        "experiment": "matched-search-v0.1",
        "question": "under equal information (the sequent alone) and one wall-clock budget, does "
                    "net-space search find or refute more MLL sequents than focused sequent "
                    "search, and where does label repetition reverse the answer",
        "arms": {
            "focused": "the committed scripts/focused_search.py reproduced in Lean step for step "
                       "(reproduction verified on 86 sequents: identical outcomes and counters)",
            "focusedBalanced": "the same search with per-name atom-balance pruning of states and splits",
            "nets": "axiom-linking enumeration in the committed generator's order, each complete "
                    "linking decided by Certificate.unificationCheck, first acceptance ends the search",
        },
        "input": "every arm receives only the sequent; no skeleton, hint, or reference linking",
        "budget": {"wallClockMsPerArmPerTask": BUDGET_MS, "process": "one Lean process, arms run "
                   "sequentially on the same machine; each arm also reports its own operation counts"},
        "outcomes": "found (a proof), refuted (search exhausted without a proof), timeout",
        "corpus": {"path": "experiments/matched-search-v0.1/corpus.jsonl", "sha256": sha256_file(CORPUS),
                   "bases": "proofnet_ir_search_corpus, seeds 20000-20119, forty per depth at depths "
                            "2, 3, 4; labels collapsed to unique, two-label, and one-label; one "
                            "connective-flip negative per positive when exhaustive net-space search "
                            "refutes it within 20 seconds",
                   "taskCount": len(tasks), "strata": dict(sorted(strata.items()))},
        "implementationSha256": {name: sha256_file(path) for name, path in IMPLEMENTATIONS.items()},
        "hypotheses": {
            "H4": "on unique-label tasks, nets finds or refutes at least as many tasks as "
                  "focusedBalanced in every size stratum, and its median elapsed time on the "
                  "32-atom unique strata is lower",
            "H5": "on one-label 32-atom positives, focusedBalanced finds more tasks within the "
                  "budget than nets",
            "H6": "focusedBalanced finds or refutes at least as many tasks as focused in every "
                  "stratum",
        },
        "report": "per stratum and arm: found, refuted, timeout counts, median and maximum elapsed "
                  "milliseconds, median operation counts; the hypotheses answered as stated; no "
                  "claim beyond MLL sequents and these two search families",
        "developmentChecksBeforeRegistration": "the six hand fixtures and the 80 development "
                                                "sequents of step 1 were run through all arms; "
                                                "no corpus task had been run",
        "resultsAbsentAtRegistration": True,
        "registeredLocalDate": "2026-09-21 America/Los_Angeles",
    }


def run_arms(tasks: list[dict[str, Any]]) -> dict[str, dict[str, Any]]:
    payload = "".join(json.dumps({"id": t["id"], "sequent": t["sequent"]}, separators=(",", ":")) + "\n"
                      for t in tasks)
    rows = lake_exe("proofnet_ir_matched_search", payload, "--budget-ms", str(BUDGET_MS))
    return {row["id"]: row for row in rows}


def outcome_of(arm: dict[str, Any]) -> str:
    if arm["timeout"]:
        return "timeout"
    return "found" if arm["found"] else "refuted"


def compute_results(tasks: list[dict[str, Any]], runs: dict[str, dict[str, Any]]) -> list[dict[str, Any]]:
    rows = []
    for task in tasks:
        run = runs[task["id"]]
        row = {k: task[k] for k in ("id", "baseId", "depth", "atoms", "labelMode", "expectedProvable", "flipPath")}
        row["stratum"] = stratum(task)
        for arm in ARMS:
            result = run[arm]
            row[arm] = {
                "outcome": outcome_of(result),
                "correct": (outcome_of(result) == ("found" if task["expectedProvable"] else "refuted")),
                "elapsedMs": result["elapsedNs"] / 1e6,
                **{k: v for k, v in result.items() if k not in ("found", "refuted", "timeout", "elapsedNs")},
            }
        rows.append(row)
    return rows


def summarize(rows: list[dict[str, Any]]) -> dict[str, Any]:
    strata: dict[str, list[dict[str, Any]]] = {}
    for row in rows:
        strata.setdefault(row["stratum"], []).append(row)
    per_stratum: dict[str, Any] = {}
    for name, members in sorted(strata.items()):
        entry: dict[str, Any] = {"tasks": len(members)}
        for arm in ARMS:
            outcomes = [m[arm]["outcome"] for m in members]
            elapsed = [m[arm]["elapsedMs"] for m in members]
            entry[arm] = {
                "found": outcomes.count("found"), "refuted": outcomes.count("refuted"),
                "timeout": outcomes.count("timeout"),
                "correct": sum(1 for m in members if m[arm]["correct"]),
                "wrong": sum(1 for m in members if m[arm]["outcome"] != "timeout" and not m[arm]["correct"]),
                "medianElapsedMs": statistics.median(elapsed), "maxElapsedMs": max(elapsed),
            }
        per_stratum[name] = entry

    def decided(entry: dict[str, Any], arm: str) -> int:
        return entry[arm]["found"] + entry[arm]["refuted"]

    h4_counts = all(decided(e, "nets") >= decided(e, "focusedBalanced")
                    for n, e in per_stratum.items() if ":unique:" in n)
    unique32 = [e for n, e in per_stratum.items() if n.startswith("atoms-32:unique:")]
    h4_time = all(e["nets"]["medianElapsedMs"] < e["focusedBalanced"]["medianElapsedMs"] for e in unique32) if unique32 else None
    one32 = per_stratum.get("atoms-32:one-label:positive")
    h5 = (one32["focusedBalanced"]["found"] > one32["nets"]["found"]) if one32 else None
    h6 = all(decided(e, "focusedBalanced") >= decided(e, "focused") for e in per_stratum.values())
    return {
        "experiment": "matched-search-v0.1",
        "preregistrationSha256": sha256_file(PREREG),
        "corpusSha256": sha256_file(CORPUS),
        "budgetMs": BUDGET_MS,
        "tasks": len(rows),
        "wrongAnswers": {arm: sum(1 for r in rows if r[arm]["outcome"] != "timeout" and not r[arm]["correct"]) for arm in ARMS},
        "strata": per_stratum,
        "hypotheses": {
            "H4": {"decidedAtLeastOnUnique": h4_counts, "fasterMedianOn32Unique": h4_time,
                   "supported": bool(h4_counts and h4_time)},
            "H5": {"supported": h5},
            "H6": {"supported": h6},
        },
        "resultsSha256": sha256_file(RESULTS),
    }


def write_report(summary: dict[str, Any]) -> None:
    lines = ["# Equal-information matched search (v0.11 step 2)", "",
             "Three arms, one input (the sequent), one wall-clock budget of "
             f"{summary['budgetMs']} ms per arm per task; definitions, corpus, and hypotheses are",
             "frozen in `preregistration.json` (SHA-256 `" + summary["preregistrationSha256"] + "`).", "",
             f"Tasks: {summary['tasks']}. Wrong answers (a decided outcome contradicting the certified "
             f"label): {summary['wrongAnswers']}.", "",
             "| Stratum | Tasks | focused found/refuted/timeout (median ms) | focusedBalanced (median ms) | nets (median ms) |",
             "| --- | ---: | --- | --- | --- |"]
    for name, entry in summary["strata"].items():
        cells = []
        for arm in ARMS:
            a = entry[arm]
            cells.append(f"{a['found']}/{a['refuted']}/{a['timeout']} ({a['medianElapsedMs']:.2f})")
        lines.append(f"| {name} | {entry['tasks']} | " + " | ".join(cells) + " |")
    h = summary["hypotheses"]
    lines += ["", "## Hypotheses", "",
              f"- H4 (nets decides at least as many unique-label tasks as focusedBalanced in every "
              f"size, and is faster at 32 atoms): {h['H4']}.",
              f"- H5 (focusedBalanced finds more one-label 32-atom positives than nets): supported: {h['H5']['supported']}.",
              f"- H6 (balance pruning never loses to the committed baseline): supported: {h['H6']['supported']}.", "",
              "## Interpretation boundary", "",
              "Two search families on unit-free, cut-free MLL sequents under one budget on one",
              "machine. The result says where rule-order redundancy or linking redundancy",
              "dominates for these corpora; it says nothing about proof assistants at the",
              "scale of Lean or Mathlib, and it claims no general advantage for proof nets."]
    write_lf(REPORT, "\n".join(lines) + "\n")


def main() -> int:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--build-corpus", action="store_true")
    mode.add_argument("--register", action="store_true")
    mode.add_argument("--run", action="store_true")
    mode.add_argument("--check-committed", action="store_true")
    args = parser.parse_args()

    if args.build_corpus:
        if PREREG.exists():
            raise SystemExit("the corpus is frozen by the registration")
        build_corpus()
        return 0
    tasks = load_tasks()
    if args.register:
        if RESULTS.exists() or SUMMARY.exists():
            raise SystemExit("results already exist; registration must precede them")
        write_lf(PREREG, json.dumps(registration_payload(tasks), indent=1, sort_keys=True) + "\n")
        print(f"registered {len(tasks)} tasks: {PREREG}")
        return 0

    prereg = json.loads(PREREG.read_text(encoding="utf-8"))
    if prereg["corpus"]["sha256"] != sha256_file(CORPUS):
        raise SystemExit("corpus changed since registration")
    for name in ("searchArms", "baseGenerator"):
        if prereg["implementationSha256"][name] != sha256_file(IMPLEMENTATIONS[name]):
            raise SystemExit(f"implementation {name} changed since registration")

    if args.run:
        rows = compute_results(tasks, run_arms(tasks))
        write_lf(RESULTS, "".join(json.dumps(r, separators=(",", ":")) + "\n" for r in rows))
        summary = summarize(rows)
        write_lf(SUMMARY, json.dumps(summary, indent=1) + "\n")
        write_report(summary)
        print(f"matched-search-run: tasks={summary['tasks']} wrong={summary['wrongAnswers']}")
        return 0

    committed = [json.loads(line) for line in RESULTS.read_text(encoding="utf-8").splitlines() if line.strip()]
    if [row["id"] for row in committed] != [task["id"] for task in tasks]:
        raise SystemExit("committed result ids differ from the corpus")
    fast = {row["id"] for row in committed if all(row[arm]["elapsedMs"] <= CHECK_MAX_ELAPSED_MS for arm in ARMS)}
    reruns = compute_results([t for t in tasks if t["id"] in fast], run_arms([t for t in tasks if t["id"] in fast]))
    by_id = {row["id"]: row for row in committed}
    for row in reruns:
        for arm in ARMS:
            if row[arm]["outcome"] != by_id[row["id"]][arm]["outcome"]:
                raise SystemExit(f"recomputed outcome differs for {row['id']} {arm}")
    summary = json.loads(SUMMARY.read_text(encoding="utf-8"))
    if summary["resultsSha256"] != sha256_file(RESULTS) or summary["preregistrationSha256"] != sha256_file(PREREG):
        raise SystemExit("summary hashes do not match the committed files")
    if any(summary["wrongAnswers"].values()):
        raise SystemExit("committed wrong answers")
    print(f"matched-search-check-ok: tasks={len(committed)} rerun={len(fast)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
