#!/usr/bin/env python3
"""Representation-as-target model study (v0.11 step 3): pilot, register, run, check.

  python scripts/run_representation_study.py --pilot <tasks.jsonl>
  python scripts/run_representation_study.py --register
  python scripts/run_representation_study.py --run
  python scripts/run_representation_study.py --check-committed

The same local model receives the same rendering of a sequent and is asked,
in one arm, for a top-down sequent-calculus proof and, in the other, for a
proof-net linking. Every proposal is verified by `proofnet_ir_representation_verify`,
which converts proofs to `CutFreeDerivation` and checks `infer?`, and completes
nets into certificates and checks `Certificate.check`. `--pilot` runs
development sequents only; `--register` freezes the corpus, prompts, model, and
hypotheses; `--run` collects and verifies the responses on the registered
corpus; `--check-committed` re-verifies the committed proposals with Lean and
checks the artifact hashes.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import statistics
import subprocess
import sys
import time
import urllib.error
import urllib.request
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
EXPERIMENT = ROOT / "experiments" / "representation-v0.1"
CORPUS_SOURCE = ROOT / "experiments" / "model-v0.2" / "corpus.jsonl"
PREREG = EXPERIMENT / "preregistration.json"
RESPONSES = EXPERIMENT / "raw-responses.jsonl"
RESULTS = EXPERIMENT / "results.jsonl"
SUMMARY = EXPERIMENT / "summary.json"
REPORT = EXPERIMENT / "report.md"
IMPLEMENTATIONS = {
    "verifier": ROOT / "ProofNetIRRepresentationVerify.lean",
    "runner": ROOT / "scripts" / "run_representation_study.py",
}
MODEL_ENDPOINT = "http://127.0.0.1:8080/v1/chat/completions"
MODEL_ID = "qwen3.6-35b-a3b-ud-q4_k_xl"
MODEL_SEED = 20260921
MODEL_MAX_TOKENS = 1024
MODEL_TIMEOUT_SECONDS = 300
ARMS = ("proof", "net")

PROOF_SYSTEM = (
    "You prove one-sided sequents of unit-free, cut-free multiplicative linear logic (MLL). "
    "Formulas are atoms with a sign (a+ is the atom, a- its dual), tensors (A ⊗ B), and pars (A ⅋ B). "
    "A proof is a tree of rule applications, written top-down from the goal sequent, whose formulas have 0-based "
    "positions. Rules: axiom closes a sequent that is exactly two dual atoms (same name, opposite sign); "
    "par at position i replaces the formula A ⅋ B by A, B in place (A takes position i, B takes i+1, later formulas "
    "shift by one); tensor at position i, for the formula A ⊗ B, lists the positions of the OTHER formulas that go "
    "with A (the rest go with B); the left premise sequent is A followed by the chosen formulas in their order, the "
    "right premise sequent is B followed by the rest in their order. Every premise is itself a proof object, never a "
    "list of formulas. Reply with one JSON object and no prose, using exactly these shapes: "
    '{"rule":"axiom"} | {"rule":"par","at":i,"premise":PROOF} | '
    '{"rule":"tensor","at":i,"left":[positions],"leftPremise":PROOF,"rightPremise":PROOF} | {"rule":"unprovable"}. '
    "Example. Sequent: 0: ([0]a+ ⊗ [1]b+) 1: ([2]a- ⅋ [3]b-). Proof: "
    '{"rule":"par","at":1,"premise":{"rule":"tensor","at":0,"left":[1],"leftPremise":{"rule":"axiom"},'
    '"rightPremise":{"rule":"axiom"}}} '
    "(after the par the sequent is 0: a+ ⊗ b+, 1: a-, 2: b-; the tensor sends position 1 left and position 2 right; "
    "the premises a+, a- and b+, b- are axioms)."
)
NET_SYSTEM = (
    "You build proof nets for one-sided sequents of unit-free, cut-free multiplicative linear logic (MLL). "
    "Formulas are atoms with a sign (a+ is the atom, a- its dual), tensors (A ⊗ B), and pars (A ⅋ B). "
    "Every atom occurrence carries a number in brackets. A proof net pairs every atom occurrence with exactly one "
    "occurrence of the same name and opposite sign such that the structure is correct: for every way of keeping one "
    "premise of each par, the graph of formula trees and axiom pairs is acyclic and connected. Reply with one JSON "
    'object and no prose, using exactly these shapes: {"pairs":[[a,b],...]} | {"unprovable":true}. '
    "Example. Sequent: 0: ([0]a+ ⊗ [1]b+) 1: ([2]a- ⅋ [3]b-). Net: "
    '{"pairs":[[0,2],[1,3]]} (occurrence 0 pairs with 2 and 1 with 3; keeping either premise of the par leaves a '
    "connected acyclic graph)."
)


def sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes().replace(b"\r\n", b"\n")).hexdigest()


def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


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


def render_formula(formula: dict[str, Any], counter: list[int]) -> str:
    if formula["kind"] == "atom":
        index = counter[0]
        counter[0] += 1
        return f"[{index}]{formula['name']}{'+' if formula['positive'] else '-'}"
    symbol = "⊗" if formula["kind"] == "tensor" else "⅋"
    return f"({render_formula(formula['left'], counter)} {symbol} {render_formula(formula['right'], counter)})"


def render_task(sequent: list[dict[str, Any]]) -> str:
    counter = [0]
    parts = [f"{position}: {render_formula(formula, counter)}" for position, formula in enumerate(sequent)]
    return "Sequent, one formula per position:\n" + "\n".join(parts)


def request_body(sequent: list[dict[str, Any]], arm: str) -> dict[str, Any]:
    return {
        "model": MODEL_ID,
        "messages": [
            {"role": "system", "content": PROOF_SYSTEM if arm == "proof" else NET_SYSTEM},
            {"role": "user", "content": render_task(sequent)},
        ],
        "temperature": 0,
        "seed": MODEL_SEED,
        "max_tokens": MODEL_MAX_TOKENS,
        "chat_template_kwargs": {"enable_thinking": False},
    }


def call_model(task: dict[str, Any], arm: str) -> dict[str, Any]:
    body = request_body(task["sequent"], arm)
    encoded = json.dumps(body, ensure_ascii=False, separators=(",", ":")).encode("utf-8")
    request = urllib.request.Request(MODEL_ENDPOINT, data=encoded,
                                     headers={"Content-Type": "application/json"}, method="POST")
    started = time.perf_counter_ns()
    try:
        with urllib.request.urlopen(request, timeout=MODEL_TIMEOUT_SECONDS) as response:
            result = json.loads(response.read().decode("utf-8"))
        error = None
    except (urllib.error.URLError, TimeoutError, json.JSONDecodeError) as exception:
        result, error = None, f"{type(exception).__name__}: {exception}"
    elapsed_ms = (time.perf_counter_ns() - started) / 1_000_000
    return {"id": task["id"], "arm": arm, "requestSha256": sha256_text(encoded.decode("utf-8")),
            "elapsedMs": elapsed_ms, "error": error, "response": result}


def extract_json(text: str) -> dict[str, Any] | None:
    text = text.strip()
    if text.startswith("```"):
        text = text.strip("`")
        if text.startswith("json"):
            text = text[4:]
    start = text.find("{")
    if start < 0:
        return None
    depth = 0
    for index in range(start, len(text)):
        if text[index] == "{":
            depth += 1
        elif text[index] == "}":
            depth -= 1
            if depth == 0:
                try:
                    value = json.loads(text[start:index + 1])
                except json.JSONDecodeError:
                    return None
                return value if isinstance(value, dict) else None
    return None


def classify(response: dict[str, Any] | None) -> tuple[str, dict[str, Any] | None, int]:
    """Returns (claim, proposal, completion tokens): claim is `provable`,
    `unprovable`, or `unparseable`."""
    if not response:
        return "unparseable", None, 0
    try:
        content = response["choices"][0]["message"]["content"]
        tokens = int(response.get("usage", {}).get("completion_tokens", 0))
    except (KeyError, IndexError, TypeError):
        return "unparseable", None, 0
    proposal = extract_json(content or "")
    if proposal is None:
        return "unparseable", None, tokens
    if proposal.get("rule") == "unprovable" or proposal.get("unprovable") is True:
        return "unprovable", proposal, tokens
    return "provable", proposal, tokens


def verify(rows: list[dict[str, Any]]) -> dict[tuple[str, str], dict[str, Any]]:
    """Runs the Lean verifier on every provable claim; keyed by (id, arm)."""
    payload = "".join(
        json.dumps({"id": f"{row['id']}|{row['arm']}", "sequent": row["sequent"], "kind": row["arm"],
                    "proposal": row["proposal"]}, separators=(",", ":")) + "\n"
        for row in rows if row["claim"] == "provable")
    verdicts: dict[tuple[str, str], dict[str, Any]] = {}
    if not payload:
        return verdicts
    completed = subprocess.run([find_lake(), "exe", "proofnet_ir_representation_verify"], cwd=ROOT,
                               input=payload, capture_output=True, text=True, encoding="utf-8", check=True)
    for line in completed.stdout.splitlines():
        if line.startswith("{"):
            verdict = json.loads(line)
            task_id, arm = verdict["id"].rsplit("|", 1)
            verdicts[(task_id, arm)] = verdict
    return verdicts


def evaluate(tasks: list[dict[str, Any]], responses: dict[tuple[str, str], dict[str, Any]]) -> list[dict[str, Any]]:
    rows = []
    for task in tasks:
        for arm in ARMS:
            response = responses[(task["id"], arm)]
            claim, proposal, tokens = classify(response["response"])
            rows.append({"id": task["id"], "arm": arm, "sequent": task["sequent"],
                         "expectedProvable": task["expectedProvable"], "claim": claim,
                         "proposal": proposal, "completionTokens": tokens,
                         "elapsedMs": response["elapsedMs"], "error": response["error"]})
    verdicts = verify(rows)
    for row in rows:
        verdict = verdicts.get((row["id"], row["arm"]))
        row["valid"] = bool(verdict and verdict["valid"])
        row["reason"] = verdict["reason"] if verdict else ""
        if row["expectedProvable"]:
            row["correct"] = row["valid"]
        else:
            row["correct"] = row["claim"] == "unprovable"
        del row["sequent"]
    return rows


def load_corpus() -> list[dict[str, Any]]:
    tasks = []
    for line in CORPUS_SOURCE.read_text(encoding="utf-8").splitlines():
        if line.strip():
            row = json.loads(line)
            tasks.append({"id": row["id"], "depth": row["depth"], "labelMode": row["labelMode"],
                          "expectedProvable": row["expectedProvable"], "sequent": row["sequent"]})
    return tasks


def stratum(task: dict[str, Any]) -> str:
    return f"depth-{task['depth']}:{task['labelMode']}:{'positive' if task['expectedProvable'] else 'negative'}"


def registration_payload(tasks: list[dict[str, Any]]) -> dict[str, Any]:
    strata: dict[str, int] = {}
    for task in tasks:
        strata[stratum(task)] = strata.get(stratum(task), 0) + 1
    return {
        "experiment": "representation-v0.1",
        "question": "given the same sequent rendering and the same budget, does the same model produce "
                    "valid proof-net linkings more often, and with fewer tokens, than valid sequent-calculus "
                    "proofs",
        "arms": {"proof": "top-down sequent proof in the JSON shapes of the system prompt, verified by "
                          "conversion to CutFreeDerivation and infer? equality",
                 "net": "axiom linking over the numbered atom occurrences, verified by Certificate.check"},
        "corpus": {"path": "experiments/model-v0.2/corpus.jsonl", "sha256": sha256_file(CORPUS_SOURCE),
                   "taskCount": len(tasks), "strata": dict(sorted(strata.items()))},
        "model": {"id": MODEL_ID, "endpoint": MODEL_ENDPOINT, "temperature": 0, "seed": MODEL_SEED,
                  "maxTokens": MODEL_MAX_TOKENS, "thinking": False},
        "promptSha256": {"proofSystem": sha256_text(PROOF_SYSTEM), "netSystem": sha256_text(NET_SYSTEM)},
        "rendering": "identical user message in both arms: the sequent with 0-based formula positions and "
                     "bracketed atom-occurrence numbers in reading order",
        "implementationSha256": {name: sha256_file(path) for name, path in IMPLEMENTATIONS.items()},
        "scoring": "positives: a proposal is correct only when Lean verifies it; negatives: correct only when "
                   "the model answers unprovable; unparseable output is wrong; tokens are completion tokens",
        "hypotheses": {
            "H7": "on positives, the net arm's Lean-verified rate exceeds the proof arm's",
            "H8": "among Lean-verified positives, the net arm's median completion tokens are lower",
            "H9": "on negatives, the two arms' correct rates differ by less than ten points",
        },
        "developmentChecksBeforeRegistration": "six hand fixtures verified both ways; a pilot on development "
                                                "sequents of step 1 (not corpus tasks) checked that both arms "
                                                "return parseable JSON",
        "resultsAbsentAtRegistration": True,
        "registeredLocalDate": "2026-09-21 America/Los_Angeles",
    }


def collect(tasks: list[dict[str, Any]], partial_path: Path | None) -> dict[tuple[str, str], dict[str, Any]]:
    responses: dict[tuple[str, str], dict[str, Any]] = {}
    if partial_path and partial_path.is_file():
        for line in partial_path.read_text(encoding="utf-8").splitlines():
            if line.strip():
                row = json.loads(line)
                responses[(row["id"], row["arm"])] = row
    for task in tasks:
        for arm in ARMS:
            key = (task["id"], arm)
            if key in responses and responses[key]["error"] is None:
                continue
            responses[key] = call_model(task, arm)
            if partial_path:
                write_lf(partial_path, "".join(json.dumps(responses[k], ensure_ascii=False, separators=(",", ":")) + "\n"
                                               for k in sorted(responses)))
    return responses


def summarize(rows: list[dict[str, Any]], tasks: list[dict[str, Any]]) -> dict[str, Any]:
    by_id = {task["id"]: task for task in tasks}
    strata: dict[str, dict[str, list[dict[str, Any]]]] = {}
    for row in rows:
        strata.setdefault(stratum(by_id[row["id"]]), {}).setdefault(row["arm"], []).append(row)
    per_stratum = {}
    for name, arms in sorted(strata.items()):
        per_stratum[name] = {}
        for arm in ARMS:
            members = arms.get(arm, [])
            valid_tokens = [m["completionTokens"] for m in members if m["valid"]]
            per_stratum[name][arm] = {
                "tasks": len(members),
                "correct": sum(1 for m in members if m["correct"]),
                "valid": sum(1 for m in members if m["valid"]),
                "unprovableClaims": sum(1 for m in members if m["claim"] == "unprovable"),
                "unparseable": sum(1 for m in members if m["claim"] == "unparseable"),
                "medianTokens": statistics.median([m["completionTokens"] for m in members]) if members else None,
                "medianTokensValid": statistics.median(valid_tokens) if valid_tokens else None,
            }
    positives = [r for r in rows if r["expectedProvable"]]
    negatives = [r for r in rows if not r["expectedProvable"]]
    rates = {}
    for arm in ARMS:
        pos = [r for r in positives if r["arm"] == arm]
        neg = [r for r in negatives if r["arm"] == arm]
        valid_tokens = [r["completionTokens"] for r in pos if r["valid"]]
        rates[arm] = {"positiveValidRate": sum(1 for r in pos if r["valid"]) / len(pos) if pos else None,
                      "negativeCorrectRate": sum(1 for r in neg if r["correct"]) / len(neg) if neg else None,
                      "medianTokensValidPositives": statistics.median(valid_tokens) if valid_tokens else None}
    h7 = rates["net"]["positiveValidRate"] > rates["proof"]["positiveValidRate"] if positives else None
    h8 = None
    if rates["net"]["medianTokensValidPositives"] is not None and rates["proof"]["medianTokensValidPositives"] is not None:
        h8 = rates["net"]["medianTokensValidPositives"] < rates["proof"]["medianTokensValidPositives"]
    h9 = None
    if negatives:
        h9 = abs(rates["net"]["negativeCorrectRate"] - rates["proof"]["negativeCorrectRate"]) < 0.10
    return {"experiment": "representation-v0.1", "preregistrationSha256": sha256_file(PREREG) if PREREG.exists() else None,
            "tasks": len(tasks), "rates": rates, "strata": per_stratum,
            "hypotheses": {"H7": {"supported": h7}, "H8": {"supported": h8}, "H9": {"supported": h9}},
            "responsesSha256": sha256_file(RESPONSES) if RESPONSES.exists() else None,
            "resultsSha256": sha256_file(RESULTS) if RESULTS.exists() else None}


def write_report(summary: dict[str, Any]) -> None:
    lines = ["# Representation-as-target model study (v0.11 step 3)", "",
             "One local model, one rendering, two output targets; prompts, corpus, model, and",
             "hypotheses are frozen in `preregistration.json` (SHA-256 `" + str(summary["preregistrationSha256"]) + "`).", "",
             f"Tasks: {summary['tasks']} (each run in both arms). Rates: {json.dumps(summary['rates'])}.", "",
             "| Stratum | proof correct/valid/unprovable-claims/unparseable (median tokens) | net correct/valid/unprovable-claims/unparseable (median tokens) |",
             "| --- | --- | --- |"]
    for name, arms in summary["strata"].items():
        cells = []
        for arm in ARMS:
            a = arms[arm]
            cells.append(f"{a['correct']}/{a['valid']}/{a['unprovableClaims']}/{a['unparseable']} ({a['medianTokens']})")
        lines.append(f"| {name} | " + " | ".join(cells) + " |")
    h = summary["hypotheses"]
    lines += ["", "## Hypotheses", "",
              f"- H7 (net arm has the higher Lean-verified rate on positives): supported: {h['H7']['supported']}.",
              f"- H8 (verified net outputs use fewer tokens than verified proofs): supported: {h['H8']['supported']}.",
              f"- H9 (negative-detection rates within ten points): supported: {h['H9']['supported']}.", "",
              "## Interpretation boundary", "",
              "One quantized local model at temperature zero without thinking, on held-out",
              "unit-free, cut-free MLL sequents. The result concerns which representation this",
              "model produces correctly under this budget; it is not a claim about proof",
              "assistants at the scale of Lean or Mathlib, nor about other models."]
    write_lf(REPORT, "\n".join(lines) + "\n")


def main() -> int:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--pilot", type=Path)
    mode.add_argument("--register", action="store_true")
    mode.add_argument("--run", action="store_true")
    mode.add_argument("--check-committed", action="store_true")
    args = parser.parse_args()

    if args.pilot:
        tasks = [json.loads(line) for line in args.pilot.read_text(encoding="utf-8").splitlines() if line.strip()]
        for task in tasks:
            task.setdefault("expectedProvable", True)
        rows = evaluate(tasks, collect(tasks, None))
        for row in rows:
            print(json.dumps({k: row[k] for k in ("id", "arm", "claim", "valid", "reason", "completionTokens", "elapsedMs")}))
        return 0

    tasks = load_corpus()
    if args.register:
        if RESULTS.exists() or RESPONSES.exists():
            raise SystemExit("results already exist; registration must precede them")
        EXPERIMENT.mkdir(parents=True, exist_ok=True)
        write_lf(PREREG, json.dumps(registration_payload(tasks), indent=1, sort_keys=True) + "\n")
        print(f"registered {len(tasks)} tasks: {PREREG}")
        return 0

    prereg = json.loads(PREREG.read_text(encoding="utf-8"))
    if prereg["corpus"]["sha256"] != sha256_file(CORPUS_SOURCE):
        raise SystemExit("corpus changed since registration")
    if prereg["promptSha256"] != {"proofSystem": sha256_text(PROOF_SYSTEM), "netSystem": sha256_text(NET_SYSTEM)}:
        raise SystemExit("prompts changed since registration")
    if prereg["implementationSha256"]["verifier"] != sha256_file(IMPLEMENTATIONS["verifier"]):
        raise SystemExit("verifier changed since registration")

    if args.run:
        responses = collect(tasks, RESPONSES)
        rows = evaluate(tasks, responses)
        write_lf(RESULTS, "".join(json.dumps(r, ensure_ascii=False, separators=(",", ":")) + "\n" for r in rows))
        summary = summarize(rows, tasks)
        write_lf(SUMMARY, json.dumps(summary, indent=1) + "\n")
        write_report(summary)
        print(f"representation-run: tasks={summary['tasks']} rates={json.dumps(summary['rates'])}")
        return 0

    responses = {}
    for line in RESPONSES.read_text(encoding="utf-8").splitlines():
        if line.strip():
            row = json.loads(line)
            responses[(row["id"], row["arm"])] = row
    rows = evaluate(tasks, responses)
    committed = [json.loads(line) for line in RESULTS.read_text(encoding="utf-8").splitlines() if line.strip()]
    if len(committed) != len(rows):
        raise SystemExit("committed result count differs")
    for want, have in zip(committed, rows):
        for field in ("id", "arm", "claim", "valid", "correct", "completionTokens"):
            if want[field] != have[field]:
                raise SystemExit(f"committed {field} differs for {want['id']} {want['arm']}")
    summary = json.loads(SUMMARY.read_text(encoding="utf-8"))
    if summary["resultsSha256"] != sha256_file(RESULTS) or summary["responsesSha256"] != sha256_file(RESPONSES):
        raise SystemExit("summary hashes do not match the committed files")
    print(f"representation-check-ok: tasks={len(committed) // 2} reverified={len(committed)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
