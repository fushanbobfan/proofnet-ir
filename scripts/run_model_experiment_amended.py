#!/usr/bin/env python3
"""Execute model-v0.2 under the publicly disclosed hard-timeout amendment.

The original preregistered runner remains byte-for-byte unchanged.  This
runner reuses its frozen corpus, prompts, raw model responses, scoring rules,
and method implementations, but isolates each algorithmic method in a child
process.  The predeclared 60-second wall-clock budget is therefore a real hard
deadline rather than a post-return classification.  Per-task scoring is also
atomically checkpointed so an interrupted audit does not repeat completed
work.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import platform
import subprocess
import sys
import time
from pathlib import Path
from typing import Any

import run_model_experiment as frozen
from focused_search import parse_formula
from run_matched_experiment import compact_json, sha256_text, verify_with_lean


AMENDMENT_PATH = frozen.OUTPUT_DIR / "protocol-amendment-1.json"
RAW_PATH = frozen.RAW_PATH
RESULTS_PATH = frozen.RESULTS_PATH
SUMMARY_PATH = frozen.SUMMARY_PATH
SCORED_PARTIAL_PATH = frozen.ROOT / "tmp" / "model-v0.2-scored-amendment-1.partial.jsonl"
EXPECTED_RAW_SHA256 = "5cff2378c2d6d3454ec7dc51c0ae39db3f8cbaa612a5b6faef00c977b48f0bef"
ORIGINAL_PREREGISTRATION_COMMIT = "3d767aa5aec53060272007209e91b7531b45929e"


def file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def atomic_write(path: Path, payload: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + ".tmp")
    temporary.write_text(payload, encoding="utf-8", newline="\n")
    temporary.replace(path)


def load_raw_rows(tasks: list[dict[str, Any]]) -> list[dict[str, Any]]:
    if not RAW_PATH.is_file():
        raise AssertionError("captured raw model responses are missing")
    if file_sha256(RAW_PATH) != EXPECTED_RAW_SHA256:
        raise AssertionError("captured raw model response hash mismatch")
    rows = [
        json.loads(line)
        for line in RAW_PATH.read_text(encoding="utf-8").splitlines()
        if line
    ]
    if len(rows) != frozen.TASK_COUNT * 2:
        raise AssertionError("captured raw model response count mismatch")
    by_key = {(row["id"], row["mode"]): row for row in rows}
    if len(by_key) != len(rows):
        raise AssertionError("duplicate raw model response key")
    for task in tasks:
        for mode in ("direct", "repair"):
            row = by_key.get((task["id"], mode))
            if row is None:
                raise AssertionError(f"missing raw response: {task['id']} {mode}")
            expected = sha256_text(compact_json(frozen.request_body(task, mode)))
            if row.get("requestSha256") != expected:
                raise AssertionError(f"raw request hash drift: {task['id']} {mode}")
    return [by_key[key] for key in sorted(by_key)]


def check_amendment(require_results: bool = False) -> list[dict[str, Any]]:
    tasks = frozen.check_preregistered(regenerate=False)
    if not AMENDMENT_PATH.is_file():
        raise AssertionError("protocol amendment is missing")
    amendment = json.loads(AMENDMENT_PATH.read_text(encoding="utf-8"))
    if amendment.get("originalPreregistrationCommit") != ORIGINAL_PREREGISTRATION_COMMIT:
        raise AssertionError("original preregistration commit mismatch")
    if amendment.get("rawResponsesSha256") != EXPECTED_RAW_SHA256:
        raise AssertionError("amendment raw response hash mismatch")
    if amendment.get("rawResponseRows") != frozen.TASK_COUNT * 2:
        raise AssertionError("amendment raw response count mismatch")
    if amendment.get("amendedRunnerSha256") != file_sha256(Path(__file__)):
        raise AssertionError("amended runner hash mismatch")
    load_raw_rows(tasks)
    if require_results and not all(
        path.is_file() for path in (RESULTS_PATH, SUMMARY_PATH)
    ):
        raise AssertionError("amended result artifacts are incomplete")
    print(
        "model-amendment-valid: original preregistration preserved, "
        "360 raw responses fixed, amended runner hash current"
    )
    return tasks


def focused_worker(task: dict[str, Any]) -> tuple[dict[str, Any], None]:
    expected = bool(task["expectedProvable"])
    sequent = [parse_formula(value) for value in task["sequent"]]
    focused, _, _ = frozen.run_focused(
        sequent, max_calls=frozen.METHOD_CANDIDATE_BUDGET
    )
    completed = not bool(focused["limitExceeded"])
    success, prediction = frozen.classify_bounded(
        expected, bool(focused["found"]), completed
    )
    result = {
        "success": success,
        "prediction": prediction,
        "found": bool(focused["found"]),
        "searchCompleted": completed,
        "states": int(focused["calls"]),
        "partitions": int(focused["partitions"]),
        "elapsedMs": float(focused["elapsedMs"]),
        "wallClockExceeded": False,
        "derivationVerified": bool(focused["derivationVerified"]),
    }
    return result, None


def net_worker(
    task: dict[str, Any]
) -> tuple[dict[str, Any], dict[str, Any] | None]:
    expected = bool(task["expectedProvable"])
    net = frozen.generate_net(
        frozen.task_skeleton(task), frozen.METHOD_CANDIDATE_BUDGET
    )
    success, prediction = frozen.classify_bounded(
        expected, net.found, net.stats.completed
    )
    result = {
        "success": success,
        "prediction": prediction,
        "found": net.found,
        "enumerationCompleted": net.stats.completed,
        "candidateCount": net.stats.complete_candidates,
        "checkerCalls": net.stats.checker_calls,
        "acceptedNets": net.stats.accepted_nets,
        "elapsedMs": net.enumeration_ms,
        "wallClockExceeded": False,
    }
    return result, net.certificate


def repair_worker(
    task: dict[str, Any]
) -> tuple[dict[str, Any], dict[str, Any] | None]:
    return frozen.distance_ordered_repair(
        task, frozen.METHOD_CANDIDATE_BUDGET
    )


def worker_main(method: str) -> int:
    task = json.loads(sys.stdin.read())
    if method == "focused":
        result, candidate = focused_worker(task)
    elif method == "netGeneration":
        result, candidate = net_worker(task)
    elif method == "algorithmicRepair":
        result, candidate = repair_worker(task)
    else:
        raise AssertionError(f"unknown worker method: {method}")
    print(compact_json({"result": result, "candidate": candidate}))
    return 0


def timeout_result(method: str, elapsed_ms: float) -> dict[str, Any]:
    common = {
        "success": False,
        "prediction": "timeout",
        "found": False,
        "elapsedMs": elapsed_ms,
        "internalElapsedMs": None,
        "workerWallElapsedMs": elapsed_ms,
        "wallClockExceeded": True,
        "hardTimeout": True,
    }
    if method == "focused":
        return common | {
            "searchCompleted": False,
            "states": 0,
            "partitions": 0,
            "derivationVerified": False,
        }
    return common | {
        "enumerationCompleted": False,
        "candidateCount": 0,
        "checkerCalls": 0,
        **({"acceptedNets": 0} if method == "netGeneration" else {}),
        **(
            {"compatibleMatchings": None, "winnerDistanceFromSource": None}
            if method == "algorithmicRepair"
            else {}
        ),
    }


def run_method_hard(
    task: dict[str, Any], method: str
) -> tuple[dict[str, Any], dict[str, Any] | None]:
    started = time.perf_counter_ns()
    try:
        completed = subprocess.run(
            [sys.executable, str(Path(__file__).resolve()), "--worker", method],
            cwd=frozen.ROOT,
            input=compact_json(task),
            capture_output=True,
            text=True,
            encoding="utf-8",
            timeout=frozen.MODEL_TIMEOUT_SECONDS,
            check=False,
        )
    except subprocess.TimeoutExpired:
        elapsed_ms = (time.perf_counter_ns() - started) / 1_000_000
        return timeout_result(method, elapsed_ms), None
    elapsed_ms = (time.perf_counter_ns() - started) / 1_000_000
    if completed.returncode != 0:
        raise AssertionError(
            f"{method} worker failed for {task['id']}: "
            f"{completed.stderr[-2000:]}"
        )
    payload = json.loads(completed.stdout)
    result = payload["result"]
    result["internalElapsedMs"] = float(result["elapsedMs"])
    result["workerWallElapsedMs"] = elapsed_ms
    result["elapsedMs"] = elapsed_ms
    result["hardTimeout"] = False
    if elapsed_ms > frozen.WALL_CLOCK_BUDGET_MS:
        result["success"] = False
        result["prediction"] = "timeout"
        result["wallClockExceeded"] = True
    return result, payload.get("candidate")


def baseline_row_hard(
    task: dict[str, Any]
) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    values: dict[str, Any] = {}
    accepted: list[dict[str, Any]] = []
    for method in ("focused", "netGeneration", "algorithmicRepair"):
        result, candidate = run_method_hard(task, method)
        values[method] = result
        if candidate is not None and frozen.independent_certificate_check(candidate):
            accepted.append(candidate)
    return values, accepted


def load_scored_partial() -> dict[str, dict[str, Any]]:
    if not SCORED_PARTIAL_PATH.is_file():
        return {}
    rows = [
        json.loads(line)
        for line in SCORED_PARTIAL_PATH.read_text(encoding="utf-8").splitlines()
        if line
    ]
    result = {entry["row"]["id"]: entry for entry in rows}
    if len(result) != len(rows):
        raise AssertionError("duplicate amended scored checkpoint id")
    return result


def write_scored_partial(rows: dict[str, dict[str, Any]]) -> None:
    payload = frozen.jsonl_payload(rows[key] for key in sorted(rows))
    atomic_write(SCORED_PARTIAL_PATH, payload)


def score_task(
    task: dict[str, Any], raw_by_key: dict[tuple[str, str], dict[str, Any]]
) -> dict[str, Any]:
    expected = bool(task["expectedProvable"])
    invalid_outputs: list[dict[str, Any]] = []
    accepted_outputs: list[dict[str, Any]] = []
    reference = task.get("referenceCertificate")
    if expected:
        if reference is None or not frozen.independent_certificate_check(reference):
            raise AssertionError(f"positive reference rejected: {task['id']}")
        accepted_outputs.append(reference)
    repair_source = frozen.with_axioms(
        task["skeleton"], task["repairSourceAxioms"]
    )
    if frozen.independent_certificate_check(repair_source):
        raise AssertionError(f"repair source accepted: {task['id']}")
    invalid_outputs.append(repair_source)

    baselines, baseline_accepted = baseline_row_hard(task)
    accepted_outputs.extend(baseline_accepted)
    direct, direct_candidate = frozen.score_model(
        task, raw_by_key[(task["id"], "direct")]
    )
    repair, repair_candidate = frozen.score_model(
        task, raw_by_key[(task["id"], "repair")]
    )
    for candidate in (direct_candidate, repair_candidate):
        if candidate is None:
            continue
        if frozen.independent_certificate_check(candidate):
            accepted_outputs.append(candidate)
        else:
            invalid_outputs.append(candidate)

    row = {
        "id": task["id"],
        "seed": task["seed"],
        "depth": task["depth"],
        "labelMode": task["labelMode"],
        "expectedProvable": expected,
        "repairDistance": task["repairDistance"],
        "sequentSha256": sha256_text(compact_json(task["sequent"])),
        **baselines,
        "modelDirect": direct,
        "modelRepair": repair,
    }
    return {
        "row": row,
        "invalidOutputs": invalid_outputs,
        "acceptedOutputs": accepted_outputs,
    }


def formal_run() -> dict[str, Any]:
    if RESULTS_PATH.exists() or SUMMARY_PATH.exists():
        raise AssertionError("formal amended result artifacts already exist")
    tasks = check_amendment()
    raw_rows = load_raw_rows(tasks)
    raw_by_key = {(row["id"], row["mode"]): row for row in raw_rows}
    scored = load_scored_partial()
    started = time.perf_counter_ns()
    for position, task in enumerate(tasks):
        if task["id"] not in scored:
            scored[task["id"]] = score_task(task, raw_by_key)
            write_scored_partial(scored)
        if (position + 1) % 10 == 0:
            print(f"amended scoring {position + 1}/{len(tasks)}", file=sys.stderr)

    ordered = [scored[task["id"]] for task in tasks]
    rows = [entry["row"] for entry in ordered]
    invalid_outputs = [
        certificate
        for entry in ordered
        for certificate in entry["invalidOutputs"]
    ]
    accepted_outputs = [
        certificate
        for entry in ordered
        for certificate in entry["acceptedOutputs"]
    ]
    verification = verify_with_lean(invalid_outputs, accepted_outputs)
    results_payload = frozen.jsonl_payload(rows)
    raw_payload = RAW_PATH.read_text(encoding="utf-8")
    response_models = sorted(
        {
            str(row["response"].get("model"))
            for row in raw_rows
            if isinstance(row.get("response"), dict)
        }
    )
    fingerprints = sorted(
        {
            str(row["response"].get("system_fingerprint"))
            for row in raw_rows
            if isinstance(row.get("response"), dict)
        }
    )
    summary = {
        "version": "model-v0.2-amendment-1",
        "taskCount": len(rows),
        "positiveTasks": sum(int(row["expectedProvable"]) for row in rows),
        "negativeTasks": sum(int(not row["expectedProvable"]) for row in rows),
        "corpusSha256": file_sha256(frozen.CORPUS_PATH),
        "preregistrationSha256": file_sha256(frozen.PREREG_PATH),
        "protocolAmendmentSha256": file_sha256(AMENDMENT_PATH),
        "rawResponsesSha256": sha256_text(raw_payload),
        "resultsSha256": sha256_text(results_payload),
        "model": {
            "requestedId": frozen.MODEL_ID,
            "responseModels": response_models,
            "systemFingerprints": fingerprints,
            "calls": len(raw_rows),
            "errors": sum(int(row.get("error") is not None) for row in raw_rows),
            "promptTokens": sum(
                int((row.get("response") or {}).get("usage", {}).get("prompt_tokens", 0))
                for row in raw_rows
            ),
            "completionTokens": sum(
                int((row.get("response") or {}).get("usage", {}).get("completion_tokens", 0))
                for row in raw_rows
            ),
        },
        "methods": frozen.summarize_rows(rows),
        "leanVerification": verification,
        "execution": {
            "algorithmicIsolation": "one fresh child process per task and method",
            "hardTimeoutSeconds": frozen.MODEL_TIMEOUT_SECONDS,
            "timeoutIncludesWorkerStartup": True,
            "scoringCheckpoint": "atomic per-task local checkpoint",
            "amendedRunElapsedMs": (time.perf_counter_ns() - started) / 1_000_000,
        },
        "hardware": {
            "platform": platform.platform(),
            "machine": platform.machine(),
            "python": platform.python_version(),
        },
        "interpretationBoundary": "held-out unit-free cut-free MLL local-model experiment only; no ordinary Lean/mathlib or general model-advantage claim",
    }
    atomic_write(RESULTS_PATH, results_payload)
    atomic_write(
        SUMMARY_PATH, json.dumps(summary, indent=2, sort_keys=True) + "\n"
    )
    print(f"wrote amended {RESULTS_PATH} and {SUMMARY_PATH}")
    return summary


def check_committed() -> None:
    check_amendment(require_results=True)
    frozen.check_committed()
    summary = json.loads(SUMMARY_PATH.read_text(encoding="utf-8"))
    if summary.get("version") != "model-v0.2-amendment-1":
        raise AssertionError("amended summary version mismatch")
    if summary.get("protocolAmendmentSha256") != file_sha256(AMENDMENT_PATH):
        raise AssertionError("amended summary protocol hash mismatch")
    results = [
        json.loads(line)
        for line in RESULTS_PATH.read_text(encoding="utf-8").splitlines()
        if line
    ]
    for row in results:
        for method in ("focused", "netGeneration", "algorithmicRepair"):
            value = row[method]
            if value.get("workerWallElapsedMs") is None:
                raise AssertionError("amended worker timing is missing")
            if value.get("hardTimeout") and value.get("success"):
                raise AssertionError("hard timeout incorrectly counted as success")
    print(
        "model-amended-results-valid: hashes current, hard-timeout schema "
        "present, every Lean-accepted output sequentialized"
    )


def smoke() -> None:
    tasks = check_amendment()
    task = next(value for value in tasks if value["id"] == "model-0-positive")
    for method in ("focused", "netGeneration", "algorithmicRepair"):
        result, candidate = run_method_hard(task, method)
        if not result["success"] or result["hardTimeout"]:
            raise AssertionError(f"amended {method} smoke failed")
        if method != "focused" and candidate is None:
            raise AssertionError(f"amended {method} smoke lost its certificate")
    original_timeout = frozen.MODEL_TIMEOUT_SECONDS
    frozen.MODEL_TIMEOUT_SECONDS = 0.01
    try:
        timeout, candidate = run_method_hard(task, "netGeneration")
    finally:
        frozen.MODEL_TIMEOUT_SECONDS = original_timeout
    if (
        not timeout["hardTimeout"]
        or timeout["success"]
        or timeout["prediction"] != "timeout"
        or candidate is not None
    ):
        raise AssertionError("amended hard-timeout smoke failed")
    print("model-amendment-smoke-ok: methods execute and hard deadline kills")


def main() -> int:
    parser = argparse.ArgumentParser()
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("--check-amendment", action="store_true")
    modes.add_argument("--write", action="store_true")
    modes.add_argument("--check-committed", action="store_true")
    modes.add_argument("--smoke", action="store_true")
    modes.add_argument(
        "--worker",
        choices=("focused", "netGeneration", "algorithmicRepair"),
    )
    args = parser.parse_args()
    if args.worker is not None:
        return worker_main(args.worker)
    if args.check_amendment:
        check_amendment()
    elif args.write:
        print(json.dumps(formal_run(), indent=2, sort_keys=True))
    elif args.smoke:
        smoke()
    else:
        check_committed()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
