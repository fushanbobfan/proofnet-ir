#!/usr/bin/env python3
"""Representation-as-target model study v0.3: does a model that thinks before it answers write valid derivations?

  python scripts/run_representation_v3.py --pilot 4
  python scripts/run_representation_v3.py --register
  python scripts/run_representation_v3.py --run
  python scripts/run_representation_v3.py --check-committed

representation-v0.2 found that one model without thinking verifies no derivation, with positions or with stable
labels, and six nets. This study asks the same question of a stronger model that reasons before it answers. It
keeps v0.2's corpus positives, prompts, renderings, label conversion, and Lean verification, and runs every arm
under two conditions of one model: `direct` (thinking off) and `thinking` (thinking on at the template's highest
effort, with a thinking budget). Both conditions use the same sampling settings, so they differ only in thinking.
No grammar constrains the answers: with thinking on, the server applies a grammar to the whole output, thinking
included, which leaves no room to think (checked on development sequents before registration).

Amendment 1 (`amendment-1.json`), made before any answer was verified: a response that ends at the token limit in a
run of one repeated non-whitespace character at least 1,000 long is a server failure. It is set aside in
`server-failures.jsonl` and its request sent again, at most three times in all. The summary gives the analysis with
the reruns and, as registered, with each request's first failure in place.

The model server is started with
  start-llama-server.ps1 -Profile qwen38dense -Reasoning on -ReasoningBudget 6144 -Parallel 6 -Ctx 122880
"""

from __future__ import annotations

import argparse
import concurrent.futures
import json
import statistics
import sys
import threading
import time
import urllib.error
import urllib.request
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parent))
import run_representation_study as v1  # noqa: E402
import run_representation_v2 as v2  # noqa: E402

ROOT = v2.ROOT
EXPERIMENT = ROOT / "experiments" / "representation-v0.3"
PREREG = EXPERIMENT / "preregistration.json"
RESPONSES = EXPERIMENT / "raw-responses.jsonl"
RESULTS = EXPERIMENT / "results.jsonl"
SUMMARY = EXPERIMENT / "summary.json"
REPORT = EXPERIMENT / "report.md"
AMENDMENT = EXPERIMENT / "amendment-1.json"
FAILURES = EXPERIMENT / "server-failures.jsonl"
IMPLEMENTATIONS = {
    "verifier": ROOT / "ProofNetIRRepresentationVerify.lean",
    "v01Runner": ROOT / "scripts" / "run_representation_study.py",
    "v02Runner": ROOT / "scripts" / "run_representation_v2.py",
    "runner": Path(__file__).resolve(),
}
MODEL_ID = "qwen3.8-27b-ud-q4_k_xl"
MODEL_FILE = "Qwen3.8-27B-UD-Q4_K_XL.gguf"
MODEL_SHA256 = "bee238bbeb3dc0a34bde4d0dedbaee1f98c009e8bb4226f03070054c12fb1372"
SERVER = {"llamaCppBuild": 11193, "reasoning": "on", "reasoningBudget": 6144, "parallel": 6, "context": 122880}
EFFORT = "xhigh"
SAMPLING = {"temperature": 0.6, "top_p": 0.95, "top_k": 20}
MAX_TOKENS = 8192
WORKERS = 6
TIMEOUT_SECONDS = 3600
FAILURE_RUN = 1000
ATTEMPTS = 3
ARMS = v2.ARMS
CONDITIONS = ("direct", "thinking")
ALPHA = 0.05


def request_body(sequent: list[dict[str, Any]], arm: str, condition: str) -> dict[str, Any]:
    body = v2.request_body(sequent, arm)
    body.pop("grammar")
    body.update(SAMPLING)
    body.update({"model": MODEL_ID, "max_tokens": MAX_TOKENS})
    body["chat_template_kwargs"] = ({"enable_thinking": True, "reasoning_effort": EFFORT}
                                    if condition == "thinking" else {"enable_thinking": False})
    return body


def call_model(task: dict[str, Any], arm: str, condition: str) -> dict[str, Any]:
    body = request_body(task["sequent"], arm, condition)
    encoded = json.dumps(body, ensure_ascii=False, separators=(",", ":")).encode("utf-8")
    request = urllib.request.Request(v1.MODEL_ENDPOINT, data=encoded, headers={"Content-Type": "application/json"},
                                     method="POST")
    started = time.perf_counter_ns()
    try:
        with urllib.request.urlopen(request, timeout=TIMEOUT_SECONDS) as response:
            result = json.loads(response.read().decode("utf-8"))
        if isinstance(result, dict) and "model" in result:
            result["model"] = MODEL_ID
        error = None
    except (urllib.error.URLError, TimeoutError, json.JSONDecodeError) as exception:
        result, error = None, f"{type(exception).__name__}: {exception}"
    return {"id": task["id"], "arm": arm, "condition": condition,
            "requestSha256": v1.sha256_text(encoded.decode("utf-8")),
            "elapsedMs": (time.perf_counter_ns() - started) / 1_000_000, "error": error, "response": result}


def server_failure(row: dict[str, Any]) -> bool:
    """Amendment 1: the output ends at the token limit in a run of one repeated non-whitespace character."""
    try:
        choice = row["response"]["choices"][0]
        message = choice["message"]
    except (KeyError, IndexError, TypeError):
        return False
    tail = ((message.get("reasoning_content") or "") + (message.get("content") or ""))[-FAILURE_RUN:]
    return (choice.get("finish_reason") == "length" and len(tail) == FAILURE_RUN and len(set(tail)) == 1
            and not tail.isspace())


def load_rows(path: Path) -> list[dict[str, Any]]:
    if not path.is_file():
        return []
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]


def dump_rows(path: Path, rows: list[dict[str, Any]]) -> None:
    v1.write_lf(path, "".join(json.dumps(r, ensure_ascii=False, separators=(",", ":")) + "\n" for r in rows))


def set_aside_failures(responses: dict[tuple[str, str, str], dict[str, Any]], path: Path) -> None:
    """Amendment 1: move server failures to FAILURES so that their requests are sent again, at most ATTEMPTS times in
    all. A failure recorded before an interruption left it in `path` as well is not recorded twice."""
    failures = load_rows(FAILURES)
    recorded = {json.dumps(r, sort_keys=True) for r in failures}
    attempts: dict[tuple[str, str, str], int] = {}
    for r in failures:
        attempts[(r["id"], r["arm"], r["condition"])] = attempts.get((r["id"], r["arm"], r["condition"]), 0) + 1
    moved = False
    for key in sorted(responses):
        if not server_failure(responses[key]):
            continue
        known = json.dumps(responses[key], sort_keys=True) in recorded
        if attempts.get(key, 0) + (0 if known else 1) < ATTEMPTS:
            if not known:
                failures.append(responses[key])
            del responses[key]
            moved = True
    if moved:
        dump_rows(FAILURES, failures)
        dump_rows(path, [responses[k] for k in sorted(responses)])


def collect(tasks: list[dict[str, Any]], path: Path | None) -> dict[tuple[str, str, str], dict[str, Any]]:
    responses = {(r["id"], r["arm"], r["condition"]): r for r in (load_rows(path) if path else [])}
    if path:
        set_aside_failures(responses, path)
    todo = [(t, a, c) for c in CONDITIONS for t in tasks for a in ARMS
            if (t["id"], a, c) not in responses or responses[(t["id"], a, c)]["error"] is not None]
    lock = threading.Lock()

    def record(row: dict[str, Any]) -> None:
        with lock:
            responses[(row["id"], row["arm"], row["condition"])] = row
            if path:
                dump_rows(path, [responses[k] for k in sorted(responses)])
            usage = (row["response"] or {}).get("usage", {})
            print(json.dumps({"id": row["id"], "arm": row["arm"], "condition": row["condition"],
                              "tokens": usage.get("completion_tokens"), "seconds": round(row["elapsedMs"] / 1000),
                              "error": row["error"], "serverFailure": server_failure(row)}), flush=True)

    with concurrent.futures.ThreadPoolExecutor(max_workers=WORKERS) as pool:
        for future in concurrent.futures.as_completed([pool.submit(call_model, t, a, c) for t, a, c in todo]):
            record(future.result())
    return responses


def reasoning_chars(response: dict[str, Any] | None) -> int:
    try:
        return len(response["choices"][0]["message"].get("reasoning_content") or "")  # type: ignore[index]
    except (KeyError, IndexError, TypeError):
        return 0


def evaluate(tasks: list[dict[str, Any]], responses: dict[tuple[str, str, str], dict[str, Any]]) -> list[dict[str, Any]]:
    rows = []
    for condition in CONDITIONS:
        subset = {(i, a): r for (i, a, c), r in responses.items() if c == condition}
        for row in v2.evaluate(tasks, subset):
            response = subset[(row["id"], row["arm"])]
            rows.append({"condition": condition, **row, "reasoningChars": reasoning_chars(response["response"]),
                         "serverFailure": server_failure(response)})
    return rows


def as_registered(tasks: list[dict[str, Any]], responses: dict[tuple[str, str, str], dict[str, Any]],
                  rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    """Amendment 1: the rows as registered, with each request's first server failure in place of its reruns."""
    first: dict[tuple[str, str, str], dict[str, Any]] = {}
    for r in load_rows(FAILURES):
        first.setdefault((r["id"], r["arm"], r["condition"]), r)
    if not first:
        return rows
    ids = {key[0] for key in first}
    redone = evaluate([t for t in tasks if t["id"] in ids],
                      {**{k: v for k, v in responses.items() if k[0] in ids}, **first})
    by = {(r["id"], r["arm"], r["condition"]): r for r in redone}
    return [by.get((r["id"], r["arm"], r["condition"]), r) for r in rows]


def amend(summary: dict[str, Any], tasks: list[dict[str, Any]],
          responses: dict[tuple[str, str, str], dict[str, Any]], rows: list[dict[str, Any]]) -> dict[str, Any]:
    failures = load_rows(FAILURES)
    registered = summarize(as_registered(tasks, responses, rows))
    summary["serverFailures"] = {
        "responses": len(failures),
        "requests": len({(r["id"], r["arm"], r["condition"]) for r in failures}),
        "byCondition": {c: sum(r["condition"] == c for r in failures) for c in CONDITIONS},
        "byArm": {a: sum(r["arm"] == a for r in failures) for a in ARMS},
        "sha256": v1.sha256_file(FAILURES) if FAILURES.exists() else None,
    }
    summary["asRegistered"] = {key: registered[key] for key in ("cells", "hypotheses", "checks")}
    summary["amendmentSha256"] = v1.sha256_file(AMENDMENT) if AMENDMENT.exists() else None
    return summary


def summarize(rows: list[dict[str, Any]]) -> dict[str, Any]:
    by = {(r["id"], r["arm"], r["condition"]): r for r in rows}
    ids = sorted({r["id"] for r in rows})
    cells: dict[str, Any] = {}
    for condition in CONDITIONS:
        for arm in ARMS:
            mine = [by[(i, arm, condition)] for i in ids]
            valid_tokens = sorted(r["completionTokens"] for r in mine if r["valid"])
            cells[f"{condition}/{arm}"] = {
                "valid": sum(r["valid"] for r in mine),
                "unprovable": sum(r["claim"] == "unprovable" for r in mine),
                "unparseable": sum(r["claim"] == "unparseable" for r in mine),
                "truncated": sum(r["finishReason"] == "length" for r in mine),
                "conversionFailures": sum(bool(r["conversion"]) for r in mine),
                "errors": sum(bool(r["error"]) for r in mine),
                "medianTokens": statistics.median(r["completionTokens"] for r in mine),
                "medianTokensValid": statistics.median(valid_tokens) if valid_tokens else None,
                "validByStratum": {s: sum(r["valid"] for r in mine if r["stratum"] == s)
                                   for s in sorted({r["stratum"] for r in mine})},
                "reasons": {},
            }
            for r in mine:
                key = (r["reason"] or r["claim"] or "")[:60]
                cells[f"{condition}/{arm}"]["reasons"][key] = cells[f"{condition}/{arm}"]["reasons"].get(key, 0) + 1

    def paired(first: tuple[str, str], second: tuple[str, str]) -> dict[str, Any]:
        (fa, fc), (sa, sc) = first, second
        wins = sum(1 for i in ids if by[(i, fa, fc)]["valid"] and not by[(i, sa, sc)]["valid"])
        losses = sum(1 for i in ids if by[(i, sa, sc)]["valid"] and not by[(i, fa, fc)]["valid"])
        return {"first": f"{fc}/{fa}", "second": f"{sc}/{sa}", "firstOnly": wins, "secondOnly": losses,
                "oneSidedP": v2.sign_test(wins, losses)}

    tests = {"H74": paired(("proofIds", "thinking"), ("proofIds", "direct")),
             "H75": paired(("net", "thinking"), ("proofIds", "thinking")),
             "H76": paired(("proofIds", "thinking"), ("net", "thinking")),
             "H77": paired(("proofIds", "thinking"), ("proof", "thinking"))}
    ordered = sorted(tests, key=lambda h: tests[h]["oneSidedP"])
    holm: dict[str, Any] = {}
    running, stopped = 0.0, False
    for rank, name in enumerate(ordered):
        p = tests[name]["oneSidedP"]
        running = max(running, min(1.0, (len(ordered) - rank) * p))
        rejected = not stopped and p <= ALPHA / (len(ordered) - rank)
        stopped = stopped or not rejected
        holm[name] = {"adjusted": running, "rejected": rejected}
    thinking_rows = [r for r in rows if r["condition"] == "thinking"]
    truncated = sum(r["finishReason"] == "length" for r in thinking_rows)
    return {
        "experiment": "representation-v0.3",
        "preregistrationSha256": v1.sha256_file(PREREG) if PREREG.exists() else None,
        "tasks": len(ids), "cells": cells,
        "hypotheses": {h: {"test": tests[h], "holm": holm[h], "supported": holm[h]["rejected"]} for h in tests},
        "checks": {"C20": {"errors": sum(bool(r["error"]) for r in rows),
                           "holds": not any(r["error"] for r in rows)},
                   "C21": {"thinkingTruncated": truncated, "thinkingAnswers": len(thinking_rows),
                           "holds": truncated < 0.1 * len(thinking_rows)},
                   "C22": {"serverFailures": sum(r["serverFailure"] for r in rows),
                           "holds": not any(r["serverFailure"] for r in rows)}},
        "resultsSha256": v1.sha256_file(RESULTS) if RESULTS.exists() else None,
        "responsesSha256": v1.sha256_file(RESPONSES) if RESPONSES.exists() else None,
    }


def corpus_positives() -> list[dict[str, Any]]:
    return [t for t in v1.load_corpus() if t["expectedProvable"]]


def registration_payload(tasks: list[dict[str, Any]]) -> dict[str, Any]:
    strata: dict[str, int] = {}
    for task in tasks:
        strata[v1.stratum(task)] = strata.get(v1.stratum(task), 0) + 1
    return {
        "experiment": "representation-v0.3",
        "question": "does a model that thinks before it answers write valid derivations, and does the lead of nets "
                    "over labelled derivations survive thinking",
        "arms": {"proof": "representation-v0.2's position-based derivation prompt and rendering",
                 "proofIds": "representation-v0.2's labelled derivation prompt and rendering, converted to positions "
                             "before Lean verifies it",
                 "net": "representation-v0.2's axiom-linking prompt and rendering"},
        "conditions": {"direct": "thinking off", "thinking": f"thinking on at reasoning effort {EFFORT}, with the "
                                                             f"server's thinking budget of "
                                                             f"{SERVER['reasoningBudget']} tokens"},
        "corpus": {"path": "experiments/model-v0.2/corpus.jsonl", "sha256": v1.sha256_file(v1.CORPUS_SOURCE),
                   "selection": "the positives", "taskCount": len(tasks), "strata": dict(sorted(strata.items()))},
        "model": {"id": MODEL_ID, "file": MODEL_FILE, "sha256": MODEL_SHA256, "endpoint": v1.MODEL_ENDPOINT,
                  "sampling": SAMPLING, "seed": v1.MODEL_SEED, "maxTokens": MAX_TOKENS, "grammar": None,
                  "server": SERVER, "concurrentRequests": WORKERS},
        "promptSha256": {"proofSystem": v1.sha256_text(v1.PROOF_SYSTEM),
                         "proofIdsSystem": v1.sha256_text(v2.PROOF_IDS_SYSTEM), "netSystem": v1.sha256_text(v1.NET_SYSTEM)},
        "implementationSha256": {name: v1.sha256_file(path) for name, path in IMPLEMENTATIONS.items()},
        "scoring": "as representation-v0.2: a proposal counts when Lean verifies it; a labelled derivation whose rules "
                   "do not apply to the sequent is invalid without reaching Lean",
        "hypotheses": {
            "H74": "with thinking, proofIds has more Lean-verified proposals than proofIds without thinking",
            "H75": "with thinking, net has more Lean-verified proposals than proofIds",
            "H76": "with thinking, proofIds has more Lean-verified proposals than net",
            "H77": "with thinking, proofIds has more Lean-verified proposals than proof",
        },
        "analysis": "exact one-sided sign test on the tasks that exactly one side of the pair verifies; H74 to H77 "
                    "are one family, decided by Holm's step-down procedure at family-wise alpha 0.05",
        "checks": {"C20": "no request fails", "C21": "fewer than 10% of the thinking answers stop at the token limit"},
        "reproducibility": "requests run six at a time on one server, so sampled outputs depend on the batch they "
                           "shared as well as on the seed; the committed responses, not a rerun, are the result",
        "report": "per condition and arm: verified proposals, unprovable and unparseable answers, truncations, "
                  "conversion failures, rejection reasons, median tokens, and verified proposals by stratum",
        "developmentChecksBeforeRegistration": [
            "grammar probe (scratch script, two development positives, all arms, thinking on at xhigh with each arm's "
            "grammar): every answer's content was empty, because the server applied the grammar to the whole output "
            "and the model could not think; hence no grammar in this study",
            "--pilot 4, with four concurrent requests: four development positives (bases at seed 950000; depth 2 and "
            "3; unique and one-label names), all arms under both conditions. Without thinking no proposal verified. "
            "With thinking 10 of 12 verified (proof 3, proofIds 3 with one unparseable, net 4), with 1,765 to 6,269 "
            "completion tokens; the thinking budget ended the thinking of three answers, and none reached the "
            "8,192-token limit",
        ],
        "resultsAbsentAtRegistration": True,
        "registeredLocalDate": time.strftime("%Y-%m-%d") + " America/Los_Angeles",
    }


def write_report(summary: dict[str, Any]) -> None:
    lines = ["# Representation-as-target model study v0.3", "",
             f"Qwen3.8-27B, with and without thinking, on {summary['tasks']} positives; frozen in "
             f"`preregistration.json` (SHA-256 `{summary['preregistrationSha256']}`).", "",
             "| Condition | Arm | Verified | Unprovable | Unparseable | Truncated | Median tokens |",
             "| --- | --- | ---: | ---: | ---: | ---: | ---: |"]
    for key, c in summary["cells"].items():
        condition, arm = key.split("/")
        lines.append(f"| {condition} | {arm} | {c['valid']} | {c['unprovable']} | {c['unparseable']} | "
                     f"{c['truncated']} | {c['medianTokens']} |")
    lines += ["", "## Hypotheses", ""]
    for name, h in summary["hypotheses"].items():
        t = h["test"]
        lines.append(f"- {name} ({t['first']} over {t['second']}): supported: {h['supported']}; {t['firstOnly']} "
                     f"against {t['secondOnly']} verified by one side alone (one-sided p {t['oneSidedP']:.3g}, Holm "
                     f"{h['holm']['adjusted']:.3g}).")
    checks = summary["checks"]
    lines += ["", f"Checks: C20 {checks['C20']}; C21 {checks['C21']}; C22 (amendment 1) {checks['C22']}.", ""]
    failures, registered = summary["serverFailures"], summary["asRegistered"]
    if failures["responses"]:
        lines += ["## Server failures (amendment 1)", "",
                  f"{failures['responses']} responses to {failures['requests']} requests ended at the token limit in a "
                  f"run of one repeated character (by condition {failures['byCondition']}, by arm "
                  f"{failures['byArm']}); they are kept in `server-failures.jsonl` and their requests were sent again. "
                  "As registered, with each request's first failure in place:", ""]
        for name, h in registered["hypotheses"].items():
            t = h["test"]
            lines.append(f"- {name}: supported: {h['supported']}; {t['firstOnly']} against {t['secondOnly']} "
                         f"(one-sided p {t['oneSidedP']:.3g}, Holm {h['holm']['adjusted']:.3g}).")
        lines += ["", f"Checks as registered: C21 {registered['checks']['C21']}.", ""]
    v1.write_lf(REPORT, "\n".join(lines) + "\n")


def main() -> int:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--pilot", type=int, metavar="N", help="the first N development positives")
    mode.add_argument("--register", action="store_true")
    mode.add_argument("--run", action="store_true")
    mode.add_argument("--check-committed", action="store_true")
    args = parser.parse_args()
    if args.pilot:
        tasks = [t for t in v2.pilot_tasks() if t["expectedProvable"]][:args.pilot]
        responses = collect(tasks, None)
        for row in evaluate(tasks, responses):
            print(json.dumps({k: row[k] for k in ("condition", "id", "arm", "claim", "valid", "reason",
                                                  "completionTokens", "finishReason", "reasoningChars")},
                             ensure_ascii=False))
        return 0
    tasks = corpus_positives()
    if args.register:
        if RESULTS.exists() or RESPONSES.exists():
            raise SystemExit("results already exist; registration must precede them")
        EXPERIMENT.mkdir(parents=True, exist_ok=True)
        v1.write_lf(PREREG, json.dumps(registration_payload(tasks), indent=1, sort_keys=True, ensure_ascii=False)
                    + "\n")
        print(f"registered {len(tasks)} tasks: {PREREG}")
        return 0
    prereg = json.loads(PREREG.read_text(encoding="utf-8"))
    amendment = json.loads(AMENDMENT.read_text(encoding="utf-8")) if AMENDMENT.exists() else {}
    for name, path in IMPLEMENTATIONS.items():
        expected = prereg["implementationSha256"][name]
        if name in amendment.get("implementationSha256AfterAmendment", {}):
            if amendment["implementationSha256BeforeAmendment"][name] != expected:
                raise SystemExit(f"amendment 1 does not start from the registered {name}")
            expected = amendment["implementationSha256AfterAmendment"][name]
        if expected != v1.sha256_file(path):
            raise SystemExit(f"implementation {name} changed since registration")
    if args.run:
        responses = collect(tasks, RESPONSES)
        rows = evaluate(tasks, responses)
        dump_rows(RESULTS, rows)
        summary = amend(summarize(rows), tasks, responses, rows)
        v1.write_lf(SUMMARY, json.dumps(summary, indent=1) + "\n")
        write_report(summary)
        print(json.dumps({h: v["supported"] for h, v in summary["hypotheses"].items()}))
        return 0
    responses = {(r["id"], r["arm"], r["condition"]): r for r in load_rows(RESPONSES)}
    rows = evaluate(tasks, responses)
    committed = json.loads(SUMMARY.read_text(encoding="utf-8"))
    recomputed = json.loads(json.dumps(amend(summarize(rows), tasks, responses, rows)))
    for key in ("responsesSha256", "preregistrationSha256", "amendmentSha256"):
        if recomputed[key] != committed[key]:
            raise SystemExit(f"hashes do not match the committed files ({key})")
    for key in ("cells", "hypotheses", "checks", "serverFailures", "asRegistered"):
        if recomputed[key] != committed[key]:
            raise SystemExit(f"the committed summary does not follow from the committed responses ({key})")
    print(f"representation-v0.3-check-ok: tasks={len(tasks)} rows={len(rows)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
