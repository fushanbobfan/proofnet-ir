#!/usr/bin/env python3
"""Prepare, run, and audit the preregistered model-backed MLL experiment.

The formal corpus pairs 90 fresh Lean-generated bases with polarity-balanced
positive tasks and atom-imbalanced negative tasks.  Direct proposal and repair
are separate model calls so the corrupted repair source cannot leak into the
direct condition.  Every parseable certificate is checked independently and
then batch-rechecked by Lean; every Lean-accepted output must sequentialize.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import itertools
import json
import math
import platform
import subprocess
import sys
import time
import tracemalloc
import urllib.error
import urllib.request
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any, Iterable, Iterator

from audit_v010 import LAKE, ROOT, independent_certificate_check
from focused_search import dual, parse_formula
from run_matched_experiment import (
    NetEnumerationStats,
    Skeleton,
    axiom_matchings,
    canonicalize_certificate,
    compact_json,
    generate_net,
    run_focused,
    sha256_text,
    verify_with_lean,
)


OUTPUT_DIR = ROOT / "experiments" / "model-v0.2"
CORPUS_PATH = OUTPUT_DIR / "corpus.jsonl"
PREREG_PATH = OUTPUT_DIR / "preregistration.json"
RAW_PATH = OUTPUT_DIR / "raw-responses.jsonl"
RESULTS_PATH = OUTPUT_DIR / "results.jsonl"
SUMMARY_PATH = OUTPUT_DIR / "summary.json"
PARTIAL_PATH = ROOT / "tmp" / "model-v0.2-raw.partial.jsonl"

IMPLEMENTATION_PATHS = {
    "runner": ROOT / "scripts" / "run_model_experiment.py",
    "focusedSearch": ROOT / "scripts" / "focused_search.py",
    "netGenerationAndLeanBridge": ROOT / "scripts" / "run_matched_experiment.py",
    "independentOracle": ROOT / "scripts" / "audit_v010.py",
    "leanCorpusGenerator": ROOT / "ProofNetIRModelExperimentCorpus.lean",
    "leanBatchVerifier": ROOT / "ProofNetIRExperimentVerify.lean",
}

BASE_COUNT = 90
TASK_COUNT = 180
METHOD_CANDIDATE_BUDGET = 1_000
WALL_CLOCK_BUDGET_MS = 60_000.0
MODEL_ENDPOINT = "http://127.0.0.1:8080/v1/chat/completions"
MODEL_ID = r"D:\ucla\models\gguf\Qwen3.6-35B-A3B-UD-Q4_K_XL.gguf"
MODEL_SEED = 20_260_723
MODEL_MAX_TOKENS = 128
MODEL_TIMEOUT_SECONDS = 60

DIRECT_SYSTEM = """You solve one unit-free cut-free MLL proof-net task. Reply with one JSON object and no prose. If unprovable: {\"c\":\"U\",\"pairs\":[]}. If provable: {\"c\":\"P\",\"pairs\":[[a,b],...]}. Pair every atom vertex exactly once with the same name and opposite sign. Fixed t/p links and ordered conclusions stay unchanged. The Danos-Regnier checker tests every par switching."""

REPAIR_SYSTEM = """You repair one unit-free cut-free MLL proof-net task. Reply with one JSON object and no prose. If the sequent is unprovable: {\"c\":\"U\",\"pairs\":[]}. If provable: {\"c\":\"P\",\"pairs\":[[a,b],...]}. Replace the supplied R axiom matching with a complete matching. Pair every atom vertex exactly once with the same name and opposite sign. Fixed t/p links and ordered conclusions stay unchanged. The Danos-Regnier checker tests every par switching."""


def file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def jsonl_payload(rows: Iterable[dict[str, Any]]) -> str:
    return "\n".join(compact_json(row) for row in rows) + "\n"


def implementation_hashes() -> dict[str, str]:
    return {
        name: file_sha256(path)
        for name, path in sorted(IMPLEMENTATION_PATHS.items())
    }


def recursive_atom_names(value: dict[str, Any]) -> Iterator[str]:
    if value["kind"] == "atom":
        yield str(value["name"])
        return
    yield from recursive_atom_names(value["left"])
    yield from recursive_atom_names(value["right"])


def rename_formula(value: dict[str, Any], names: dict[str, str]) -> dict[str, Any]:
    if value["kind"] == "atom":
        return {
            "kind": "atom",
            "name": names[str(value["name"])],
            "positive": bool(value["positive"]),
        }
    return {
        "kind": value["kind"],
        "left": rename_formula(value["left"], names),
        "right": rename_formula(value["right"], names),
    }


def label_mode_for(base_index: int) -> str:
    within_depth = base_index % 30
    return ("unique", "two-label", "one-label")[within_depth % 3]


def name_map(certificate: dict[str, Any], mode: str) -> dict[str, str]:
    original = sorted(
        {
            name
            for formula in certificate["formulas"]
            for name in recursive_atom_names(formula)
        }
    )
    if mode == "unique":
        return {name: f"r{index}" for index, name in enumerate(original)}
    if mode == "two-label":
        return {name: f"r{index % 2}" for index, name in enumerate(original)}
    if mode == "one-label":
        return {name: "r0" for name in original}
    raise AssertionError(f"unknown label mode: {mode}")


def fixed_links(certificate: dict[str, Any]) -> list[dict[str, Any]]:
    return [copy.deepcopy(link) for link in certificate["links"] if link["kind"] != "axiom"]


def axiom_links(certificate: dict[str, Any]) -> list[dict[str, Any]]:
    return [copy.deepcopy(link) for link in certificate["links"] if link["kind"] == "axiom"]


def with_axioms(skeleton: dict[str, Any], axioms: list[dict[str, Any]]) -> dict[str, Any]:
    candidate = copy.deepcopy(skeleton)
    candidate["links"] = [*fixed_links(skeleton), *copy.deepcopy(axioms)]
    return canonicalize_certificate(candidate)


def edge_set(axioms: list[dict[str, Any]]) -> set[tuple[int, int]]:
    return {
        tuple(sorted((int(link["left"]), int(link["right"]))))
        for link in axioms
    }


def matching_distance(
    left: list[dict[str, Any]], right: list[dict[str, Any]]
) -> int:
    return len(edge_set(left) - edge_set(right))


def compatible_matching_count(skeleton: Skeleton) -> int:
    """Count all locally typed complete axiom matchings without enumerating them."""
    positive: Counter[str] = Counter()
    negative: Counter[str] = Counter()
    for vertex in skeleton.atom_vertices:
        formula = skeleton.formulas[vertex]
        if formula[0] != "atom":
            raise AssertionError("skeleton atom list contains a non-atom")
        target = positive if bool(formula[2]) else negative
        target[str(formula[1])] += 1
    if positive != negative:
        return 0
    return math.prod(math.factorial(count) for count in positive.values())


def distance_ordered_axiom_matchings(
    skeleton: Skeleton, source: list[dict[str, Any]]
) -> Iterator[list[dict[str, Any]]]:
    """Enumerate typed matchings in exact edge distance from ``source``.

    Source edges that are locally typed form a partial matching.  For each
    distance layer we retain an exact subset of those preferred edges, then
    complete every label group while forbidding the other preferred edges.
    Invalid source edges contribute an unavoidable unit of distance.  Thus
    every compatible complete matching appears exactly once and layers are
    emitted in nondecreasing distance without materializing the factorial
    search space.
    """
    if compatible_matching_count(skeleton) == 0:
        return

    formulas = skeleton.formulas
    groups: dict[str, tuple[list[int], list[int]]] = {}
    labels = sorted({str(formulas[vertex][1]) for vertex in skeleton.atom_vertices})
    for label in labels:
        positives = sorted(
            vertex
            for vertex in skeleton.atom_vertices
            if str(formulas[vertex][1]) == label and bool(formulas[vertex][2])
        )
        negatives = sorted(
            vertex
            for vertex in skeleton.atom_vertices
            if str(formulas[vertex][1]) == label and not bool(formulas[vertex][2])
        )
        groups[label] = (positives, negatives)

    source_edges = edge_set(source)
    preferred = sorted(
        (positive, negative)
        for _, (positives, negatives) in groups.items()
        for positive in positives
        for negative in negatives
        if tuple(sorted((positive, negative))) in source_edges
    )
    if len({left for left, _ in preferred}) != len(preferred) or (
        len({right for _, right in preferred}) != len(preferred)
    ):
        raise AssertionError("repair source does not define a partial matching")

    for dropped_count in range(len(preferred) + 1):
        for dropped_indices in itertools.combinations(
            range(len(preferred)), dropped_count
        ):
            dropped = set(dropped_indices)
            assignment = {
                left: right
                for index, (left, right) in enumerate(preferred)
                if index not in dropped
            }
            used_negatives = set(assignment.values())
            grouped_positives: list[list[int]] = []
            group_options: list[list[tuple[int, ...]]] = []
            for label in labels:
                positives, negatives = groups[label]
                remaining_positives = [
                    vertex for vertex in positives if vertex not in assignment
                ]
                remaining_negatives = [
                    vertex for vertex in negatives if vertex not in used_negatives
                ]
                options = [
                    permutation
                    for permutation in itertools.permutations(remaining_negatives)
                    if all(
                        tuple(sorted((left, right))) not in source_edges
                        for left, right in zip(remaining_positives, permutation)
                    )
                ]
                grouped_positives.append(remaining_positives)
                group_options.append(options)
            for selected in itertools.product(*group_options):
                completed = dict(assignment)
                for positives, permutation in zip(grouped_positives, selected):
                    for left, right in zip(positives, permutation):
                        completed[left] = right
                yield [
                    {"kind": "axiom", "left": left, "right": completed[left]}
                    for left in sorted(completed)
                ]


def corrupt_axioms(
    skeleton: dict[str, Any], reference: list[dict[str, Any]], requested: int
) -> tuple[list[dict[str, Any]], int]:
    if len(reference) < requested:
        raise AssertionError("not enough axioms for preregistered repair distance")
    for indices in itertools.combinations(range(len(reference)), requested):
        rights = [int(reference[index]["right"]) for index in indices]
        for permuted in itertools.permutations(rights):
            if any(permuted[offset] == rights[offset] for offset in range(requested)):
                continue
            candidate_links = copy.deepcopy(reference)
            for offset, index in enumerate(indices):
                candidate_links[index]["right"] = permuted[offset]
            if matching_distance(reference, candidate_links) != requested:
                continue
            candidate = with_axioms(skeleton, candidate_links)
            if not independent_certificate_check(candidate):
                return axiom_links(candidate), requested
    raise AssertionError(
        f"could not construct invalid distance-{requested} repair source"
    )


def recompute_formula_table(
    skeleton: dict[str, Any], flipped_vertex: int
) -> list[dict[str, Any]]:
    original = copy.deepcopy(skeleton["formulas"])
    if original[flipped_vertex]["kind"] != "atom":
        raise AssertionError("negative mutation must target an atom vertex")
    original[flipped_vertex]["positive"] = not bool(
        original[flipped_vertex]["positive"]
    )
    producers = {
        int(link["conclusion"]): link
        for link in fixed_links(skeleton)
    }
    active: set[int] = set()
    memo: dict[int, dict[str, Any]] = {}

    def formula(vertex: int) -> dict[str, Any]:
        if vertex in memo:
            return memo[vertex]
        if vertex in active:
            raise AssertionError("connective skeleton contains a cycle")
        active.add(vertex)
        link = producers.get(vertex)
        if link is None:
            result = copy.deepcopy(original[vertex])
        else:
            result = {
                "kind": link["kind"],
                "left": formula(int(link["left"])),
                "right": formula(int(link["right"])),
            }
        active.remove(vertex)
        memo[vertex] = result
        return result

    return [formula(vertex) for vertex in range(len(original))]


def atom_balance(skeleton: dict[str, Any]) -> dict[str, int]:
    balance: Counter[str] = Counter()
    produced = {int(link["conclusion"]) for link in fixed_links(skeleton)}
    for vertex, value in enumerate(skeleton["formulas"]):
        if vertex in produced or value["kind"] != "atom":
            continue
        balance[str(value["name"])] += 1 if value["positive"] else -1
    return dict(sorted(balance.items()))


def task_sequent(skeleton: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        copy.deepcopy(skeleton["formulas"][int(vertex)])
        for vertex in skeleton["conclusions"]
    ]


def run_base_corpus() -> list[dict[str, Any]]:
    completed = subprocess.run(
        [LAKE, "exe", "proofnet_ir_model_experiment_corpus"],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
        encoding="utf-8",
    )
    rows = [json.loads(line) for line in completed.stdout.splitlines() if line]
    if len(rows) != BASE_COUNT:
        raise AssertionError(f"expected {BASE_COUNT} bases, got {len(rows)}")
    return rows


def prepare_tasks() -> list[dict[str, Any]]:
    tasks: list[dict[str, Any]] = []
    for base_index, base in enumerate(run_base_corpus()):
        reference = copy.deepcopy(base["referenceCertificate"])
        mode = label_mode_for(base_index)
        names = name_map(reference, mode)
        reference["formulas"] = [
            rename_formula(value, names) for value in reference["formulas"]
        ]
        reference = canonicalize_certificate(reference)
        if not independent_certificate_check(reference):
            raise AssertionError(f"renamed reference rejected: {base['id']}")
        skeleton = copy.deepcopy(reference)
        skeleton["links"] = fixed_links(reference)
        reference_axioms = axiom_links(reference)
        requested_distance = 2 if base_index % 2 == 0 else 3
        repair_axioms, actual_distance = corrupt_axioms(
            skeleton, reference_axioms, requested_distance
        )
        repair_source = with_axioms(skeleton, repair_axioms)
        if independent_certificate_check(repair_source):
            raise AssertionError("positive repair source unexpectedly accepted")

        common = {
            "baseId": base["id"],
            "baseIndex": base_index,
            "seed": int(base["seed"]),
            "depth": int(base["depth"]),
            "labelMode": mode,
        }
        tasks.append(
            common
            | {
                "id": f"model-{base_index}-positive",
                "expectedProvable": True,
                "sequent": task_sequent(skeleton),
                "skeleton": skeleton,
                "repairSourceAxioms": repair_axioms,
                "repairDistance": actual_distance,
                "referenceCertificate": reference,
                "atomBalance": atom_balance(skeleton),
            }
        )

        negative = copy.deepcopy(skeleton)
        flipped_vertex = int(reference_axioms[0]["left"])
        negative["formulas"] = recompute_formula_table(negative, flipped_vertex)
        negative_source = with_axioms(negative, reference_axioms)
        if independent_certificate_check(negative_source):
            raise AssertionError("atom-imbalanced negative unexpectedly accepted")
        imbalance = atom_balance(negative)
        if not any(value != 0 for value in imbalance.values()):
            raise AssertionError("negative task lacks its preregistered imbalance")
        tasks.append(
            common
            | {
                "id": f"model-{base_index}-negative",
                "expectedProvable": False,
                "sequent": task_sequent(negative),
                "skeleton": negative,
                "repairSourceAxioms": reference_axioms,
                "repairDistance": None,
                "referenceCertificate": None,
                "flippedAtomVertex": flipped_vertex,
                "atomBalance": imbalance,
            }
        )
    if len(tasks) != TASK_COUNT:
        raise AssertionError(f"expected {TASK_COUNT} prepared tasks")
    return tasks


def prepare() -> None:
    if any(path.exists() for path in (RAW_PATH, RESULTS_PATH, SUMMARY_PATH)):
        raise AssertionError("formal result artifacts already exist; refusing to preregister")
    tasks = prepare_tasks()
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)
    corpus_payload = jsonl_payload(tasks)
    CORPUS_PATH.write_text(corpus_payload, encoding="utf-8", newline="\n")
    strata: Counter[str] = Counter(
        f"depth-{task['depth']}:{task['labelMode']}:"
        f"{'positive' if task['expectedProvable'] else 'negative'}"
        for task in tasks
    )
    preregistration = {
        "version": "model-v0.2",
        "registeredLocalDate": "2026-07-22 America/Los_Angeles",
        "resultsAbsentAtRegistration": True,
        "developmentChecksBeforeRegistration": "fixture construction, independent checker agreement, and exact-distance repair enumeration were validated; no formal aggregate, task-specific model response, or result artifact existed",
        "taskCount": TASK_COUNT,
        "baseCount": BASE_COUNT,
        "freshSeedRange": [10_000, 10_089],
        "corpusSha256": sha256_text(corpus_payload),
        "strata": dict(sorted(strata.items())),
        "positiveConstruction": "Lean-generated accepted derivation, with deterministic atom-label collapse",
        "negativeConstruction": "flip one atom occurrence and recompute every connective ancestor; nonzero per-label polarity balance is an unprovability witness",
        "repairDistance": "number of reference axiom links absent from the repair source; positive tasks alternate exactly 2 and 3",
        "methods": [
            "focused search",
            "exhaustive proof-net generation",
            "distance-ordered checker-guided repair",
            "model direct proposal",
            "model repair proposal",
        ],
        "success": {
            "positive": "produce a certificate accepted by the independent oracle and Lean checker, then sequentialized by Lean",
            "negative": "return unprovable only when the method completed its bounded search, or for the model emit c=U",
        },
        "budgets": {
            "algorithmicCompleteCandidatesPerTask": METHOD_CANDIDATE_BUDGET,
            "wallClockMsPerTask": WALL_CLOCK_BUDGET_MS,
            "modelCallsPerTask": 2,
            "modelCompleteProposalsPerCall": 1,
            "modelMaxTokensPerCall": MODEL_MAX_TOKENS,
            "modelTimeoutSeconds": MODEL_TIMEOUT_SECONDS,
        },
        "model": {
            "endpoint": MODEL_ENDPOINT,
            "id": MODEL_ID,
            "temperature": 0,
            "seed": MODEL_SEED,
            "thinking": False,
        },
        "promptSha256": {
            "directSystem": sha256_text(DIRECT_SYSTEM),
            "repairSystem": sha256_text(REPAIR_SYSTEM),
        },
        "implementationSha256": implementation_hashes(),
        "interpretationBoundary": "first local-model held-out MLL study; not evidence for ordinary Lean/mathlib, arbitrary graph isomorphism, or a general model advantage",
    }
    PREREG_PATH.write_text(
        json.dumps(preregistration, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
        newline="\n",
    )
    print(
        f"preregistered {TASK_COUNT} tasks corpus_sha256="
        f"{preregistration['corpusSha256']}"
    )


def load_tasks() -> list[dict[str, Any]]:
    if not CORPUS_PATH.is_file() or not PREREG_PATH.is_file():
        raise AssertionError("run --prepare before the formal experiment")
    payload = CORPUS_PATH.read_text(encoding="utf-8")
    preregistration = json.loads(PREREG_PATH.read_text(encoding="utf-8"))
    if preregistration["corpusSha256"] != sha256_text(payload):
        raise AssertionError("preregistered corpus hash mismatch")
    tasks = [json.loads(line) for line in payload.splitlines() if line]
    if len(tasks) != TASK_COUNT:
        raise AssertionError(f"expected {TASK_COUNT} preregistered tasks")
    return tasks


def task_skeleton(task: dict[str, Any]) -> Skeleton:
    skeleton = copy.deepcopy(task["skeleton"])
    formulas = [parse_formula(value) for value in skeleton["formulas"]]
    atoms = [index for index, value in enumerate(formulas) if value[0] == "atom"]
    return Skeleton(skeleton, formulas, atoms)


def render_task(task: dict[str, Any], mode: str) -> str:
    skeleton = task["skeleton"]
    atoms = []
    for vertex, value in enumerate(skeleton["formulas"]):
        if value["kind"] == "atom":
            atoms.append(
                f"{vertex}:{value['name']}{'+' if value['positive'] else '-'}"
            )
    fixed = []
    for link in fixed_links(skeleton):
        prefix = "t" if link["kind"] == "tensor" else "p"
        fixed.append(
            f"{prefix}{int(link['left'])},{int(link['right'])}>"
            f"{int(link['conclusion'])}"
        )
    fields = [
        f"id={task['id']}",
        "A=" + ",".join(atoms),
        "F=" + ";".join(fixed),
        "C=" + ",".join(str(int(value)) for value in skeleton["conclusions"]),
    ]
    if mode == "repair":
        fields.append(
            "R="
            + ",".join(
                f"{int(link['left'])}-{int(link['right'])}"
                for link in task["repairSourceAxioms"]
            )
        )
    return " ".join(fields)


def request_body(task: dict[str, Any], mode: str) -> dict[str, Any]:
    system = DIRECT_SYSTEM if mode == "direct" else REPAIR_SYSTEM
    return {
        "model": MODEL_ID,
        "messages": [
            {"role": "system", "content": system},
            {"role": "user", "content": render_task(task, mode)},
        ],
        "temperature": 0,
        "seed": MODEL_SEED,
        "max_tokens": MODEL_MAX_TOKENS,
        "chat_template_kwargs": {"enable_thinking": False},
    }


def call_model(task: dict[str, Any], mode: str) -> dict[str, Any]:
    body = request_body(task, mode)
    encoded = compact_json(body).encode("utf-8")
    request = urllib.request.Request(
        MODEL_ENDPOINT,
        data=encoded,
        headers={"Content-Type": "application/json"},
        method="POST",
    )
    started = time.perf_counter_ns()
    try:
        with urllib.request.urlopen(request, timeout=MODEL_TIMEOUT_SECONDS) as response:
            result = json.loads(response.read().decode("utf-8"))
        error = None
    except (urllib.error.URLError, TimeoutError, json.JSONDecodeError) as exception:
        result = None
        error = f"{type(exception).__name__}: {exception}"
    elapsed_ms = (time.perf_counter_ns() - started) / 1_000_000
    return {
        "id": task["id"],
        "mode": mode,
        "requestSha256": sha256_text(encoded.decode("utf-8")),
        "elapsedMs": elapsed_ms,
        "error": error,
        "response": result,
    }


def load_partial() -> dict[tuple[str, str], dict[str, Any]]:
    if not PARTIAL_PATH.is_file():
        return {}
    rows = [
        json.loads(line)
        for line in PARTIAL_PATH.read_text(encoding="utf-8").splitlines()
        if line
    ]
    return {(row["id"], row["mode"]): row for row in rows}


def write_partial(rows: dict[tuple[str, str], dict[str, Any]]) -> None:
    PARTIAL_PATH.parent.mkdir(parents=True, exist_ok=True)
    ordered = [rows[key] for key in sorted(rows)]
    PARTIAL_PATH.write_text(jsonl_payload(ordered), encoding="utf-8", newline="\n")


def collect_model_responses(tasks: list[dict[str, Any]]) -> list[dict[str, Any]]:
    rows = load_partial()
    total = len(tasks) * 2
    for task in tasks:
        for mode in ("direct", "repair"):
            key = (task["id"], mode)
            if key in rows:
                expected_request_hash = sha256_text(
                    compact_json(request_body(task, mode))
                )
                if rows[key].get("requestSha256") != expected_request_hash:
                    raise AssertionError(
                        f"stale partial model response for {task['id']} {mode}"
                    )
                continue
            rows[key] = call_model(task, mode)
            write_partial(rows)
            completed = len(rows)
            print(f"model calls {completed}/{total}", file=sys.stderr)
    return [rows[key] for key in sorted(rows)]


def extract_json_object(content: str) -> dict[str, Any]:
    decoder = json.JSONDecoder()
    start = content.find("{")
    if start < 0:
        raise ValueError("no JSON object in model response")
    value, _ = decoder.raw_decode(content[start:])
    if not isinstance(value, dict):
        raise ValueError("model response is not an object")
    return value


def candidate_from_pairs(
    task: dict[str, Any], raw_pairs: object
) -> dict[str, Any]:
    if not isinstance(raw_pairs, list):
        raise ValueError("pairs must be a list")
    skeleton = task["skeleton"]
    atom_vertices = {
        index
        for index, value in enumerate(skeleton["formulas"])
        if value["kind"] == "atom"
    }
    seen: list[int] = []
    links: list[dict[str, Any]] = []
    for raw_pair in raw_pairs:
        if (
            not isinstance(raw_pair, list)
            or len(raw_pair) != 2
            or not all(isinstance(value, int) and not isinstance(value, bool) for value in raw_pair)
        ):
            raise ValueError("every pair must contain exactly two integer vertices")
        left, right = int(raw_pair[0]), int(raw_pair[1])
        if left == right or left not in atom_vertices or right not in atom_vertices:
            raise ValueError("pair names a non-atom or self endpoint")
        seen.extend((left, right))
        links.append({"kind": "axiom", "left": left, "right": right})
    if len(seen) != len(set(seen)) or set(seen) != atom_vertices:
        raise ValueError("pairs do not cover every atom exactly once")
    return with_axioms(skeleton, links)


def score_model(
    task: dict[str, Any], raw: dict[str, Any]
) -> tuple[dict[str, Any], dict[str, Any] | None]:
    result: dict[str, Any] = {
        "success": False,
        "prediction": "error",
        "accepted": False,
        "parseError": None,
        "elapsedMs": float(raw["elapsedMs"]),
        "promptTokens": 0,
        "completionTokens": 0,
        "totalTokens": 0,
        "finishReason": None,
        "responseModel": None,
        "systemFingerprint": None,
        "wallClockExceeded": float(raw["elapsedMs"]) > WALL_CLOCK_BUDGET_MS,
    }
    if raw.get("error") is not None or raw.get("response") is None:
        result["parseError"] = raw.get("error") or "missing response"
        return result, None
    response = raw["response"]
    usage = response.get("usage", {})
    result["promptTokens"] = int(usage.get("prompt_tokens", 0))
    result["completionTokens"] = int(usage.get("completion_tokens", 0))
    result["totalTokens"] = int(usage.get("total_tokens", 0))
    result["responseModel"] = response.get("model")
    result["systemFingerprint"] = response.get("system_fingerprint")
    try:
        choice = response["choices"][0]
        result["finishReason"] = choice.get("finish_reason")
        value = extract_json_object(str(choice["message"].get("content", "")))
        classification = value.get("c")
        if classification == "U":
            if value.get("pairs") != []:
                raise ValueError("U response must contain an empty pairs list")
            within_time = not bool(result["wallClockExceeded"])
            result["prediction"] = "unprovable" if within_time else "timeout"
            result["success"] = not bool(task["expectedProvable"]) and within_time
            return result, None
        if classification != "P":
            raise ValueError("c must be P or U")
        result["prediction"] = "provable"
        candidate = candidate_from_pairs(task, value.get("pairs"))
        accepted = independent_certificate_check(candidate)
        result["accepted"] = accepted
        result["candidateSha256"] = sha256_text(compact_json(candidate))
        within_time = not bool(result["wallClockExceeded"])
        result["prediction"] = "provable" if within_time else "timeout"
        result["success"] = (
            bool(task["expectedProvable"]) and accepted and within_time
        )
        return result, candidate
    except (KeyError, IndexError, TypeError, ValueError) as exception:
        result["parseError"] = f"{type(exception).__name__}: {exception}"
        return result, None


def classify_bounded(
    expected: bool, found: bool, completed: bool
) -> tuple[bool, str]:
    if found:
        return expected, "provable"
    if completed:
        return not expected, "unprovable"
    return False, "unknown"


def distance_ordered_repair(
    task: dict[str, Any], candidate_limit: int
) -> tuple[dict[str, Any], dict[str, Any] | None]:
    skeleton = task_skeleton(task)
    source = task["repairSourceAxioms"]
    started = time.perf_counter_ns()
    winner: dict[str, Any] | None = None
    checker_calls = 0
    compatible_matchings = compatible_matching_count(skeleton)
    for matching in distance_ordered_axiom_matchings(skeleton, source):
        if checker_calls >= candidate_limit:
            break
        checker_calls += 1
        candidate = with_axioms(skeleton.certificate, matching)
        if independent_certificate_check(candidate):
            winner = candidate
            break
    elapsed_ms = (time.perf_counter_ns() - started) / 1_000_000
    completed = compatible_matchings <= candidate_limit
    success, prediction = classify_bounded(
        bool(task["expectedProvable"]), winner is not None, completed
    )
    within_time = elapsed_ms <= WALL_CLOCK_BUDGET_MS
    return (
        {
            "success": success and within_time,
            "prediction": prediction if within_time else "timeout",
            "found": winner is not None,
            "enumerationCompleted": completed,
            "compatibleMatchings": compatible_matchings,
            "candidateCount": checker_calls,
            "checkerCalls": checker_calls,
            "elapsedMs": elapsed_ms,
            "wallClockExceeded": not within_time,
            "winnerDistanceFromSource": (
                matching_distance(source, axiom_links(winner))
                if winner is not None
                else None
            ),
        },
        winner,
    )


def baseline_row(
    task: dict[str, Any]
) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    expected = bool(task["expectedProvable"])
    sequent = [parse_formula(value) for value in task["sequent"]]
    focused, _, _ = run_focused(sequent, max_calls=METHOD_CANDIDATE_BUDGET)
    focused_completed = not bool(focused["limitExceeded"])
    focused_success, focused_prediction = classify_bounded(
        expected, bool(focused["found"]), focused_completed
    )
    focused_within_time = float(focused["elapsedMs"]) <= WALL_CLOCK_BUDGET_MS
    focused_result = {
        "success": focused_success and focused_within_time,
        "prediction": focused_prediction if focused_within_time else "timeout",
        "found": bool(focused["found"]),
        "searchCompleted": focused_completed,
        "states": int(focused["calls"]),
        "partitions": int(focused["partitions"]),
        "elapsedMs": float(focused["elapsedMs"]),
        "wallClockExceeded": not focused_within_time,
        "derivationVerified": bool(focused["derivationVerified"]),
    }

    net = generate_net(task_skeleton(task), METHOD_CANDIDATE_BUDGET)
    net_success, net_prediction = classify_bounded(
        expected, net.found, net.stats.completed
    )
    net_within_time = net.enumeration_ms <= WALL_CLOCK_BUDGET_MS
    net_result = {
        "success": net_success and net_within_time,
        "prediction": net_prediction if net_within_time else "timeout",
        "found": net.found,
        "enumerationCompleted": net.stats.completed,
        "candidateCount": net.stats.complete_candidates,
        "checkerCalls": net.stats.checker_calls,
        "acceptedNets": net.stats.accepted_nets,
        "elapsedMs": net.enumeration_ms,
        "wallClockExceeded": not net_within_time,
    }

    repair_result, repair_winner = distance_ordered_repair(
        task, METHOD_CANDIDATE_BUDGET
    )
    accepted = [
        candidate
        for candidate in (net.certificate, repair_winner)
        if candidate is not None
    ]
    return {
        "focused": focused_result,
        "netGeneration": net_result,
        "algorithmicRepair": repair_result,
    }, accepted


def method_summary(rows: list[dict[str, Any]], name: str) -> dict[str, Any]:
    values = [row[name] for row in rows]
    elapsed = sorted(float(value["elapsedMs"]) for value in values)
    return {
        "tasks": len(values),
        "successes": sum(int(bool(value["success"])) for value in values),
        "successRate": (
            sum(int(bool(value["success"])) for value in values) / len(values)
            if values
            else 0.0
        ),
        "predictions": dict(sorted(Counter(value["prediction"] for value in values).items())),
        "medianElapsedMs": elapsed[len(elapsed) // 2] if elapsed else 0.0,
        "p95ElapsedMs": (
            elapsed[min(len(elapsed) - 1, math.ceil(0.95 * len(elapsed)) - 1)]
            if elapsed
            else 0.0
        ),
        "totalElapsedMs": sum(elapsed),
        "totalTokens": sum(int(value.get("totalTokens", 0)) for value in values),
        "totalCheckerCalls": sum(int(value.get("checkerCalls", 0)) for value in values),
    }


METHOD_NAMES = (
    "focused",
    "netGeneration",
    "algorithmicRepair",
    "modelDirect",
    "modelRepair",
)


def summarize_rows(rows: list[dict[str, Any]]) -> dict[str, Any]:
    groups: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for row in rows:
        polarity = "positive" if row["expectedProvable"] else "negative"
        groups[f"depth-{row['depth']}"].append(row)
        groups[row["labelMode"]].append(row)
        groups[polarity].append(row)
    return {
        "overall": {name: method_summary(rows, name) for name in METHOD_NAMES},
        "groups": {
            group: {name: method_summary(values, name) for name in METHOD_NAMES}
            for group, values in sorted(groups.items())
        },
    }


def formal_run(write: bool) -> dict[str, Any]:
    tasks = check_preregistered(regenerate=False)
    raw_rows = collect_model_responses(tasks)
    raw_by_key = {(row["id"], row["mode"]): row for row in raw_rows}
    tracemalloc.start()
    rows: list[dict[str, Any]] = []
    invalid_outputs: list[dict[str, Any]] = []
    accepted_outputs: list[dict[str, Any]] = []

    for position, task in enumerate(tasks):
        expected = bool(task["expectedProvable"])
        reference = task.get("referenceCertificate")
        if expected:
            if reference is None or not independent_certificate_check(reference):
                raise AssertionError(f"positive reference rejected: {task['id']}")
            accepted_outputs.append(reference)
        repair_source = with_axioms(task["skeleton"], task["repairSourceAxioms"])
        if independent_certificate_check(repair_source):
            raise AssertionError(f"repair source accepted: {task['id']}")
        invalid_outputs.append(repair_source)

        baselines, baseline_accepted = baseline_row(task)
        accepted_outputs.extend(baseline_accepted)
        direct, direct_candidate = score_model(
            task, raw_by_key[(task["id"], "direct")]
        )
        repair, repair_candidate = score_model(
            task, raw_by_key[(task["id"], "repair")]
        )
        for candidate in (direct_candidate, repair_candidate):
            if candidate is None:
                continue
            if independent_certificate_check(candidate):
                accepted_outputs.append(candidate)
            else:
                invalid_outputs.append(candidate)
        rows.append(
            {
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
        )
        if (position + 1) % 10 == 0:
            print(f"scored {position + 1}/{len(tasks)}", file=sys.stderr)

    verification = verify_with_lean(invalid_outputs, accepted_outputs)
    raw_payload = jsonl_payload(raw_rows)
    results_payload = jsonl_payload(rows)
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
        "version": "model-v0.2",
        "taskCount": len(rows),
        "positiveTasks": sum(int(row["expectedProvable"]) for row in rows),
        "negativeTasks": sum(int(not row["expectedProvable"]) for row in rows),
        "corpusSha256": file_sha256(CORPUS_PATH),
        "preregistrationSha256": file_sha256(PREREG_PATH),
        "rawResponsesSha256": sha256_text(raw_payload),
        "resultsSha256": sha256_text(results_payload),
        "model": {
            "requestedId": MODEL_ID,
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
        "methods": summarize_rows(rows),
        "leanVerification": verification,
        "hardware": {
            "platform": platform.platform(),
            "machine": platform.machine(),
            "python": platform.python_version(),
        },
        "interpretationBoundary": "held-out unit-free cut-free MLL local-model experiment only; no ordinary Lean/mathlib or general model-advantage claim",
    }
    if write:
        RAW_PATH.write_text(raw_payload, encoding="utf-8", newline="\n")
        RESULTS_PATH.write_text(results_payload, encoding="utf-8", newline="\n")
        SUMMARY_PATH.write_text(
            json.dumps(summary, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
            newline="\n",
        )
        print(f"wrote {RAW_PATH}, {RESULTS_PATH}, and {SUMMARY_PATH}")
    return summary


def check_committed() -> None:
    tasks = check_preregistered(regenerate=False)
    if not all(path.is_file() for path in (RAW_PATH, RESULTS_PATH, SUMMARY_PATH)):
        raise AssertionError("model experiment artifacts are incomplete")
    raw_payload = RAW_PATH.read_text(encoding="utf-8")
    results_payload = RESULTS_PATH.read_text(encoding="utf-8")
    raw = [json.loads(line) for line in raw_payload.splitlines() if line]
    results = [json.loads(line) for line in results_payload.splitlines() if line]
    summary = json.loads(SUMMARY_PATH.read_text(encoding="utf-8"))
    if len(tasks) != TASK_COUNT or len(results) != TASK_COUNT or len(raw) != TASK_COUNT * 2:
        raise AssertionError("committed model experiment cardinality mismatch")
    if summary["rawResponsesSha256"] != sha256_text(raw_payload):
        raise AssertionError("raw response hash mismatch")
    if summary["resultsSha256"] != sha256_text(results_payload):
        raise AssertionError("result hash mismatch")
    if summary["corpusSha256"] != file_sha256(CORPUS_PATH):
        raise AssertionError("summary corpus hash mismatch")
    if summary["preregistrationSha256"] != file_sha256(PREREG_PATH):
        raise AssertionError("summary preregistration hash mismatch")
    if not all(
        all(name in row and isinstance(row[name]["success"], bool) for name in METHOD_NAMES)
        for row in results
    ):
        raise AssertionError("method result schema mismatch")
    verification = summary["leanVerification"]
    if verification["accepted"] != verification["sequentialized"]:
        raise AssertionError("not every Lean-accepted output sequentialized")
    print(
        f"model-experiment-valid: {TASK_COUNT} tasks, {TASK_COUNT * 2} raw calls, "
        "hashes current, every accepted output sequentialized"
    )


def check_preregistered(regenerate: bool = True) -> list[dict[str, Any]]:
    tasks = load_tasks()
    preregistration = json.loads(PREREG_PATH.read_text(encoding="utf-8"))
    if preregistration.get("implementationSha256") != implementation_hashes():
        raise AssertionError("preregistered implementation hash mismatch")
    strata: Counter[str] = Counter()
    for task in tasks:
        expected = bool(task["expectedProvable"])
        polarity = "positive" if expected else "negative"
        strata[f"depth-{task['depth']}:{task['labelMode']}:{polarity}"] += 1
        if expected:
            reference = task.get("referenceCertificate")
            if reference is None or not independent_certificate_check(reference):
                raise AssertionError(f"preregistered positive rejected: {task['id']}")
            if task["repairDistance"] not in {2, 3}:
                raise AssertionError("positive repair distance is not 2 or 3")
            reference_distance = matching_distance(
                task["repairSourceAxioms"], axiom_links(reference)
            )
            if reference_distance != task["repairDistance"]:
                raise AssertionError("positive reference distance drifted")
            repair_result, repair_winner = distance_ordered_repair(
                task, METHOD_CANDIDATE_BUDGET
            )
            if (
                repair_winner is None
                or not repair_result["success"]
                or repair_result["winnerDistanceFromSource"]
                > task["repairDistance"]
            ):
                raise AssertionError(
                    f"distance-ordered repair fixture failed: {task['id']}"
                )
        elif not any(int(value) != 0 for value in task["atomBalance"].values()):
            raise AssertionError("negative task lost its polarity imbalance")
        elif compatible_matching_count(task_skeleton(task)) != 0:
            raise AssertionError("negative task unexpectedly has a complete axiom matching")
        repair_source = with_axioms(task["skeleton"], task["repairSourceAxioms"])
        if independent_certificate_check(repair_source):
            raise AssertionError(f"preregistered repair source accepted: {task['id']}")
    if len(strata) != 18 or set(strata.values()) != {10}:
        raise AssertionError(f"unexpected preregistered strata: {dict(strata)}")
    if regenerate:
        regenerated = jsonl_payload(prepare_tasks())
        committed = CORPUS_PATH.read_text(encoding="utf-8")
        if regenerated != committed:
            raise AssertionError("Lean/Python corpus regeneration drifted")
    print(
        f"model-preregistration-valid: {TASK_COUNT} tasks, 18 balanced strata, "
        f"corpus_sha256={file_sha256(CORPUS_PATH)}"
    )
    return tasks


def smoke_model() -> None:
    tasks = load_tasks()[:2]
    for task in tasks:
        for mode in ("direct", "repair"):
            raw = call_model(task, mode)
            result, _ = score_model(task, raw)
            print(compact_json({"id": task["id"], "mode": mode, "result": result}))


def main() -> int:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--prepare", action="store_true")
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check-preregistered", action="store_true")
    mode.add_argument("--check-committed", action="store_true")
    mode.add_argument("--smoke-model", action="store_true")
    args = parser.parse_args()
    if args.prepare:
        prepare()
    elif args.write:
        print(json.dumps(formal_run(write=True), indent=2, sort_keys=True))
    elif args.check_preregistered:
        check_preregistered()
    elif args.check_committed:
        check_committed()
    else:
        smoke_model()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
