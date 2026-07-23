#!/usr/bin/env python3
"""Run the deterministic 1,000-task matched MLL experiment.

The three methods see exactly the same one-sided sequents:

* focused cut-free sequent search;
* direct proof-net generation by enumerating atom matchings over a fixed
  formula-occurrence skeleton;
* checker-guided one-edit repair of a deterministic invalid mutation.

The Python checker is the independent differential oracle from audit_v010.py.
Every emitted invalid mutation and every accepted output is batch rechecked by
the compiled Lean checker; accepted outputs must also pass the public runtime
sequentializer.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import math
import platform
import statistics
import subprocess
import sys
import time
import tracemalloc
from collections import Counter, defaultdict
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Iterable, Iterator

from audit_v010 import LAKE, ROOT, independent_certificate_check
from audit_v03_canonical import reindex_v1
from focused_search import (
    FocusedSearch,
    Formula,
    SearchLimitExceeded,
    canonical_sequent,
    dual,
    parse_formula,
)


OUTPUT_DIR = ROOT / "experiments" / "matched-v0.1"
CORPUS_PATH = OUTPUT_DIR / "corpus.jsonl"
RESULTS_PATH = OUTPUT_DIR / "results.jsonl"
SUMMARY_PATH = OUTPUT_DIR / "summary.json"
METHOD_BUDGET = 1_000


def compact_json(value: object) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"))


def sha256_text(value: str) -> str:
    return hashlib.sha256(value.encode("utf-8")).hexdigest()


def run_corpus() -> tuple[list[dict[str, Any]], str]:
    if CORPUS_PATH.is_file():
        payload = CORPUS_PATH.read_text(encoding="utf-8")
        lines = [line for line in payload.splitlines() if line]
        if len(lines) != 1_000:
            raise AssertionError(f"cached corpus has {len(lines)} tasks, expected 1000")
        return [json.loads(line) for line in lines], sha256_text(payload)
    completed = subprocess.run(
        [LAKE, "exe", "proofnet_ir_experiment_corpus"],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
        encoding="utf-8",
    )
    lines = [line for line in completed.stdout.splitlines() if line]
    if len(lines) != 1_000:
        raise AssertionError(f"expected 1000 corpus tasks, got {len(lines)}")
    payload = "\n".join(lines) + "\n"
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)
    CORPUS_PATH.write_text(payload, encoding="utf-8", newline="\n")
    return [json.loads(line) for line in lines], sha256_text(payload)


def formula_json(formula: Formula) -> dict[str, Any]:
    if formula[0] == "atom":
        return {"kind": "atom", "name": formula[1], "positive": formula[2]}
    return {
        "kind": formula[0],
        "left": formula_json(formula[1]),
        "right": formula_json(formula[2]),
    }


def link_key(link: dict[str, Any]) -> tuple[int, ...]:
    if link["kind"] == "axiom":
        return (0, int(link["left"]), int(link["right"]))
    rank = 1 if link["kind"] == "tensor" else 2
    return (
        rank,
        int(link["conclusion"]),
        int(link["left"]),
        int(link["right"]),
    )


def canonicalize_certificate(raw: dict[str, Any]) -> dict[str, Any]:
    result = copy.deepcopy(raw)
    normalized_links: list[dict[str, Any]] = []
    for link in result["links"]:
        if link["kind"] == "axiom" and int(link["right"]) < int(link["left"]):
            link["left"], link["right"] = link["right"], link["left"]
        normalized_links.append(link)
    result["version"] = "0.2"
    result["canonical"] = True
    result["links"] = sorted(normalized_links, key=link_key)
    result["conclusions"] = sorted(int(value) for value in result["conclusions"])
    return result


@dataclass
class Skeleton:
    certificate: dict[str, Any]
    formulas: list[Formula]
    atom_vertices: list[int]


def build_skeleton(sequent_json: list[dict[str, Any]]) -> Skeleton:
    formula_values: list[Formula] = []
    formula_values_json: list[dict[str, Any]] = []
    links: list[dict[str, Any]] = []
    atoms: list[int] = []

    def add(value: dict[str, Any]) -> int:
        parsed = parse_formula(value)
        if parsed[0] == "atom":
            vertex = len(formula_values)
            formula_values.append(parsed)
            formula_values_json.append(copy.deepcopy(value))
            atoms.append(vertex)
            return vertex
        left = add(value["left"])
        right = add(value["right"])
        conclusion = len(formula_values)
        formula_values.append(parsed)
        formula_values_json.append(copy.deepcopy(value))
        links.append(
            {
                "kind": parsed[0],
                "left": left,
                "right": right,
                "conclusion": conclusion,
            }
        )
        return conclusion

    conclusions = [add(value) for value in sequent_json]
    return Skeleton(
        certificate={
            "version": "0.2",
            "canonical": True,
            "formulas": formula_values_json,
            "links": links,
            "conclusions": conclusions,
        },
        formulas=formula_values,
        atom_vertices=atoms,
    )


@dataclass
class NetEnumerationStats:
    partial_nodes: int = 0
    complete_candidates: int = 0
    checker_calls: int = 0
    accepted_nets: int = 0
    completed: bool = True


def axiom_matchings(
    atom_vertices: tuple[int, ...],
    formulas: list[Formula],
    stats: NetEnumerationStats,
) -> Iterator[list[dict[str, Any]]]:
    stats.partial_nodes += 1
    if not atom_vertices:
        yield []
        return
    first = atom_vertices[0]
    target = dual(formulas[first])
    for offset, second in enumerate(atom_vertices[1:], start=1):
        if formulas[second] != target:
            continue
        rest = atom_vertices[1:offset] + atom_vertices[offset + 1 :]
        for tail in axiom_matchings(rest, formulas, stats):
            yield [{"kind": "axiom", "left": first, "right": second}, *tail]


@dataclass
class NetResult:
    found: bool
    certificate: dict[str, Any] | None
    elapsed_to_first_ms: float
    enumeration_ms: float
    peak_python_bytes: int
    stats: NetEnumerationStats


def generate_net(skeleton: Skeleton, candidate_limit: int) -> NetResult:
    stats = NetEnumerationStats()
    winner: dict[str, Any] | None = None
    first_elapsed = 0.0
    start = time.perf_counter_ns()
    tracemalloc.reset_peak()
    allocation_baseline = tracemalloc.get_traced_memory()[0]
    for matching in axiom_matchings(tuple(skeleton.atom_vertices), skeleton.formulas, stats):
        if stats.complete_candidates >= candidate_limit:
            stats.completed = False
            break
        stats.complete_candidates += 1
        candidate = copy.deepcopy(skeleton.certificate)
        candidate["links"] = [*candidate["links"], *matching]
        candidate = canonicalize_certificate(candidate)
        stats.checker_calls += 1
        if independent_certificate_check(candidate):
            stats.accepted_nets += 1
            if winner is None:
                winner = candidate
                first_elapsed = (time.perf_counter_ns() - start) / 1_000_000
    elapsed = (time.perf_counter_ns() - start) / 1_000_000
    peak = max(0, tracemalloc.get_traced_memory()[1] - allocation_baseline)
    return NetResult(winner is not None, winner, first_elapsed, elapsed, peak, stats)


@dataclass
class CountStats:
    calls: int = 0
    cache_hits: int = 0
    par_steps: int = 0
    tensor_choices: int = 0
    partitions: int = 0


class FocusedCounter:
    def __init__(self, max_calls: int, max_partitions: int) -> None:
        self.max_calls = max_calls
        self.max_partitions = max_partitions
        self.stats = CountStats()
        self.memo: dict[tuple[Formula, ...], int] = {}

    def count(self, sequent: list[Formula]) -> int:
        state = canonical_sequent(sequent)
        if state in self.memo:
            self.stats.cache_hits += 1
            return self.memo[state]
        self.stats.calls += 1
        if self.stats.calls > self.max_calls:
            raise SearchLimitExceeded(f"count exceeded {self.max_calls} states")
        for index, formula in enumerate(state):
            if formula[0] == "par":
                self.stats.par_steps += 1
                expanded = list(state[:index]) + [formula[1], formula[2]] + list(
                    state[index + 1 :]
                )
                result = self.count(expanded)
                self.memo[state] = result
                return result
        if len(state) == 2 and state[0][0] == "atom" and state[1] == dual(state[0]):
            self.memo[state] = 1
            return 1
        result = 0
        for tensor_index, formula in enumerate(state):
            if formula[0] != "tensor":
                continue
            self.stats.tensor_choices += 1
            context = list(state[:tensor_index] + state[tensor_index + 1 :])
            for mask in range(1 << len(context)):
                self.stats.partitions += 1
                if self.stats.partitions > self.max_partitions:
                    raise SearchLimitExceeded(
                        f"count exceeded {self.max_partitions} resource partitions"
                    )
                left_context = [
                    value for index, value in enumerate(context) if (mask >> index) & 1
                ]
                right_context = [
                    value for index, value in enumerate(context) if not (mask >> index) & 1
                ]
                left_count = self.count([formula[1], *left_context])
                if left_count == 0:
                    continue
                right_count = self.count([formula[2], *right_context])
                result += left_count * right_count
        self.memo[state] = result
        return result


def run_focused(
    sequent: list[Formula], max_calls: int
) -> tuple[dict[str, Any], int | None, dict[str, Any]]:
    engine = FocusedSearch(max_calls=max_calls, max_partitions=max_calls)
    tracemalloc.reset_peak()
    allocation_baseline = tracemalloc.get_traced_memory()[0]
    start = time.perf_counter_ns()
    limit_exceeded = False
    try:
        proof = engine.search(sequent)
    except SearchLimitExceeded:
        proof = None
        limit_exceeded = True
    elapsed = (time.perf_counter_ns() - start) / 1_000_000
    peak = max(0, tracemalloc.get_traced_memory()[1] - allocation_baseline)

    counter = FocusedCounter(max_calls=max_calls, max_partitions=max_calls)
    count_start = time.perf_counter_ns()
    count_complete = True
    try:
        proof_count: int | None = counter.count(sequent)
    except SearchLimitExceeded:
        proof_count = None
        count_complete = False
    count_elapsed = (time.perf_counter_ns() - count_start) / 1_000_000
    first = {
        "found": proof is not None,
        "limitExceeded": limit_exceeded,
        "elapsedMs": elapsed,
        "peakPythonBytes": peak,
        "derivationVerified": (
            proof is not None
            and canonical_sequent(focused_proof_sequent(proof))
            == canonical_sequent(sequent)
        ),
        **asdict(engine.stats),
    }
    counting = {
        "completed": count_complete,
        "proofTraces": proof_count,
        "elapsedMs": count_elapsed,
        **asdict(counter.stats),
    }
    return first, proof_count, counting


def focused_proof_sequent(proof: dict[str, Any]) -> list[Formula]:
    rule = proof["rule"]
    if rule == "axiom":
        left = parse_formula(proof["left"])
        right = parse_formula(proof["right"])
        if right != dual(left):
            raise AssertionError("focused proof contains a non-dual axiom")
        return [left, right]
    formula = parse_formula(proof["formula"])
    if rule == "par":
        if formula[0] != "par":
            raise AssertionError("focused par node names a non-par formula")
        premise = focused_proof_sequent(proof["premise"])
        try:
            premise.remove(formula[1])
            premise.remove(formula[2])
        except ValueError as error:
            raise AssertionError("focused par premise does not contain both premises") from error
        return [*premise, formula]
    if rule == "tensor":
        if formula[0] != "tensor":
            raise AssertionError("focused tensor node names a non-tensor formula")
        left = focused_proof_sequent(proof["left"])
        right = focused_proof_sequent(proof["right"])
        try:
            left.remove(formula[1])
            right.remove(formula[2])
        except ValueError as error:
            raise AssertionError("focused tensor premises do not contain their foci") from error
        return [*left, *right, formula]
    raise AssertionError(f"unknown focused proof rule: {rule!r}")


def mutate(certificate: dict[str, Any], index: int) -> tuple[str, dict[str, Any]]:
    result = copy.deepcopy(certificate)
    axioms = [i for i, link in enumerate(result["links"]) if link["kind"] == "axiom"]
    connectives = [
        i for i, link in enumerate(result["links"]) if link["kind"] != "axiom"
    ]
    mutation_class = index % 4
    if mutation_class == 0:
        label = "missing-axiom"
        del result["links"][axioms[0]]
    elif mutation_class == 1:
        label = "wrong-axiom-endpoint"
        if len(axioms) < 2:
            raise AssertionError("mutation requires two axiom links")
        result["links"][axioms[0]]["right"] = result["links"][axioms[1]]["right"]
    elif mutation_class == 2:
        label = "missing-connective"
        del result["links"][connectives[0]]
    else:
        label = "duplicated-link"
        result["links"].append(copy.deepcopy(result["links"][0]))
    result = canonicalize_certificate(result)
    if independent_certificate_check(result):
        raise AssertionError(f"mutation {label} unexpectedly remained valid")
    return label, result


def parent_counts(certificate: dict[str, Any]) -> list[int]:
    counts = [0] * len(certificate["formulas"])
    for link in certificate["links"]:
        if link["kind"] != "axiom":
            counts[int(link["left"])] += 1
            counts[int(link["right"])] += 1
    return counts


def producer_counts(certificate: dict[str, Any]) -> list[int]:
    counts = [0] * len(certificate["formulas"])
    for link in certificate["links"]:
        if link["kind"] != "axiom":
            counts[int(link["conclusion"])] += 1
    return counts


def repair_neighbors(certificate: dict[str, Any]) -> Iterator[dict[str, Any]]:
    seen: set[str] = set()

    def emit(candidate: dict[str, Any]) -> Iterator[dict[str, Any]]:
        normalized = canonicalize_certificate(candidate)
        key = compact_json(normalized)
        if key not in seen:
            seen.add(key)
            yield normalized

    # Delete one stored link.
    for index in range(len(certificate["links"])):
        candidate = copy.deepcopy(certificate)
        del candidate["links"][index]
        yield from emit(candidate)

    formulas = [parse_formula(value) for value in certificate["formulas"]]
    atoms = [index for index, formula in enumerate(formulas) if formula[0] == "atom"]

    # Add one locally typed axiom link.
    existing_axioms = {
        tuple(sorted((int(link["left"]), int(link["right"]))))
        for link in certificate["links"]
        if link["kind"] == "axiom"
    }
    for left_offset, left in enumerate(atoms):
        for right in atoms[left_offset + 1 :]:
            if formulas[right] != dual(formulas[left]):
                continue
            if (left, right) in existing_axioms:
                continue
            candidate = copy.deepcopy(certificate)
            candidate["links"].append({"kind": "axiom", "left": left, "right": right})
            yield from emit(candidate)

    # Replace one axiom endpoint with any locally dual atom occurrence.
    for link_index, link in enumerate(certificate["links"]):
        if link["kind"] != "axiom":
            continue
        left, right = int(link["left"]), int(link["right"])
        for replacement in atoms:
            if replacement != right and formulas[replacement] == dual(formulas[right]):
                candidate = copy.deepcopy(certificate)
                candidate["links"][link_index]["left"] = replacement
                yield from emit(candidate)
            if replacement != left and formulas[replacement] == dual(formulas[left]):
                candidate = copy.deepcopy(certificate)
                candidate["links"][link_index]["right"] = replacement
                yield from emit(candidate)

    # Add one missing locally typed connective producer. Prefer currently
    # parent-free premises; this is an observable structural condition, not a
    # reference-certificate hint.
    parents = parent_counts(certificate)
    producers = producer_counts(certificate)
    for conclusion, formula in enumerate(formulas):
        if formula[0] not in {"tensor", "par"} or producers[conclusion] != 0:
            continue
        left_formula, right_formula = formula[1], formula[2]
        lefts = [
            vertex
            for vertex, value in enumerate(formulas)
            if value == left_formula and parents[vertex] == 0 and vertex != conclusion
        ]
        rights = [
            vertex
            for vertex, value in enumerate(formulas)
            if value == right_formula and parents[vertex] == 0 and vertex != conclusion
        ]
        for left in lefts:
            for right in rights:
                if left == right:
                    continue
                candidate = copy.deepcopy(certificate)
                candidate["links"].append(
                    {
                        "kind": formula[0],
                        "left": left,
                        "right": right,
                        "conclusion": conclusion,
                    }
                )
                yield from emit(candidate)


def repair(certificate: dict[str, Any], candidate_limit: int) -> dict[str, Any]:
    tracemalloc.reset_peak()
    allocation_baseline = tracemalloc.get_traced_memory()[0]
    start = time.perf_counter_ns()
    checker_calls = 0
    winner: dict[str, Any] | None = None
    for candidate in repair_neighbors(certificate):
        if checker_calls >= candidate_limit:
            break
        checker_calls += 1
        if independent_certificate_check(candidate):
            winner = candidate
            break
    elapsed = (time.perf_counter_ns() - start) / 1_000_000
    return {
        "found": winner is not None,
        "certificate": winner,
        "elapsedMs": elapsed,
        "peakPythonBytes": max(
            0, tracemalloc.get_traced_memory()[1] - allocation_baseline
        ),
        "candidateCount": checker_calls,
        "checkerCalls": checker_calls,
        "editDistance": 1 if winner is not None else None,
        "limitExceeded": winner is None and checker_calls >= candidate_limit,
    }


def verify_with_lean(
    invalid: Iterable[dict[str, Any]], accepted: Iterable[dict[str, Any]]
) -> dict[str, int]:
    expectations: dict[str, bool] = {}
    for candidate in invalid:
        text = compact_json(canonicalize_certificate(candidate))
        expectations[text] = False
    for candidate in accepted:
        text = compact_json(canonicalize_certificate(candidate))
        previous = expectations.get(text)
        if previous is False:
            raise AssertionError("same certificate supplied as both invalid and accepted")
        expectations[text] = True
    payload = "\n".join(expectations) + "\n"
    completed = subprocess.run(
        [LAKE, "exe", "proofnet_ir_experiment_verify"],
        cwd=ROOT,
        input=payload,
        check=True,
        capture_output=True,
        text=True,
        encoding="utf-8",
    )
    outputs = [json.loads(line) for line in completed.stdout.splitlines() if line]
    if len(outputs) != len(expectations):
        raise AssertionError(
            f"Lean verifier returned {len(outputs)} rows for {len(expectations)} inputs"
        )
    accepted_count = 0
    rejected_count = 0
    sequentialized_count = 0
    for (certificate_text, expected), output in zip(expectations.items(), outputs):
        actual = bool(output["accepted"])
        sequentialized = bool(output["sequentialized"])
        if actual != expected:
            raise AssertionError(
                f"Lean/Python disagreement expected={expected}: {certificate_text[:160]}"
            )
        if actual and not sequentialized:
            raise AssertionError("Lean accepted an output that runtime sequentialization rejected")
        accepted_count += int(actual)
        rejected_count += int(not actual)
        sequentialized_count += int(sequentialized)
    return {
        "uniqueInputs": len(expectations),
        "accepted": accepted_count,
        "rejected": rejected_count,
        "sequentialized": sequentialized_count,
    }


def percentile(values: list[float], quantile: float) -> float:
    if not values:
        return 0.0
    ordered = sorted(values)
    index = min(len(ordered) - 1, math.ceil(quantile * len(ordered)) - 1)
    return ordered[index]


def method_summary(rows: list[dict[str, Any]], name: str) -> dict[str, Any]:
    values = [row[name] for row in rows]
    elapsed_key = "elapsedMs" if name != "netGeneration" else "elapsedToFirstMs"
    elapsed = [float(value[elapsed_key]) for value in values]
    checker_key = "checkerCalls"
    summary = {
        "successes": sum(bool(value["found"]) for value in values),
        "successRate": sum(bool(value["found"]) for value in values) / len(values),
        "limitExceeded": sum(bool(value.get("limitExceeded", False)) for value in values),
        "totalElapsedMs": sum(elapsed),
        "medianElapsedMs": statistics.median(elapsed),
        "p95ElapsedMs": percentile(elapsed, 0.95),
        "maxPeakPythonBytes": max(int(value["peakPythonBytes"]) for value in values),
        "totalCheckerCalls": sum(int(value.get(checker_key, 0)) for value in values),
    }
    if name == "focused":
        summary["totalStates"] = sum(int(value["calls"]) for value in values)
        summary["totalPartitions"] = sum(int(value["partitions"]) for value in values)
    elif name == "netGeneration":
        summary["totalPartialNodes"] = sum(int(value["partialNodes"]) for value in values)
        summary["totalCandidates"] = sum(int(value["candidateCount"]) for value in values)
        summary["enumerationIncomplete"] = sum(
            not bool(value["enumerationCompleted"]) for value in values
        )
    else:
        summary["totalCandidates"] = sum(int(value["candidateCount"]) for value in values)
    return summary


def focused_counting_summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    values = [row["focusedCounting"] for row in rows]
    elapsed = [float(value["elapsedMs"]) for value in values]
    completed_counts = [
        int(value["proofTraces"])
        for value in values
        if value["completed"] and value["proofTraces"] is not None
    ]
    return {
        "completedTasks": sum(bool(value["completed"]) for value in values),
        "incompleteTasks": sum(not bool(value["completed"]) for value in values),
        "totalElapsedMs": sum(elapsed),
        "medianElapsedMs": statistics.median(elapsed),
        "p95ElapsedMs": percentile(elapsed, 0.95),
        "totalStates": sum(int(value["calls"]) for value in values),
        "totalPartitions": sum(int(value["partitions"]) for value in values),
        "maxProofTracesOnCompletedTask": max(completed_counts, default=0),
    }


def summarize(
    rows: list[dict[str, Any]], corpus_sha256: str, verification: dict[str, int]
) -> dict[str, Any]:
    by_depth: dict[str, Any] = {}
    grouped: dict[int, list[dict[str, Any]]] = defaultdict(list)
    for row in rows:
        grouped[int(row["depth"])].append(row)
    for depth, group in sorted(grouped.items()):
        by_depth[str(depth)] = {
            "tasks": len(group),
            "focused": method_summary(group, "focused"),
            "focusedCounting": focused_counting_summary(group),
            "netGeneration": method_summary(group, "netGeneration"),
            "repair": method_summary(group, "repair"),
        }

    redundancy = [
        float(row["redundancy"]["log2Ratio"])
        for row in rows
        if row["redundancy"]["completed"]
    ]
    mutation_counts = Counter(row["repair"]["mutationClass"] for row in rows)
    mutation_success = Counter(
        row["repair"]["mutationClass"] for row in rows if row["repair"]["found"]
    )
    canonical_keys = [
        row["netGeneration"]["winnerReindexV1Sha256"]
        for row in rows
        if row["netGeneration"]["winnerReindexV1Sha256"] is not None
    ]
    verification_report = {
        **verification,
        "logicalInvalidOutputs": len(rows),
        "logicalAcceptedOutputs": sum(
            int(row["netGeneration"]["found"]) + int(row["repair"]["found"])
            for row in rows
        ),
        "deduplication": (
            "identical canonical certificates are checked and sequentialized once; "
            "the result covers every matching logical output"
        ),
    }
    return {
        "version": "matched-v0.1",
        "tasks": len(rows),
        "corpusSha256": corpus_sha256,
        "depthCounts": dict(sorted(Counter(row["depth"] for row in rows).items())),
        "limits": {
            "focusedStatesPerTask": METHOD_BUDGET,
            "focusedPartitionsPerTask": METHOD_BUDGET,
            "netCandidatesPerTask": METHOD_BUDGET,
            "repairCandidatesPerTask": METHOD_BUDGET,
        },
        "deterministic": True,
        "stochasticSeeds": "not applicable: all three methods are deterministic",
        "modelTokens": 0,
        "pythonAllocationMetric": "tracemalloc peak bytes; excludes Lean verifier RSS",
        "hardware": {
            "platform": platform.platform(),
            "machine": platform.machine(),
            "processor": platform.processor(),
            "python": platform.python_version(),
        },
        "overall": {
            "focused": method_summary(rows, "focused"),
            "focusedCounting": focused_counting_summary(rows),
            "netGeneration": method_summary(rows, "netGeneration"),
            "repair": method_summary(rows, "repair"),
        },
        "byDepth": by_depth,
        "repairByMutation": {
            name: {"tasks": count, "successes": mutation_success[name]}
            for name, count in sorted(mutation_counts.items())
        },
        "redundancy": {
            "completedTasks": len(redundancy),
            "medianLog2Ratio": statistics.median(redundancy) if redundancy else None,
            "p95Log2Ratio": percentile(redundancy, 0.95) if redundancy else None,
            "definition": "focused proof traces / max(1, accepted axiom-link proof nets)",
        },
        "canonicalDiversity": {
            "reindexV1DistinctWinners": len(set(canonical_keys)),
            "distinctSequentPayloads": len(set(row["sequentSha256"] for row in rows)),
            "scope": "v0.3 ReindexEquivalent normal form, not arbitrary graph isomorphism",
        },
        "leanVerification": verification_report,
    }


def refresh_committed_summary() -> dict[str, Any]:
    payload = RESULTS_PATH.read_text(encoding="utf-8")
    rows = [json.loads(line) for line in payload.splitlines() if line]
    old_summary = json.loads(SUMMARY_PATH.read_text(encoding="utf-8"))
    verification = {
        key: int(old_summary["leanVerification"][key])
        for key in ("uniqueInputs", "accepted", "rejected", "sequentialized")
    }
    corpus_payload = CORPUS_PATH.read_text(encoding="utf-8")
    summary = summarize(rows, sha256_text(corpus_payload), verification)
    summary["resultsSha256"] = sha256_text(payload)
    SUMMARY_PATH.write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
        newline="\n",
    )
    return summary


def check_committed() -> None:
    corpus_payload = CORPUS_PATH.read_text(encoding="utf-8")
    results_payload = RESULTS_PATH.read_text(encoding="utf-8")
    summary = json.loads(SUMMARY_PATH.read_text(encoding="utf-8"))
    corpus = [json.loads(line) for line in corpus_payload.splitlines() if line]
    rows = [json.loads(line) for line in results_payload.splitlines() if line]
    if len(corpus) != 1_000 or len(rows) != 1_000 or summary["tasks"] != 1_000:
        raise AssertionError("matched experiment must contain exactly 1000 tasks")
    if summary["corpusSha256"] != sha256_text(corpus_payload):
        raise AssertionError("committed corpus hash does not match summary")
    if summary["resultsSha256"] != sha256_text(results_payload):
        raise AssertionError("committed results hash does not match summary")
    expected_ids = [f"matched-{index}" for index in range(1_000)]
    if [row["id"] for row in rows] != expected_ids:
        raise AssertionError("result ids are missing, duplicated, or out of order")
    if not all(
        (not row["focused"]["found"] or row["focused"]["derivationVerified"])
        and row["netGeneration"]["found"]
        and row["repair"]["found"]
        for row in rows
    ):
        raise AssertionError("committed result contains an unverified claimed success")
    verification = summary["leanVerification"]
    if verification["accepted"] != verification["sequentialized"]:
        raise AssertionError("not every unique accepted output sequentialized")
    if verification["logicalAcceptedOutputs"] != 2_000:
        raise AssertionError("logical accepted-output coverage is incomplete")
    print(
        "matched-experiment-valid: 1000 tasks, hashes current, "
        "all claimed outputs covered by Lean verification"
    )


def run_experiment(limit: int | None) -> tuple[list[dict[str, Any]], dict[str, Any]]:
    corpus, corpus_sha256 = run_corpus()
    if limit is not None:
        corpus = corpus[:limit]
    tracemalloc.start()
    rows: list[dict[str, Any]] = []
    invalid_outputs: list[dict[str, Any]] = []
    accepted_outputs: list[dict[str, Any]] = []

    for position, task in enumerate(corpus):
        sequent_json = task["sequent"]
        sequent = [parse_formula(value) for value in sequent_json]
        reference = task["referenceCertificate"]
        if not independent_certificate_check(reference):
            raise AssertionError(f"Lean reference rejected by Python oracle: {task['id']}")

        focused, proof_traces, counting = run_focused(
            sequent, max_calls=METHOD_BUDGET
        )
        if focused["found"] and not focused["derivationVerified"]:
            raise AssertionError(f"focused proof verification failed on {task['id']}")
        skeleton = build_skeleton(sequent_json)
        net = generate_net(skeleton, candidate_limit=METHOD_BUDGET)

        repair_source = net.certificate if net.certificate is not None else reference
        mutation_class, invalid = mutate(repair_source, position)
        repaired = repair(invalid, candidate_limit=METHOD_BUDGET)
        if not repaired["found"] or repaired["certificate"] is None:
            raise AssertionError(f"repair failed on {task['id']} ({mutation_class})")

        invalid_outputs.append(invalid)
        if net.certificate is not None:
            accepted_outputs.append(net.certificate)
        accepted_outputs.append(repaired["certificate"])
        winner_key = reindex_v1(net.certificate) if net.certificate is not None else None
        redundancy_complete = proof_traces is not None and net.stats.completed
        ratio = (
            proof_traces / max(1, net.stats.accepted_nets)
            if redundancy_complete and proof_traces is not None
            else None
        )
        rows.append(
            {
                "id": task["id"],
                "seed": task["seed"],
                "depth": task["depth"],
                "sequentSha256": sha256_text(compact_json(sequent_json)),
                "focused": focused,
                "focusedCounting": counting,
                "netGeneration": {
                    "found": net.found,
                    "elapsedToFirstMs": net.elapsed_to_first_ms,
                    "fullEnumerationMs": net.enumeration_ms,
                    "peakPythonBytes": net.peak_python_bytes,
                    "partialNodes": net.stats.partial_nodes,
                    "candidateCount": net.stats.complete_candidates,
                    "checkerCalls": net.stats.checker_calls,
                    "acceptedNets": net.stats.accepted_nets,
                    "enumerationCompleted": net.stats.completed,
                    "winnerReindexV1Sha256": (
                        sha256_text(compact_json(winner_key))
                        if winner_key is not None
                        else None
                    ),
                },
                "repair": {
                    key: value
                    for key, value in repaired.items()
                    if key != "certificate"
                }
                | {"mutationClass": mutation_class},
                "redundancy": {
                    "completed": redundancy_complete,
                    "ratio": ratio,
                    "log2Ratio": math.log2(ratio) if ratio is not None and ratio > 0 else None,
                },
            }
        )
        if (position + 1) % 10 == 0:
            print(f"completed {position + 1}/{len(corpus)}", file=sys.stderr)

    verification = verify_with_lean(invalid_outputs, accepted_outputs)
    summary = summarize(rows, corpus_sha256, verification)
    return rows, summary


def main() -> int:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--refresh-summary", action="store_true")
    mode.add_argument("--check-committed", action="store_true")
    parser.add_argument("--limit", type=int)
    args = parser.parse_args()
    if args.limit is not None and not 1 <= args.limit <= 1_000:
        parser.error("--limit must be between 1 and 1000")
    if args.refresh_summary:
        if args.limit is not None:
            parser.error("--refresh-summary cannot be combined with --limit")
        print(json.dumps(refresh_committed_summary(), indent=2, sort_keys=True))
        return 0
    if args.check_committed:
        if args.limit is not None:
            parser.error("--check-committed cannot be combined with --limit")
        check_committed()
        return 0
    rows, summary = run_experiment(args.limit)
    payload = "\n".join(compact_json(row) for row in rows) + "\n"
    summary["resultsSha256"] = sha256_text(payload)
    if args.write:
        if args.limit is not None:
            parser.error("--write cannot be combined with --limit")
        OUTPUT_DIR.mkdir(parents=True, exist_ok=True)
        RESULTS_PATH.write_text(payload, encoding="utf-8", newline="\n")
        SUMMARY_PATH.write_text(
            json.dumps(summary, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
            newline="\n",
        )
        print(f"wrote {RESULTS_PATH} and {SUMMARY_PATH}")
    else:
        print(json.dumps(summary, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
