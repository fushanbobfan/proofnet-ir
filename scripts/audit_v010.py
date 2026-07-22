#!/usr/bin/env python3
"""Differential mathematical audit for the ProofNet-IR v0.1 checker.

The subject values come from compiled Lean executables. This script implements
independent Python union-find and MLL-certificate oracles and fails on the first
counterexample.
"""

from __future__ import annotations

import itertools
import json
import shutil
import subprocess
import sys
from pathlib import Path
from typing import Any, Iterable


ROOT = Path(__file__).resolve().parents[1]


def find_lake() -> str:
    """Find Lake even when a non-login Windows shell omits Elan from PATH."""
    on_path = shutil.which("lake")
    if on_path is not None:
        return on_path
    elan_bin = Path.home() / ".elan" / "bin"
    for executable in ("lake", "lake.exe"):
        elan_lake = elan_bin / executable
        if elan_lake.is_file():
            return str(elan_lake)
    raise FileNotFoundError("lake was not found on PATH or under ~/.elan/bin")


LAKE = find_lake()


def run_lean(executable: str) -> list[str]:
    completed = subprocess.run(
        [LAKE, "exe", executable],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
        encoding="utf-8",
    )
    return completed.stdout.splitlines()


def candidate_edges(vertex_count: int) -> list[tuple[int, int]]:
    return [
        (first, second)
        for first in range(vertex_count)
        for second in range(vertex_count)
        if first < second
    ]


def union_find_tree(vertex_count: int, edges: Iterable[tuple[int, int]]) -> bool:
    if vertex_count <= 0:
        return False
    parent = list(range(vertex_count))
    rank = [0] * vertex_count

    def find(vertex: int) -> int:
        while parent[vertex] != vertex:
            parent[vertex] = parent[parent[vertex]]
            vertex = parent[vertex]
        return vertex

    edge_count = 0
    for first, second in edges:
        edge_count += 1
        if not (0 <= first < vertex_count and 0 <= second < vertex_count):
            return False
        if first == second:
            return False
        first_root, second_root = find(first), find(second)
        if first_root == second_root:
            return False
        if rank[first_root] < rank[second_root]:
            first_root, second_root = second_root, first_root
        parent[second_root] = first_root
        if rank[first_root] == rank[second_root]:
            rank[first_root] += 1

    root = find(0)
    return edge_count == vertex_count - 1 and all(
        find(vertex) == root for vertex in range(vertex_count)
    )


def audit_graphs() -> int:
    lines = run_lean("proofnet_ir_audit_graph")
    expected_count = sum(2 ** (n * (n - 1) // 2) for n in range(7))
    if len(lines) != expected_count:
        raise AssertionError(
            f"graph case count mismatch: Lean={len(lines)}, expected={expected_count}"
        )
    for line in lines:
        vertex_text, mask_text, lean_text = line.split("\t")
        vertex_count, mask = int(vertex_text), int(mask_text)
        candidates = candidate_edges(vertex_count)
        edges = [
            edge for index, edge in enumerate(candidates) if (mask >> index) & 1
        ]
        expected = union_find_tree(vertex_count, edges)
        actual = lean_text == "1"
        if actual != expected:
            raise AssertionError(
                "graph counterexample: "
                f"n={vertex_count}, mask={mask}, edges={edges}, "
                f"Lean={actual}, oracle={expected}"
            )
    return len(lines)


Formula = tuple[Any, ...]


def parse_formula(value: dict[str, Any]) -> Formula:
    tag = value.get("tag", value.get("kind"))
    if tag == "atom":
        return ("atom", value["name"], bool(value["positive"]))
    if tag in {"tensor", "par"}:
        return (tag, parse_formula(value["left"]), parse_formula(value["right"]))
    raise AssertionError(f"unknown formula tag: {tag!r}")


def dual(formula: Formula) -> Formula:
    tag = formula[0]
    if tag == "atom":
        return ("atom", formula[1], not formula[2])
    if tag == "tensor":
        return ("par", dual(formula[1]), dual(formula[2]))
    if tag == "par":
        return ("tensor", dual(formula[1]), dual(formula[2]))
    raise AssertionError(f"unknown formula: {formula!r}")


def independent_certificate_check(raw: dict[str, Any]) -> bool:
    formulas = [parse_formula(value) for value in raw["formulas"]]
    links = raw["links"]
    conclusions = raw["conclusions"]
    size = len(formulas)

    if size == 0 or not conclusions:
        return False
    if any(not isinstance(vertex, int) or not 0 <= vertex < size for vertex in conclusions):
        return False
    if len(set(conclusions)) != len(conclusions):
        return False

    axiom_count = [0] * size
    producer_count = [0] * size
    parent_count = [0] * size
    fixed_edges: list[tuple[int, int]] = []
    par_choices: list[tuple[tuple[int, int], tuple[int, int]]] = []

    for link in links:
        tag = link.get("tag", link.get("kind"))
        if tag == "axiom":
            left, right = link["left"], link["right"]
            if not (0 <= left < size and 0 <= right < size and left != right):
                return False
            if formulas[left][0] != "atom" or formulas[right] != dual(formulas[left]):
                return False
            axiom_count[left] += 1
            axiom_count[right] += 1
            fixed_edges.append((left, right))
        elif tag in {"tensor", "par"}:
            left, right, conclusion = (
                link["left"],
                link["right"],
                link["conclusion"],
            )
            if not all(0 <= vertex < size for vertex in (left, right, conclusion)):
                return False
            if len({left, right, conclusion}) != 3:
                return False
            expected = (tag, formulas[left], formulas[right])
            if formulas[conclusion] != expected:
                return False
            producer_count[conclusion] += 1
            parent_count[left] += 1
            parent_count[right] += 1
            if tag == "tensor":
                fixed_edges.extend([(left, conclusion), (right, conclusion)])
            else:
                par_choices.append(
                    ((left, conclusion), (right, conclusion))
                )
        else:
            return False

    conclusion_set = set(conclusions)
    for vertex, formula in enumerate(formulas):
        if formula[0] == "atom":
            if axiom_count[vertex] != 1:
                return False
        elif producer_count[vertex] != 1:
            return False
        expected_parent_count = 0 if vertex in conclusion_set else 1
        if parent_count[vertex] != expected_parent_count:
            return False

    selections = itertools.product((0, 1), repeat=len(par_choices))
    for selection in selections:
        edges = fixed_edges + [
            par_choices[index][choice]
            for index, choice in enumerate(selection)
        ]
        if not union_find_tree(size, edges):
            return False
    return True


def audit_certificates() -> int:
    lines = run_lean("proofnet_ir_audit_certificates")
    if len(lines) < 1_000:
        raise AssertionError(f"expected at least 1000 certificate cases, got {len(lines)}")
    for line in lines:
        record = json.loads(line)
        case_id = record["id"]
        certificate = record["certificate"]
        expected = independent_certificate_check(certificate)
        actual = bool(certificate["accepted"])
        if actual != expected:
            raise AssertionError(
                f"certificate counterexample {case_id}: Lean={actual}, oracle={expected}"
            )
        if case_id.endswith(":valid") and not actual:
            raise AssertionError(f"generated valid certificate rejected: {case_id}")
        if not case_id.endswith(":valid") and actual:
            raise AssertionError(f"mutated certificate accepted: {case_id}")
    return len(lines)


def main() -> int:
    graph_cases = audit_graphs()
    certificate_cases = audit_certificates()
    print(
        "ProofNet-IR differential audit passed: "
        f"{graph_cases} exhaustive graphs, {certificate_cases} certificates"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
