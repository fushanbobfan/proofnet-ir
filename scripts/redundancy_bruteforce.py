#!/usr/bin/env python3
"""Independent brute-force cross-check of the Lean redundancy counter.

Reads task lines (`id`, `sequent`) and prints one JSON line per task with the
same `dAll`, `dWeak`, `dFoc`, and `nets` fields as `proofnet_ir_redundancy_count`,
computed by explicit enumeration over frozen occurrence sets without balance
pruning, and with proof nets decided by the independent Python checker of
`audit_v010.py`. Intended for tasks with at most 16 atom occurrences.
"""

from __future__ import annotations

import itertools
import json
import math
import sys
from functools import lru_cache
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parent))
from audit_v010 import independent_certificate_check  # noqa: E402

ATOM, TENSOR, PAR = 0, 1, 2


def build_forest(sequent: list[dict[str, Any]]) -> tuple[list[dict[str, Any]], list[int]]:
    occurrences: list[dict[str, Any]] = []

    def add(formula: dict[str, Any]) -> int:
        index = len(occurrences)
        if formula["kind"] == "atom":
            occurrences.append({"kind": ATOM, "name": formula["name"],
                                "positive": bool(formula["positive"]), "formula": formula})
            return index
        occurrences.append({"kind": TENSOR if formula["kind"] == "tensor" else PAR,
                            "formula": formula})
        left = add(formula["left"])
        right = add(formula["right"])
        occurrences[index]["left"] = left
        occurrences[index]["right"] = right
        return index

    roots = [add(formula) for formula in sequent]
    return occurrences, roots


def count_task(sequent: list[dict[str, Any]]) -> dict[str, Any]:
    occurrences, roots = build_forest(sequent)

    def is_axiom(state: frozenset[int]) -> bool:
        if len(state) != 2:
            return False
        a, b = (occurrences[i] for i in state)
        return (a["kind"] == ATOM and b["kind"] == ATOM and a["name"] == b["name"]
                and a["positive"] != b["positive"])

    def splits(state: frozenset[int], tensor: int):
        context = sorted(state - {tensor})
        left, right = occurrences[tensor]["left"], occurrences[tensor]["right"]
        for size in range(len(context) + 1):
            for chosen in itertools.combinations(context, size):
                rest = [x for x in context if x not in chosen]
                yield frozenset(chosen) | {left}, frozenset(rest) | {right}

    @lru_cache(maxsize=None)
    def d_all(state: frozenset[int]) -> int:
        if is_axiom(state):
            return 1
        total = 0
        for occurrence in state:
            node = occurrences[occurrence]
            if node["kind"] == PAR:
                total += d_all((state - {occurrence}) | {node["left"], node["right"]})
            elif node["kind"] == TENSOR:
                for left_state, right_state in splits(state, occurrence):
                    left_count = d_all(left_state)
                    if left_count:
                        total += left_count * d_all(right_state)
        return total

    @lru_cache(maxsize=None)
    def d_weak(state: frozenset[int]) -> int:
        pars = [i for i in sorted(state) if occurrences[i]["kind"] == PAR]
        if pars:
            node = occurrences[pars[0]]
            return d_weak((state - {pars[0]}) | {node["left"], node["right"]})
        if is_axiom(state):
            return 1
        total = 0
        for occurrence in state:
            if occurrences[occurrence]["kind"] == TENSOR:
                for left_state, right_state in splits(state, occurrence):
                    left_count = d_weak(left_state)
                    if left_count:
                        total += left_count * d_weak(right_state)
        return total

    @lru_cache(maxsize=None)
    def d_foc(state: frozenset[int], focus: int | None) -> int:
        if focus is not None:
            node = occurrences[focus]
            total = 0
            for left_state, right_state in splits(state, focus):
                left_count = continue_on(left_state, node["left"])
                if left_count:
                    total += left_count * continue_on(right_state, node["right"])
            return total
        pars = [i for i in sorted(state) if occurrences[i]["kind"] == PAR]
        if pars:
            node = occurrences[pars[0]]
            return d_foc((state - {pars[0]}) | {node["left"], node["right"]}, None)
        if is_axiom(state):
            return 1
        return sum(d_foc(state, i) for i in state if occurrences[i]["kind"] == TENSOR)

    def continue_on(state: frozenset[int], sub: int) -> int:
        return d_foc(state, sub if occurrences[sub]["kind"] == TENSOR else None)

    root = frozenset(roots)
    all_count, weak_count, foc_count = d_all(root), d_weak(root), d_foc(root, None)

    names = sorted({o["name"] for o in occurrences if o["kind"] == ATOM})
    per_name = []
    linkings = 1
    for name in names:
        positives = [i for i, o in enumerate(occurrences)
                     if o["kind"] == ATOM and o["name"] == name and o["positive"]]
        negatives = [i for i, o in enumerate(occurrences)
                     if o["kind"] == ATOM and o["name"] == name and not o["positive"]]
        if len(positives) != len(negatives):
            linkings = 0
            break
        linkings *= math.factorial(len(positives))
        per_name.append([list(zip(positives, perm)) for perm in itertools.permutations(negatives)])
    nets = 0
    if linkings:
        connectives = [
            {"kind": "tensor" if o["kind"] == TENSOR else "par", "left": o["left"],
             "right": o["right"], "conclusion": i}
            for i, o in enumerate(occurrences) if o["kind"] != ATOM
        ]
        for combo in itertools.product(*per_name):
            axioms = [{"kind": "axiom", "left": p, "right": n} for pairs in combo for p, n in pairs]
            raw = {"formulas": [o["formula"] for o in occurrences],
                   "links": axioms + connectives, "conclusions": roots}
            if independent_certificate_check(raw):
                nets += 1
    return {"dAll": str(all_count), "dWeak": str(weak_count), "dFoc": str(foc_count),
            "linkings": str(linkings), "nets": str(nets)}


def main() -> int:
    for line in sys.stdin:
        line = line.strip()
        if not line:
            continue
        task = json.loads(line)
        result = {"id": task["id"], **count_task(task["sequent"])}
        print(json.dumps(result, separators=(",", ":")))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
