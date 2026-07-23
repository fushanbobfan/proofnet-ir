#!/usr/bin/env python3
"""Focused cut-free proof-search baseline for one-sided unit-free MLL.

The invertible phase eagerly decomposes every par. The focused phase chooses a
tensor and enumerates all linear-resource partitions. Exchange is implicit by
canonical multiset ordering. This baseline is intentionally small and
independent of the proof-net checker.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any


Formula = tuple[Any, ...]


def parse_formula(value: dict[str, Any]) -> Formula:
    kind = value["kind"]
    if kind == "atom":
        return ("atom", value["name"], bool(value["positive"]))
    if kind in {"tensor", "par"}:
        return (kind, parse_formula(value["left"]), parse_formula(value["right"]))
    raise ValueError(f"unknown formula kind: {kind!r}")


def formula_json(formula: Formula) -> dict[str, Any]:
    if formula[0] == "atom":
        return {"kind": "atom", "name": formula[1], "positive": formula[2]}
    return {
        "kind": formula[0],
        "left": formula_json(formula[1]),
        "right": formula_json(formula[2]),
    }


def dual(formula: Formula) -> Formula:
    if formula[0] == "atom":
        return ("atom", formula[1], not formula[2])
    if formula[0] == "tensor":
        return ("par", dual(formula[1]), dual(formula[2]))
    return ("tensor", dual(formula[1]), dual(formula[2]))


def formula_key(formula: Formula) -> str:
    return json.dumps(formula_json(formula), sort_keys=True, separators=(",", ":"))


def canonical_sequent(sequent: list[Formula]) -> tuple[Formula, ...]:
    return tuple(sorted(sequent, key=formula_key))


@dataclass
class Stats:
    calls: int = 0
    cache_hits: int = 0
    par_steps: int = 0
    tensor_choices: int = 0
    partitions: int = 0


class SearchLimitExceeded(RuntimeError):
    pass


class FocusedSearch:
    def __init__(
        self, max_calls: int = 1_000_000, max_partitions: int = 1_000_000
    ) -> None:
        self.max_calls = max_calls
        self.max_partitions = max_partitions
        self.stats = Stats()
        self.memo: dict[tuple[Formula, ...], dict[str, Any] | None] = {}

    def search(self, sequent: list[Formula]) -> dict[str, Any] | None:
        state = canonical_sequent(sequent)
        if state in self.memo:
            self.stats.cache_hits += 1
            return self.memo[state]
        self.stats.calls += 1
        if self.stats.calls > self.max_calls:
            raise SearchLimitExceeded(f"search exceeded {self.max_calls} states")

        # Invertible phase: eagerly decompose the first par in canonical order.
        for index, formula in enumerate(state):
            if formula[0] == "par":
                self.stats.par_steps += 1
                expanded = list(state[:index]) + [formula[1], formula[2]] + list(
                    state[index + 1 :]
                )
                premise = self.search(expanded)
                result = None if premise is None else {
                    "rule": "par",
                    "formula": formula_json(formula),
                    "premise": premise,
                }
                self.memo[state] = result
                return result

        if len(state) == 2 and state[0][0] == "atom" and state[1] == dual(state[0]):
            result = {
                "rule": "axiom",
                "left": formula_json(state[0]),
                "right": formula_json(state[1]),
            }
            self.memo[state] = result
            return result

        # Focused phase: choose a tensor and enumerate every resource split.
        for tensor_index, formula in enumerate(state):
            if formula[0] != "tensor":
                continue
            self.stats.tensor_choices += 1
            context = list(state[:tensor_index] + state[tensor_index + 1 :])
            for mask in range(1 << len(context)):
                self.stats.partitions += 1
                if self.stats.partitions > self.max_partitions:
                    raise SearchLimitExceeded(
                        f"search exceeded {self.max_partitions} resource partitions"
                    )
                left_context = [
                    value for index, value in enumerate(context) if (mask >> index) & 1
                ]
                right_context = [
                    value for index, value in enumerate(context) if not (mask >> index) & 1
                ]
                left_proof = self.search([formula[1], *left_context])
                if left_proof is None:
                    continue
                right_proof = self.search([formula[2], *right_context])
                if right_proof is None:
                    continue
                result = {
                    "rule": "tensor",
                    "formula": formula_json(formula),
                    "left": left_proof,
                    "right": right_proof,
                }
                self.memo[state] = result
                return result

        self.memo[state] = None
        return None


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("--max-calls", type=int, default=1_000_000)
    parser.add_argument("--max-partitions", type=int, default=1_000_000)
    parser.add_argument("--require-found", action="store_true")
    args = parser.parse_args()

    raw = json.loads(args.input.read_text(encoding="utf-8"))
    sequent = [parse_formula(value) for value in raw["sequent"]]
    engine = FocusedSearch(
        max_calls=args.max_calls, max_partitions=args.max_partitions
    )
    proof = engine.search(sequent)
    output = {
        "found": proof is not None,
        "proof": proof,
        "stats": vars(engine.stats),
    }
    print(json.dumps(output, sort_keys=True, separators=(",", ":")))
    if args.require_found and proof is None:
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
