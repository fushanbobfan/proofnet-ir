#!/usr/bin/env python3
"""An exhaustive prover for unit-free, cut-free MLL, written independently of the library's searches.

It decides `⊢ Γ` in the plain one-sided sequent calculus (axiom, tensor with every split of its context, par), with
three facts any textbook proof gives and nothing else:

- par is invertible, so pars are decomposed first, in any order;
- every cut-free derivation has one more axiom than tensors, so a provable sequent has 2t + 2 = a for t tensors and a
  atom occurrences;
- every axiom links an atom with its dual, so a provable sequent has, for every atom name, as many positive as
  negative occurrences.

A sequent of atoms alone is provable exactly when it is one atom and its dual. Otherwise the search tries every
distinct tensor as the last rule and every split of the remaining formulas (as multisets: alike formulas are
interchangeable) whose two premises meet the two counting conditions, and memoizes sequents as sorted multisets of
formula keys. It shares no code with focusedStrict or the net searches: formulas are its own tuples, splits are
enumerated by a dynamic program over the counting vectors, and no focusing discipline is used, so its refutations
certify unprovability independently of them.
"""

from __future__ import annotations

import sys
import time
from typing import Any

Formula = tuple  # ("atom", name, positive) | ("tensor", A, B) | ("par", A, B)


def parse(value: dict[str, Any]) -> Formula:
    kind = value["kind"]
    if kind == "atom":
        return ("atom", value["name"], bool(value["positive"]))
    if kind in ("tensor", "par"):
        return (kind, parse(value["left"]), parse(value["right"]))
    raise ValueError(f"unknown formula kind {kind}")


def flatten_pars(formulas: list[Formula]) -> list[Formula]:
    out: list[Formula] = []
    stack = list(formulas)
    while stack:
        f = stack.pop()
        if f[0] == "par":
            stack.append(f[1])
            stack.append(f[2])
        else:
            out.append(f)
    return out


class Prover:
    def __init__(self, names: list[str], node_limit: int | None = None, deadline: float | None = None) -> None:
        self.names = sorted(set(names))
        self.index = {n: i for i, n in enumerate(self.names)}
        self.width = len(self.names) + 1  # per-name balance, then atoms minus twice the tensors
        self.calls = 0
        self.node_limit = node_limit
        self.deadline = deadline
        self.memo: dict[tuple[Formula, ...], bool] = {}
        self.vectors: dict[Formula, tuple[int, ...]] = {}

    def vector(self, f: Formula) -> tuple[int, ...]:
        """The counting vector of a formula: per name, positive minus negative occurrences; last, atom occurrences
        minus twice the tensors."""
        cached = self.vectors.get(f)
        if cached is not None:
            return cached
        v = [0] * self.width
        stack = [f]
        while stack:
            g = stack.pop()
            if g[0] == "atom":
                v[self.index[g[1]]] += 1 if g[2] else -1
                v[-1] += 1
            else:
                if g[0] == "tensor":
                    v[-1] -= 2
                stack.append(g[1])
                stack.append(g[2])
        out = tuple(v)
        self.vectors[f] = out
        return out

    def feasible(self, formulas: list[Formula]) -> bool:
        """Both counting conditions: every name balanced, and atoms minus twice the tensors equal to two."""
        total = [0] * self.width
        for f in formulas:
            for i, x in enumerate(self.vector(f)):
                total[i] += x
        return all(x == 0 for x in total[:-1]) and total[-1] == 2

    def prove(self, formulas: list[Formula]) -> bool:
        sequent = tuple(sorted(flatten_pars(formulas), key=repr))
        cached = self.memo.get(sequent)
        if cached is not None:
            return cached
        self.calls += 1
        if self.node_limit is not None and self.calls > self.node_limit:
            raise TimeoutError("node limit")
        if self.deadline is not None and self.calls % 256 == 0 and time.monotonic() > self.deadline:
            raise TimeoutError("wall clock")
        result = self._prove(list(sequent))
        self.memo[sequent] = result
        return result

    def _prove(self, sequent: list[Formula]) -> bool:
        if not self.feasible(sequent):
            return False
        if all(f[0] == "atom" for f in sequent):
            return (len(sequent) == 2 and sequent[0][1] == sequent[1][1] and sequent[0][2] != sequent[1][2])
        tried: set[Formula] = set()
        for i, f in enumerate(sequent):
            if f[0] != "tensor" or f in tried:
                continue
            tried.add(f)
            rest = sequent[:i] + sequent[i + 1:]
            for left, right in self.splits(rest, f[1], f[2]):
                if self.prove([f[1]] + left) and self.prove([f[2]] + right):
                    return True
        return False

    def splits(self, rest: list[Formula], a: Formula, b: Formula):
        """Every split of `rest` as multisets (left, right) whose premises ⊢ a, left and ⊢ b, right both meet the
        counting conditions, enumerated over the groups of alike formulas with a reachability table on the left
        premise's counting vector."""
        groups: list[tuple[Formula, int]] = []
        for f in sorted(rest, key=repr):
            if groups and groups[-1][0] == f:
                groups[-1] = (f, groups[-1][1] + 1)
            else:
                groups.append((f, 1))
        target = [0] * self.width
        target[-1] = 2
        start = list(self.vector(a))
        # reachable[g] = the left-premise vectors reachable by choosing counts for groups g.., as a set
        reachable: list[set[tuple[int, ...]]] = [set() for _ in range(len(groups) + 1)]
        reachable[len(groups)] = {tuple(0 for _ in range(self.width))}
        for g in range(len(groups) - 1, -1, -1):
            f, m = groups[g]
            v = self.vector(f)
            here: set[tuple[int, ...]] = set()
            for tail in reachable[g + 1]:
                for c in range(m + 1):
                    here.add(tuple(t + c * x for t, x in zip(tail, v)))
            reachable[g] = here
        need = tuple(t - s for t, s in zip(target, start))
        if need not in reachable[0]:
            return

        def walk(g: int, chosen: list[int], remaining: tuple[int, ...]):
            if g == len(groups):
                if all(x == 0 for x in remaining):
                    left = [f for (f, _), c in zip(groups, chosen) for _ in range(c)]
                    right = [f for (f, m), c in zip(groups, chosen) for _ in range(m - c)]
                    if self.feasible([b] + right):
                        yield left, right
                return
            f, m = groups[g]
            v = self.vector(f)
            for c in range(m + 1):
                after = tuple(r - c * x for r, x in zip(remaining, v))
                if after in reachable[g + 1]:
                    yield from walk(g + 1, chosen + [c], after)

        yield from walk(0, [], need)


def decide(sequent_json: list[dict[str, Any]], node_limit: int | None = None,
           seconds: float | None = None) -> dict[str, Any]:
    """Provability of the sequent (None if a limit was reached), with the number of distinct sequents examined."""
    formulas = [parse(v) for v in sequent_json]
    names: list[str] = []
    stack = list(formulas)
    while stack:
        f = stack.pop()
        if f[0] == "atom":
            names.append(f[1])
        else:
            stack.extend([f[1], f[2]])
    prover = Prover(names, node_limit, None if seconds is None else time.monotonic() + seconds)
    sys.setrecursionlimit(100000)
    try:
        provable = prover.prove(formulas)
    except TimeoutError:
        return {"provable": None, "calls": prover.calls}
    return {"provable": provable, "calls": prover.calls}
