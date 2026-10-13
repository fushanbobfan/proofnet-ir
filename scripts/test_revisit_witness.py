#!/usr/bin/env python3
"""revisit-witness-v0.1's rebuild and classes on hand-made branches whose answer is known."""

from __future__ import annotations

import unittest
from collections import Counter

import run_revisit_witness as rw


def atom(name: str, positive: bool) -> dict:
    return {"kind": "atom", "name": name, "positive": positive}


def tensor(left: dict, right: dict) -> dict:
    return {"kind": "tensor", "left": left, "right": right}


A, B, C, D = (atom(n, True) for n in "abcd")
NA, NB, NC, ND = (atom(n, False) for n in "abcd")
T1, T2 = tensor(NA, NB), tensor(NC, ND)  # neither side a positive atom: each rule splits its context
SEQUENT = [T1, T2, A, B, C, D]
KEYS = [rw.key(f) for f in (T1, T2, A, B, C, D, NA, NB, NC, ND)]
ID = {k: i for i, k in enumerate(KEYS)}


def ids(*formulas: dict) -> list[int]:
    return [ID[rw.key(f)] for f in formulas]


def step(t: dict, side: int, *sent: dict) -> list:
    return [ID[rw.key(t)], side, ids(*sent)]


# T1 first, into its right premise (b-), sending a+; then T2 into its left premise (c-), sending b+, b-, d+.
FIRST_T1 = [step(T1, 1, A), step(T2, 0, B, NB, D)]
# T2 first, into its left premise, sending T1 whole with a+, b+, d+: the same query, T1 decomposed later elsewhere.
FIRST_T2 = [step(T2, 0, T1, A, B, D)]
# T1 first but into its left premise (a-), sending b+, d+; then T2 into its left premise, sending a+, a-.
T1_LEFT = [step(T1, 0, B, D), step(T2, 0, A, NA)]
QUERY = {"table": "prove", "query": ids(C, NC), "goal": None}


def record(current: list, *earlier: list, distinct: int | None = None) -> dict:
    return QUERY | {"rank": 0, "current": current, "earlier": list(earlier),
                    "distinctEarlier": len(earlier) if distinct is None else distinct}


def task(sequent: list) -> dict:
    return {"sequent": sequent}


UNIQUE = Counter(k for f in SEQUENT for k in rw.subformula_keys(f))


class RebuildTests(unittest.TestCase):
    def test_each_hand_made_branch_reaches_the_query(self):
        for branch in (FIRST_T1, FIRST_T2, T1_LEFT):
            self.assertTrue(rw.rebuilds(record(branch), task(SEQUENT), KEYS))

    def test_the_contexts_each_rule_splits(self):
        infos, frontier = rw.rebuild(SEQUENT, FIRST_T1, KEYS)
        self.assertEqual(infos[1]["context"], Counter({rw.key(B): 1, rw.key(NB): 1, rw.key(C): 1, rw.key(D): 1}))
        self.assertEqual(infos[1]["kept"], Counter({rw.key(C): 1}))
        self.assertEqual(frontier, ("prove", Counter({rw.key(C): 1, rw.key(NC): 1})))

    def test_a_rule_on_a_tensor_not_in_the_sequent_does_not_rebuild(self):
        broken = [step(T2, 0, T1, A, B, D), step(T1, 1, A)]  # T1 was sent away
        self.assertFalse(rw.rebuilds(record(broken), task(SEQUENT), KEYS))

    def test_a_split_that_sends_what_the_context_lacks_does_not_rebuild(self):
        self.assertFalse(rw.rebuilds(record([step(T2, 0, T1, A, B, D, NA)]), task(SEQUENT), KEYS))


class ClassTests(unittest.TestCase):
    def classify(self, rec: dict, multiplicity: Counter = UNIQUE, sequent: list = SEQUENT) -> str:
        return rw.classify(rec, task(sequent), KEYS, multiplicity)

    def test_two_tensors_decomposed_in_either_order_are_a_reordering(self):
        self.assertEqual(self.classify(record(FIRST_T2, FIRST_T1)), "reorder")
        self.assertEqual(self.classify(record(FIRST_T1, FIRST_T2)), "reorder")
        self.assertEqual(self.classify(record(T1_LEFT, FIRST_T2)), "reorder")

    def test_a_shared_tensor_entered_from_different_sides_is_an_exclusion(self):
        self.assertEqual(self.classify(record(T1_LEFT, FIRST_T1)), "exclusion")

    def test_an_exclusion_needs_every_earlier_branch(self):
        # the query was met by more distinct branches than were kept
        self.assertEqual(self.classify(record(T1_LEFT, FIRST_T1, distinct=5)), "unresolved")
        # and a reordering against any earlier branch wins
        self.assertEqual(self.classify(record(T1_LEFT, FIRST_T1, FIRST_T2)), "reorder")

    def test_repeated_formulas_are_alike(self):
        sequent = SEQUENT + [atom("c", True)]
        multiplicity = Counter(k for f in sequent for k in rw.subformula_keys(f))
        self.assertEqual(self.classify(record(FIRST_T2, FIRST_T1), multiplicity, sequent), "alike")

    def test_material_folded_into_a_tensor_leaves_with_it(self):
        infos, _ = rw.rebuild(SEQUENT, FIRST_T1, KEYS)
        exits = rw.exits(infos, {rw.key(T2)})
        self.assertEqual(exits[rw.key(T2)], Counter({rw.key(T1): 1, rw.key(A): 1, rw.key(B): 1, rw.key(D): 1}))

    def test_a_tensor_whose_parts_leave_at_two_rules_is_not_folded(self):
        e, f, g = atom("e", True), atom("f", True), atom("g", True)
        ne, nf, ng = atom("e", False), atom("f", False), atom("g", False)
        par = {"kind": "par", "left": NB, "right": ne}
        t1, t3 = tensor(NA, par), tensor(nf, ng)  # T1's right part is a par: released, it leaves b- and e-
        sequent = [t1, T2, t3, A, B, C, D, e, f, g]
        keys = sorted({k for x in sequent for k in rw.subformula_keys(x)} | {rw.key(x) for x in (NB, ne, nf, ng)})
        identify = {k: i for i, k in enumerate(keys)}

        def st(t, side, *sent):
            return [identify[rw.key(t)], side, [identify[rw.key(x)] for x in sent]]

        # T1 into its right premise; T3 sends e- away and keeps b-; T2 then sends b-: T1's parts leave at two rules
        branch = [st(t1, 1, A), st(t3, 0, ne, e, g), st(T2, 0, B, D, f, NB, nf)]
        infos, frontier = rw.rebuild(sequent, branch, keys)
        self.assertEqual(frontier, ("prove", Counter({rw.key(C): 1, rw.key(NC): 1})))
        self.assertIsNone(rw.exits(infos, {rw.key(T2), rw.key(t3)}))
        # with T3 not shared, it folds too, and T1's parts leave at T2 alone
        self.assertIsNotNone(rw.exits(infos, {rw.key(T2)}))


if __name__ == "__main__":
    unittest.main()
