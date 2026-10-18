#!/usr/bin/env python3
"""The review's constructed sequent: a splits revisit with a reordering witness, classed by revisit-witness-v0.1's code."""

from __future__ import annotations

import json
import unittest
from collections import Counter

import run_revisit_witness as rw
import run_revisit_witness_v2 as rw2


class ConstructedSplitsRevisit(unittest.TestCase):
    def setUp(self) -> None:
        self.record = json.loads(rw2.CONSTRUCTED.read_text(encoding="utf-8"))
        self.memo = self.record["strictMemo"]
        self.task = {"sequent": self.record["sequent"]}
        self.keys = self.memo["keys"]
        self.multiplicity = Counter(k for f in self.task["sequent"] for k in rw.subformula_keys(f))

    def test_classes(self) -> None:
        self.assertEqual(tuple(self.memo[k] for k in rw.CLASS_FIELDS), (2, 1, 3, 0, 0, 0))
        self.assertEqual(len(self.memo["samples"]), 1)

    def test_splits_class(self) -> None:
        sample = self.memo["samples"][0]
        tensors = sorted(step[0] for step in sample["current"])
        earlier = [sorted(step[0] for step in branch) for branch in sample["earlier"]]
        self.assertIn(tensors, earlier)  # some earlier branch decomposed the same tensors
        self.assertTrue(any(e != tensors for e in earlier))  # and another decomposed other tensors

    def test_witnesses(self) -> None:
        sample = self.memo["samples"][0]
        self.assertTrue(rw.rebuilds(sample, self.task, self.keys))
        verdicts = sorted(rw.compare(sample, sample["current"], b, self.task, self.keys, self.multiplicity)
                          for b in sample["earlier"])
        self.assertEqual(verdicts, ["exclusion", "reorder"])
        self.assertEqual(rw.classify(sample, self.task, self.keys, self.multiplicity), "reorder")
        self.assertTrue(rw2.constructed_holds(self.record))


if __name__ == "__main__":
    unittest.main(verbosity=2)
