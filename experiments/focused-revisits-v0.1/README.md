# Focused revisits v0.1

Strict focusing leaves more than one cut-free derivation per proof net on most of redundancy-v0.1's tasks: two foci
that the net does not order can be taken in either order. That is redundancy in the space of proofs. This
experiment asks how much of it the strictly focused search of matched-search-v0.2 actually meets, and what merging
it buys. A search meets it when it reaches a query it has already met along another sequence of foci and splits.

## Arms

Both run `focusedStrict` of `ProofNetIRPrunedSearch.lean`, copied unchanged into `ProofNetIRFocusedRevisits.lean`
(`proofnet_ir_focused_revisits`), on the sequent alone, with five seconds of wall clock per arm per task:

- `strictMemo`: with its two memo tables, for sequents and for a tensor in focus with its context, as in
  matched-search-v0.2; a query answered from a table is a revisit;
- `strictNoMemo`: with both tables neither consulted nor filled, so every revisit is explored again; a set of the
  queries met so far counts revisits without pruning anything.

A query is a call of `prove` (a sequent after eager par decomposition, as a sorted multiset of formulas) or of
`focus` on a tensor goal (the goal with its context).

## Corpus

matched-search-v0.2's 983 tasks, unchanged: 360 positives, 280 connective-flip negatives, and 343 count-preserving
negatives.

## Registration

`preregistration.json` was committed before the run. It fixes the corpus and matched-search-v0.2's results by hash,
the arms, the budget, the measures, four hypotheses, and two checks:

- **H83**: over the count-preserving negatives, at least half of `strictMemo`'s queries are revisits;
- **H84**: at 16 and at 32 atoms, `strictMemo`'s pooled revisit share is higher on the count-preserving negatives
  than on the positives;
- **H85**: `strictNoMemo` decides fewer of the 32-atom count-preserving negatives than `strictMemo`;
- **H86**: on the count-preserving negatives both arms decide, the median ratio of `strictNoMemo`'s explored queries
  to `strictMemo`'s exceeds 2;
- **C26**: `strictMemo` reproduces matched-search-v0.2's `focusedStrict` outcome and six counters on every task;
- **C27**: no arm gives a wrong answer.

matched-search-v0.2 recorded `focusedStrict`'s memo hits for every task; no quantity of this registration was
computed from them before it. The development run on matched-search-v0.2's development set, recorded in the
registration, checked the copy (C26 held there) and printed only decided, timeout, and median-time counts.

## Reproduction

```text
python scripts/run_focused_revisits.py --check-committed
```
