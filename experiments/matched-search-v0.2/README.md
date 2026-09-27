# Equal-information matched search v0.2

matched-search-v0.1 left two questions open. Its net search enumerated linkings without pruning, while its
sequent search pruned states, so the reversal it found (nets win where unique labels force the linking and
lose where labels repeat) could belong to those implementations. And its negatives were connective flips
admitted only when the net arm refuted them within 20 seconds, so large repeated-label negatives, which the
net arm could not refute, were missing. This experiment prunes both searches and adds negatives certified
without the net arms.

## Arms

All five receive only the sequent, with five seconds of wall clock per arm per task:

- `focused`, `focusedBalanced`, `nets`: matched-search-v0.1's arms, unchanged (`proofnet_ir_matched_search`);
- `focusedStrict`: Andreoli-focused search. Pars are decomposed eagerly; a positive formula stays in focus
  through its tensors; a positive atom in focus closes only against exactly its dual; every branch must be
  balanced per name and satisfy `2 * tensors + 2 = atoms`, and the context splits of a tensor are enumerated
  as multisets under both conditions;
- `netsPruned`: linking search that refutes an unbalanced sequent or one with the wrong tensor count at once,
  checks every partial net by Danos's contraction (a par whose premises share a node merges with it; an axiom
  or par that closes a cycle in some switching abandons the branch), links the atom with the fewest partners
  outside its node first, and decides each complete linking by `Certificate.unificationCheck`.

Both new arms are in `ProofNetIRPrunedSearch.lean` (`proofnet_ir_pruned_search`).

## Corpus

matched-search-v0.1's 360 positives and 280 connective-flip negatives, and one count-preserving negative per
positive: the first unprovable candidate among the exchanges of one tensor with one par, then up to 1,000
seeded shuffles of the positive's atom occurrences. Both keep the atoms and the connective counts. A
candidate's unprovability is certified by a countermodel in a Lukasiewicz chain {0..m}, m = 1 to 4 (MLL is
sound for MV-algebras; m = 1 is the classical case), or else by `focusedStrict` refuting it within 60
seconds. 343 negatives: 90 certified by a countermodel and 253 by search, no candidate timed out, and 17
one-label positives (7 of 8 atoms, 10 of 32) had no unprovable candidate. 983 tasks.

## Artifacts

- `corpus.jsonl`, `preregistration.json`: the tasks with their mutations and certificates, the arms, the
  budget, hypotheses (registered as H7 to H10), and checks C15 to C17, committed before the run;
- `amendment-1.json`: the hypotheses relabelled H68 to H71, because H7 to H10 were already in use in the
  program's single numbering; made before any result was read;
- `results.jsonl`, `summary.json`, `report.md`: per task and arm the outcome, correctness, elapsed time, and
  the arm's counters; the stratum table and the decisions.

## Reproduction

```text
python scripts/run_pruned_search.py --check-committed
```

verifies the hashes, labels, and countermodels and reruns the 536 tasks on which every arm finished within
200 ms; CI runs it. `--run` repeats the whole run, about seventy minutes, on a machine shared with other
experiments as this one was.

## Outcome

No arm gave a wrong answer, and all four hypotheses hold.

- **H68**: pruning helps the linking search everywhere. It decides at least as many tasks as `nets` in every
  stratum and finds 18 of the 40 two-label and 21 of the 40 one-label 32-atom positives, against 2 and 0
  (one-sided sign tests, p = 1.5e-5 and 4.8e-7). On 16-atom one-label positives its median falls from 297 ms
  to 0.8 ms.
- **H69**: strict focusing decides every one of the 983 tasks, the slowest in 143 ms, and so at least as many
  as `focusedBalanced` in every stratum.
- **H70**: label repetition still reverses the ranking with both searches pruned: `focusedStrict` proves all
  40 one-label 32-atom positives (median 0.36 ms), `netsPruned` 21 (p = 1.9e-6).
- **H71**: `netsPruned` refutes none of the 30 one-label 32-atom count-preserving negatives, nor any of the
  40 two-label ones.

Every connective-flip negative violates the tensor count (C15), so both pruned arms refute all 280 at their
root checks, in well under a millisecond: v0.1's negatives did not test search. Where labels are unique the
linking is forced and the net search is the faster refuter (32-atom count-preserving negatives: 0.19 ms
median against 12.6 ms), but not the faster prover (32-atom positives: 2.45 ms against 1.06 ms).

`focusedStrict` certified 253 of the count-preserving negatives, so its refutations of those are not an
independent measurement. On the 90 certified by a countermodel it refutes all; `netsPruned` refutes 87, missing
3 of the 4 at 32 atoms, and `focusedBalanced` 88.

## Interpretation boundary

Unit-free, cut-free MLL sequents from one generator, under one wall-clock budget on a machine shared with
other experiments. The comparison is between these implementations of the two families; a net search with
stronger incremental constraints might close part of the gap. Nothing here concerns proof assistants at the
scale of Lean or Mathlib.
