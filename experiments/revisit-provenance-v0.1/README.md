# Revisit provenance v0.1

focused-revisits-v0.1 found that 70.6% of the strictly focused search's queries on the count-preserving negatives are
revisits, queries answered from a memo table. A revisit shows that a query recurred, not why. This experiment runs
the same search, with its control flow unchanged, and gives every query its *branch*: the tensor rules applied on the
way to it, each with the premise it enters and the multiset of formulas it sends to the other premise. Each revisit is
classed against the branches that met the same query before:

- **permutation**: an earlier branch applied the same rules, with the same splits, in another order: the reordering
  of commuting foci, which proof nets and maximal multi-focusing remove;
- **splits**: no earlier branch applied the same rules, but one decomposed the same tensors, with some context split
  differently;
- **tensors**: every earlier branch decomposed a different multiset of tensors.

## Artifacts

- `preregistration.json`: question, definitions, hypotheses H94 to H96, checks C35 and C36, the corpus and the
  compared results by hash, implementation hashes (`ProofNetIRRevisitProvenance.lean`,
  `scripts/run_revisit_provenance.py`), registered before any run on the corpus;
- `results.jsonl`: per task, the outcome, the counters of focused-revisits-v0.1, and the classes of the revisits in
  each table;
- `summary.json`, `report.md`: pooled shares by kind, stratum, size, and table; hypotheses and checks.

## Reproduction

```text
python scripts/run_revisit_provenance.py --check-committed
```

verifies the hashes and the summary and reruns every task that finished within 200 ms; CI runs it.

## Outcome

The search reproduces focused-revisits-v0.1's outcome and eight counters on all 983 tasks (C35), and the classes add
up on every task (C36).

| Count-preserving negatives | revisits | permutation | splits | tensors | permutation of all queries |
|---|---:|---:|---:|---:|---:|
| all 343 | 156,624 | 7.8% | 33.3% | 58.9% | 5.5% |
| 32 atoms, unique labels | 3,055 | 23.3% | 15.5% | 61.1% | 6.4% |
| 32 atoms, two labels | 88,155 | 7.6% | 36.5% | 55.9% | 5.4% |
| 32 atoms, one label | 64,596 | 7.1% | 30.1% | 62.9% | 5.6% |

- **H94 fails**: 7.8% of the count-preserving negatives' revisits are permutations (bootstrap interval 6.9% to 8.7%),
  against a registered threshold of half.
- **H95 fails**: with unique labels at 32 atoms, where no two formulas are alike, 23.3%.
- **H96 holds**: at 32 atoms the share is lower with one label (7.1%) than with unique labels (23.3%).

By table, permutations are 12.5% of the sequent table's revisits and 0.5% of the focus table's: a reordering met
again is usually caught at the sequent it reaches first. Positives meet few revisits (3,433), 5.4% of them
permutations. Flipped negatives fail the edge-count condition at the root and meet none.

## Interpretation boundary

The classes describe the branch of each revisit. A splits revisit decomposes the same tensors as an earlier branch but
routes some formula to a different premise, which yields a different linking, so no quotient by rule order removes it:
at least a third of the revisits are not rule-order redundancy. A permutation revisit is rule-order redundancy. A
tensors revisit can be either: reordering two foci also re-creates the subproblems of the premises the first rule
sends material to, and the branches to those subproblems differ in the tensors they decomposed (one decomposed the
other focus before sending its parts away, the other sent it whole), as do the branches of attempts that are not
reorderings. So rule order accounts for at least 7.8% and at most 66.7% of the revisits, and the 70.6% revisit share
is not a measure of the redundancy that proof nets remove: at least a third of it comes from different splits, and
reorderings along a revisit's own branch account for 7.8%.
Formulas are compared by their keys, as the memo tables compare them, so with repeated labels alike formulas are not
told apart.
