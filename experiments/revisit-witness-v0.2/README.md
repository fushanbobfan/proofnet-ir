# Revisit witness v0.2

revisit-provenance-v0.1 put a revisit in the splits class when no earlier branch to its query applied the same rules
with the same splits and some earlier branch decomposed the same tensors, and read the class as excluding rule order;
with the tensors class examined by revisit-witness-v0.1, rule order then accounted for between 7.8% and 66.7% of the
count-preserving negatives' revisits. A query can have several earlier branches, and the class speaks for one of them.
On a sequent constructed outside the corpus in a review of the paper (2026-10-18),
(c⁻ ⊗ d⁻), (a⁻ ⊗ b⁻), (c⁺ ⊗ b⁺), a⁺, d⁺, (z⁺ ⊗ z⁻), the one splits revisit has a reordering witness against one
earlier branch and an exclusion witness against the other. This experiment runs revisit-witness-v0.1's search with its
control flow unchanged (`ProofNetIRRevisitWitnessSplits.lean`) and writes out the splits revisits of every
count-preserving negative with unique labels and 2% of those with repeated labels, each classed by revisit-witness-v0.1's
own code (reorder, exclusion, alike, unresolved). With both classes that are not permutations examined, the
identification interval for rule order runs from (permutations + tensors revisits × their reorder share + splits
revisits × their reorder share) / revisits to (revisits − tensors revisits × their exclusion share − splits revisits ×
their exclusion share) / revisits, the tensors revisits' shares taken from revisit-witness-v0.1 over the same tasks.

## Artifacts

- `preregistration.json`: the question, the sample rule and rates, hypotheses H125 and H126, checks C55 to C57, the
  corpus and the compared results by hash, implementation hashes (this search, revisit-witness-v0.1's classification
  code, the runner), registered before any run on the corpus;
- `constructed.json`: the constructed sequent's run, the regression case;
- `results.jsonl.gz`: per task, the outcome, the counters and classes, and each sampled splits revisit with its
  branches and witness class;
- `summary.json`, `report.md`: the witness shares and the identification interval by stratum; the hypotheses and
  checks.

## Reproduction

```text
python scripts/test_revisit_witness_v2.py
python scripts/run_revisit_witness_v2.py --check-committed
```

class the constructed sequent's splits revisit, and verify the hashes and the summary, rerun every task that finished
within 200 ms, and rerun the constructed sequent; CI runs both.

## Outcome

The search reproduces focused-revisits-v0.1's outcomes and counters and revisit-provenance-v0.1's class counts on all
983 tasks (C55), every branch of all 1,509 sampled splits revisits rebuilds to its query (C56), and the constructed
sequent gives two permutation, one splits and three tensors revisits, the splits revisit with a reordering witness
(C57).

- **H125 holds**: 2 of the 492 sampled splits revisits with unique labels have a reordering witness, both on 16-atom
  negatives.
- **H126 holds**: of the 17 whose branches can be compared, 15 have an exclusion witness (88.2%, bootstrap interval
  69.2% to 100%); the other 475, all at 32 atoms, are alike.

| Count-preserving negatives | revisits | splits revisits | sampled | reorder | exclusion | alike | rule order |
|---|---:|---:|---:|---:|---:|---:|---|
| all 343 | 156,624 | 52,228 | 1,509 | 2 | 15 | 1,492 | 7.8% to 100% |
| 16 atoms, unique labels | 60 | 17 | 17 | 2 | 15 | 0 | 73.3% to 75.0% |
| 32 atoms, unique labels | 3,055 | 475 | 475 | 0 | 0 | 475 | 23.3% to 100% |
| 32 atoms, two labels | 88,155 | 32,139 | 628 | 0 | 0 | 628 | 7.6% to 100% |
| 32 atoms, one label | 64,596 | 19,420 | 382 | 0 | 0 | 382 | 7.1% to 100% |

The last column is the interval with both classes examined. Where every formula is distinct (16 atoms, unique labels),
the stratum's 60 revisits are 17 permutations, 17 splits revisits (2 reorderings, 15 exclusions) and 26 tensors
revisits (25 reorderings, 1 unresolved), so rule order accounts for 73.3% to 75.0% of them; read as exclusions, the
splits revisits had given 70.0% to 71.7%.

## Interpretation boundary

Where the branches can be compared, most splits revisits contradict every earlier branch, but two of seventeen are
reorderings, so the class cannot be read as excluding rule order. Over the corpus, alike formulas at 32 atoms leave
both classes uncompared, and the share of revisits that rule order accounts for lies between 7.8%, the permutations,
and 100%: these measurements give it no upper limit. The upper limit of 66.7% in revisit-provenance-v0.1 and
revisit-witness-v0.1 rests on the reading this experiment tests and does not hold.
