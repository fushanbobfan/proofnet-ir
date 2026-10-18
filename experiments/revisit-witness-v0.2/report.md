# Splits revisits examined branch against branch (revisit-witness v0.2)

Tasks: 983.

| Count-preserving negatives | revisits | splits revisits | sampled | reorder | exclusion | alike | unresolved | rule order, both classes examined |
|---|---:|---:|---:|---:|---:|---:|---:|---|
| all | 156624 | 52228 | 1509 | 2 | 15 | 1492 | 0 | 7.8% to 100.0% |
| atoms-16:one-label:negative-count | 548 | 135 | 5 | 0 | 0 | 5 | 0 | 18.2% to 100.0% |
| atoms-16:two-label:negative-count | 201 | 38 | 2 | 0 | 0 | 2 | 0 | 17.4% to 100.0% |
| atoms-16:unique:negative-count | 60 | 17 | 17 | 2 | 15 | 0 | 0 | 73.3% to 75.0% |
| atoms-32:one-label:negative-count | 64596 | 19420 | 382 | 0 | 0 | 382 | 0 | 7.1% to 100.0% |
| atoms-32:two-label:negative-count | 88155 | 32139 | 628 | 0 | 0 | 628 | 0 | 7.6% to 100.0% |
| atoms-32:unique:negative-count | 3055 | 475 | 475 | 0 | 0 | 475 | 0 | 23.3% to 100.0% |
| atoms-8:one-label:negative-count | 1 | 1 | 0 | 0 | 0 | 0 | 0 | n/a |
| atoms-8:two-label:negative-count | 8 | 3 | 0 | 0 | 0 | 0 | 0 | n/a |
| atoms-8:unique:negative-count | 0 | 0 | 0 | 0 | 0 | 0 | 0 | n/a |

## Hypotheses

- H125 (holds): on the count-preserving negatives with unique labels (all sizes pooled), at least one sampled splits revisit has a reordering witness. {"reorder": 2, "sampled": 492}
- H126 (holds): on the count-preserving negatives with unique labels (all sizes pooled), at least half of the sampled splits revisits whose branches can be compared (a witness other than alike) have an exclusion witness. {"exclusionShareOfComparable": 0.8823529411764706, "sampledByWitness": {"reorder": 2, "exclusion": 15, "alike": 475, "unresolved": 0}, "interval": [0.6923076923076923, 1.0]}

## Checks

- C55 (holds): the search reproduces focused-revisits-v0.1's outcome and eight counters, and revisit-provenance-v0.1's six class counts, on every task.
- C56 (holds): every branch of every sampled splits revisit, rebuilt from the input sequent rule by rule, reaches the revisited query.
- C57 (holds): on the review's constructed sequent, outside the corpus, the search records two permutation, one splits and three tensors revisits, all in the sequent table, and the splits revisit has a reordering witness.
