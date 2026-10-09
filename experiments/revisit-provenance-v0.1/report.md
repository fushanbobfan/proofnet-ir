# revisit-provenance-v0.1

Tasks: 983. Wrong answers: 0.

| Stratum | tasks | decided | revisits | permutation | splits | tensors | permutation of queries |
|---|---:|---:|---:|---:|---:|---:|---:|
| atoms-16:one-label:negative-count | 40 | 40 | 548 | 18.2% | 24.6% | 57.1% | 6.0% |
| atoms-16:one-label:negative-flip | 40 | 40 | 0 | n/a | n/a | n/a | 0.0% |
| atoms-16:one-label:positive | 40 | 40 | 167 | 8.4% | 31.1% | 60.5% | 1.7% |
| atoms-16:two-label:negative-count | 40 | 40 | 201 | 17.4% | 18.9% | 63.7% | 3.2% |
| atoms-16:two-label:negative-flip | 40 | 40 | 0 | n/a | n/a | n/a | 0.0% |
| atoms-16:two-label:positive | 40 | 40 | 145 | 11.0% | 16.6% | 72.4% | 1.6% |
| atoms-16:unique:negative-count | 40 | 40 | 60 | 28.3% | 28.3% | 43.3% | 1.8% |
| atoms-16:unique:negative-flip | 40 | 40 | 0 | n/a | n/a | n/a | 0.0% |
| atoms-16:unique:positive | 40 | 40 | 1 | 0.0% | 0.0% | 100.0% | 0.0% |
| atoms-32:one-label:negative-count | 30 | 30 | 64596 | 7.1% | 30.1% | 62.9% | 5.6% |
| atoms-32:one-label:positive | 40 | 40 | 826 | 5.9% | 29.2% | 64.9% | 2.1% |
| atoms-32:two-label:negative-count | 40 | 40 | 88155 | 7.6% | 36.5% | 55.9% | 5.4% |
| atoms-32:two-label:positive | 40 | 40 | 2123 | 4.9% | 27.7% | 67.4% | 2.0% |
| atoms-32:unique:negative-count | 40 | 40 | 3055 | 23.3% | 15.5% | 61.1% | 6.4% |
| atoms-32:unique:negative-flip | 40 | 40 | 0 | n/a | n/a | n/a | 0.0% |
| atoms-32:unique:positive | 40 | 40 | 112 | 2.7% | 11.6% | 85.7% | 0.2% |
| atoms-8:one-label:negative-count | 33 | 33 | 1 | 0.0% | 100.0% | 0.0% | 0.0% |
| atoms-8:one-label:negative-flip | 40 | 40 | 0 | n/a | n/a | n/a | 0.0% |
| atoms-8:one-label:positive | 40 | 40 | 46 | 0.0% | 39.1% | 60.9% | 0.0% |
| atoms-8:two-label:negative-count | 40 | 40 | 8 | 0.0% | 37.5% | 62.5% | 0.0% |
| atoms-8:two-label:negative-flip | 40 | 40 | 0 | n/a | n/a | n/a | 0.0% |
| atoms-8:two-label:positive | 40 | 40 | 13 | 0.0% | 7.7% | 92.3% | 0.0% |
| atoms-8:unique:negative-count | 40 | 40 | 0 | n/a | n/a | n/a | 0.0% |
| atoms-8:unique:negative-flip | 40 | 40 | 0 | n/a | n/a | n/a | 0.0% |
| atoms-8:unique:positive | 40 | 40 | 0 | n/a | n/a | n/a | 0.0% |

## Hypotheses

- H94 (fails): over the count-preserving negatives, at least half of the revisits are permutations (pooled share of permutation revisits among all revisits >= 0.5). {"permutationShare": 0.07755516395954642, "interval": [0.06934313618191065, 0.08717511297743732], "tasks": 343}
- H95 (fails): on the 32-atom count-preserving negatives with unique labels, where no two formulas are alike, at least half of the revisits are permutations. {"permutationShare": 0.23306055646481177, "tasks": 40}
- H96 (holds): on the 32-atom count-preserving negatives, the pooled share of permutations among revisits is lower with one label than with unique labels. {"oneLabel": 0.07062356802278778, "uniqueLabels": 0.23306055646481177, "tasks": {"one-label": 30, "unique": 40}}

## Checks

- C35 (holds): the search reproduces focused-revisits-v0.1's strictMemo on every task: the same outcome and the same eight counters (proveCalls, focusCalls, cacheHits, proveHits, focusHits, decides, splits, infeasible).
- C36 (holds): on every task the three classes add up to the hits of each table.
