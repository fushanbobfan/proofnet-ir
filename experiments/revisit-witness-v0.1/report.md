# revisit-witness-v0.1

Tasks: 983.

| Count-preserving negatives | tasks | tensors revisits | sampled | reorder | exclusion | alike | unresolved | rule order |
|---|---:|---:|---:|---:|---:|---:|---:|---|
| all | 343 | 92249 | 3643 | 0.0% | 0.0% | 100.0% | 0.0% | 7.8% to 66.7% |
| atoms-16:one-label:negative-count | 40 | 313 | 7 | 0.0% | 0.0% | 100.0% | 0.0% | 18.2% to 75.4% |
| atoms-16:two-label:negative-count | 40 | 128 | 1 | 0.0% | 0.0% | 100.0% | 0.0% | 17.4% to 81.1% |
| atoms-16:unique:negative-count | 40 | 26 | 26 | 96.2% | 0.0% | 0.0% | 3.8% | 70.0% to 71.7% |
| atoms-32:one-label:negative-count | 30 | 40614 | 784 | 0.0% | 0.0% | 100.0% | 0.0% | 7.1% to 69.9% |
| atoms-32:two-label:negative-count | 40 | 49295 | 956 | 0.0% | 0.0% | 100.0% | 0.0% | 7.6% to 63.5% |
| atoms-32:unique:negative-count | 40 | 1868 | 1868 | 0.0% | 0.0% | 100.0% | 0.0% | 23.3% to 84.5% |
| atoms-8:one-label:negative-count | 33 | 0 | 0 | n/a | n/a | n/a | n/a | n/a |
| atoms-8:two-label:negative-count | 40 | 5 | 1 | 0.0% | 0.0% | 100.0% | 0.0% | 0.0% to 62.5% |
| atoms-8:unique:negative-count | 40 | 0 | 0 | n/a | n/a | n/a | n/a | n/a |

## Hypotheses

- H119 (fails): on the count-preserving negatives with unique labels (all sizes pooled), at least half of the tensors revisits have a reordering witness. {"reorderShare": 0.013199577613516367, "sampled": 1894, "interval": [0.005484460694698354, 0.026248941574936496]}
- H120 (holds): on the count-preserving negatives with unique labels (all sizes pooled), fewer than one in ten tensors revisits has an exclusion witness. {"exclusionShare": 0.0, "sampled": 1894, "interval": [0.0, 0.0]}
- H121 (fails): on the 32-atom count-preserving negatives with unique labels, the identification interval for the share of revisits that rule order accounts for (permutations and reordering-witnessed tensors revisits at its low end; all revisits but splits and exclusion-witnessed tensors revisits at its high end) lies entirely on one side of one half. {"ruleOrderInterval": [0.23306055646481177, 0.8445171849427169], "tasks": 40}

## Checks

- C51 (holds): the search reproduces focused-revisits-v0.1's outcome and eight counters, and revisit-provenance-v0.1's six class counts, on every task.
- C52 (holds): every branch of every sampled revisit, rebuilt from the input sequent rule by rule, reaches the revisited query.
