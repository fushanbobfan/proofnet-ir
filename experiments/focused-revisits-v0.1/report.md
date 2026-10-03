# focused-revisits-v0.1

Tasks: 983. Wrong answers: {'strictMemo': 0, 'strictNoMemo': 0}.

| Stratum | tasks | memo decided | memo revisit share | no-memo decided | no-memo revisit share | median work ratio |
|---|---:|---:|---:|---:|---:|---:|
| atoms-16:one-label:negative-count | 40 | 40 | 32.6% | 40 | 66.7% | 1.81 |
| atoms-16:one-label:negative-flip | 40 | 40 | 0.0% | 40 | 0.0% | 1.00 |
| atoms-16:one-label:positive | 40 | 40 | 20.5% | 40 | 37.7% | 1.18 |
| atoms-16:two-label:negative-count | 40 | 40 | 18.2% | 40 | 41.3% | 1.26 |
| atoms-16:two-label:negative-flip | 40 | 40 | 0.0% | 40 | 0.0% | 1.00 |
| atoms-16:two-label:positive | 40 | 40 | 14.7% | 40 | 26.2% | 1.18 |
| atoms-16:unique:negative-count | 40 | 40 | 6.4% | 40 | 19.6% | 1.02 |
| atoms-16:unique:negative-flip | 40 | 40 | 0.0% | 40 | 0.0% | 1.00 |
| atoms-16:unique:positive | 40 | 40 | 0.1% | 40 | 0.8% | 1.00 |
| atoms-32:one-label:negative-count | 30 | 30 | 79.0% | 29 | 99.8% | 152.13 |
| atoms-32:one-label:positive | 40 | 40 | 36.1% | 40 | 91.5% | 1.27 |
| atoms-32:two-label:negative-count | 40 | 40 | 70.8% | 38 | 99.6% | 57.01 |
| atoms-32:two-label:positive | 40 | 40 | 40.4% | 40 | 86.6% | 1.37 |
| atoms-32:unique:negative-count | 40 | 40 | 27.4% | 40 | 83.4% | 3.93 |
| atoms-32:unique:negative-flip | 40 | 40 | 0.0% | 40 | 0.0% | 1.00 |
| atoms-32:unique:positive | 40 | 40 | 5.7% | 40 | 19.3% | 1.06 |
| atoms-8:one-label:negative-count | 33 | 33 | 0.7% | 33 | 1.3% | 1.00 |
| atoms-8:one-label:negative-flip | 40 | 40 | 0.0% | 40 | 0.0% | 1.00 |
| atoms-8:one-label:positive | 40 | 40 | 13.5% | 40 | 17.6% | 1.12 |
| atoms-8:two-label:negative-count | 40 | 40 | 3.6% | 40 | 7.0% | 1.00 |
| atoms-8:two-label:negative-flip | 40 | 40 | 0.0% | 40 | 0.0% | 1.00 |
| atoms-8:two-label:positive | 40 | 40 | 3.6% | 40 | 4.4% | 1.00 |
| atoms-8:unique:negative-count | 40 | 40 | 0.0% | 40 | 0.0% | 1.00 |
| atoms-8:unique:negative-flip | 40 | 40 | 0.0% | 40 | 0.0% | 1.00 |
| atoms-8:unique:positive | 40 | 40 | 0.0% | 40 | 0.0% | 1.00 |

## Hypotheses

- H83 (holds): over the count-preserving negatives, at least half of strictMemo's queries are revisits (pooled share of memo hits among all queries >= 0.5). {"pooledRevisitShare": 0.7062229176154425, "interval": [0.6733204601187021, 0.7310750988142293], "tasks": 343}
- H84 (holds): at 16 and at 32 atoms, the pooled revisit share of strictMemo is higher on the count-preserving negatives than on the positives. {"atoms-16": {"countNegatives": 0.21788311338540264, "positives": 0.12420634920634921}, "atoms-32": {"countNegatives": 0.7164515402195255, "positives": 0.32221052631578945}}
- H85 (holds): strictNoMemo decides fewer of the 32-atom count-preserving negatives than strictMemo. {"tasks": 110, "decided": {"strictMemo": 110, "strictNoMemo": 107}}
- H86 (fails): on the count-preserving negatives that both arms decide, the median ratio of strictNoMemo's explored queries to strictMemo's exceeds 2. {"bothDecided": 340, "medianWorkRatio": 1.2222222222222223}

## Checks

- C26 (holds): strictMemo reproduces matched-search-v0.2's focusedStrict on every task: the same outcome and the same six counters (proveCalls, focusCalls, cacheHits, decides, splits, infeasible).
- C27 (holds): no arm gives a wrong answer.
