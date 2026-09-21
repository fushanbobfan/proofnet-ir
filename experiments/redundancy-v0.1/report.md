# Search-redundancy experiment (v0.11 step 1)

Exact counts of cut-free derivations per proof net on the committed MLL
corpora; definitions, budgets, and hypotheses are frozen in
`preregistration.json` (SHA-256 `33d600e35c9bcf0a80328212875a57ca8d1f2a4b301fdd553a2ec6bf9e47c58f`).

Tasks: 1180; complete: 1160; excluded: 20; cross-checked against the brute-force enumerator: 1060 with 0 disagreements.

| Stratum | Tasks | Ratio-bearing | dAll/nets median (q1, q3, max) | dWeak/nets median | dFoc/nets median | dFoc/dWeak median | dFoc/nets = 1 |
| --- | ---: | ---: | --- | ---: | ---: | ---: | ---: |
| matched:atoms-16 | 250 | 250 | 36 (13, 156.25, 12864) | 10 | 7 | 0.666667 | 3.2% |
| matched:atoms-32 | 50 | 50 | 170734 (24967.5, 2.74889e+06, 5.72024e+08) | 3263.75 | 362 | 0.154681 | 0.0% |
| matched:atoms-8 | 700 | 700 | 2 (2, 3, 19) | 2 | 2 | 1 | 25.6% |
| model:depth-2:one-label:negative | 10 | 0 | n/a | n/a | n/a | n/a | n/a |
| model:depth-2:one-label:positive | 10 | 10 | 2.33333 (1.33333, 4.83333, 7.66667) | 2.16667 | 2 | 1 | 30.0% |
| model:depth-2:two-label:negative | 10 | 0 | n/a | n/a | n/a | n/a | n/a |
| model:depth-2:two-label:positive | 10 | 10 | 3 (2, 6.625, 15.6667) | 2.25 | 2.25 | 1 | 10.0% |
| model:depth-2:unique:negative | 10 | 0 | n/a | n/a | n/a | n/a | n/a |
| model:depth-2:unique:positive | 10 | 10 | 2 (1, 2.25, 19) | 2 | 2 | 1 | 40.0% |
| model:depth-3:one-label:negative | 10 | 0 | n/a | n/a | n/a | n/a | n/a |
| model:depth-3:one-label:positive | 10 | 10 | 248.729 (27.7143, 1087.4, 2507.61) | 33.9416 | 19.5521 | 0.526305 | 0.0% |
| model:depth-3:two-label:negative | 10 | 0 | n/a | n/a | n/a | n/a | n/a |
| model:depth-3:two-label:positive | 10 | 10 | 54.2143 (26.1875, 217.178, 1031.69) | 17.7639 | 9.64062 | 0.574703 | 0.0% |
| model:depth-3:unique:negative | 10 | 0 | n/a | n/a | n/a | n/a | n/a |
| model:depth-3:unique:positive | 10 | 10 | 18 (6.5, 22, 114) | 8 | 5 | 0.666667 | 0.0% |
| model:depth-4:one-label:negative | 10 | 0 | n/a | n/a | n/a | n/a | n/a |
| model:depth-4:one-label:positive | 10 | 0 | n/a | n/a | n/a | n/a | n/a |
| model:depth-4:two-label:negative | 10 | 0 | n/a | n/a | n/a | n/a | n/a |
| model:depth-4:two-label:positive | 10 | 0 | n/a | n/a | n/a | n/a | n/a |
| model:depth-4:unique:negative | 10 | 0 | n/a | n/a | n/a | n/a | n/a |
| model:depth-4:unique:positive | 10 | 10 | 3.41628e+06 (448460, 7.58377e+06, 1.21839e+07) | 14634.2 | 1315 | 0.134923 | 0.0% |

## Hypotheses

- H1 (dFoc/nets > 1 on more than half of the ratio-bearing tasks): fraction 0.818; supported: True.
- H2 (median dAll/nets more than doubles from 8 to 16 and from 16 to 32 atoms): medians {'8': 2.0, '16': 36.0, '32': 170733.5}; supported: True.
- H3 (dFoc < dWeak on more than half of the ratio-bearing tasks): fraction 0.278; supported: False.

## Interpretation boundary

The ratios measure how many derivations of each calculus denote one proof net
on these corpora. They are properties of the search spaces, not of any search
procedure's running time, and they claim no advantage for any method; the
matched corpus is derivation-generated with mostly unique labels, and the
model corpus adds repeated labels and negatives.
