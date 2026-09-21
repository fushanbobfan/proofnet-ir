# Equal-information matched search (v0.11 step 2)

Three arms, one input (the sequent), one wall-clock budget of 5000 ms per arm per task; definitions, corpus, and hypotheses are
frozen in `preregistration.json` (SHA-256 `8ab0f64eca65dc302b9c1bb54b948eaa7a6d476b80b8d3078f37f444124c0e88`).

Tasks: 640. Wrong answers (a decided outcome contradicting the certified label): {'focused': 0, 'focusedBalanced': 0, 'nets': 0}.

| Stratum | Tasks | focused found/refuted/timeout (median ms) | focusedBalanced (median ms) | nets (median ms) |
| --- | ---: | --- | --- | --- |
| atoms-16:one-label:negative | 40 | 0/40/0 (52.77) | 0/40/0 (9.22) | 0/39/1 (2966.35) |
| atoms-16:one-label:positive | 40 | 40/0/0 (0.21) | 40/0/0 (0.08) | 40/0/0 (206.30) |
| atoms-16:two-label:negative | 40 | 0/40/0 (107.09) | 0/40/0 (7.90) | 0/40/0 (46.54) |
| atoms-16:two-label:positive | 40 | 40/0/0 (0.85) | 40/0/0 (0.20) | 40/0/0 (6.51) |
| atoms-16:unique:negative | 40 | 0/40/0 (216.84) | 0/40/0 (4.10) | 0/40/0 (0.17) |
| atoms-16:unique:positive | 40 | 40/0/0 (13.49) | 40/0/0 (0.18) | 40/0/0 (0.32) |
| atoms-32:one-label:positive | 40 | 39/0/1 (0.86) | 40/0/0 (0.29) | 0/0/40 (5001.27) |
| atoms-32:two-label:positive | 40 | 31/0/9 (70.85) | 40/0/0 (1.42) | 2/0/38 (5001.18) |
| atoms-32:unique:negative | 40 | 0/0/40 (5010.75) | 0/36/4 (1893.81) | 0/40/0 (9.79) |
| atoms-32:unique:positive | 40 | 3/0/37 (5007.88) | 40/0/0 (12.62) | 40/0/0 (1.94) |
| atoms-8:one-label:negative | 40 | 0/40/0 (0.26) | 0/40/0 (0.12) | 0/40/0 (0.68) |
| atoms-8:one-label:positive | 40 | 40/0/0 (0.02) | 40/0/0 (0.02) | 40/0/0 (0.21) |
| atoms-8:two-label:negative | 40 | 0/40/0 (0.34) | 0/40/0 (0.15) | 0/40/0 (0.12) |
| atoms-8:two-label:positive | 40 | 40/0/0 (0.03) | 40/0/0 (0.02) | 40/0/0 (0.11) |
| atoms-8:unique:negative | 40 | 0/40/0 (0.42) | 0/40/0 (0.13) | 0/40/0 (0.04) |
| atoms-8:unique:positive | 40 | 40/0/0 (0.04) | 40/0/0 (0.02) | 40/0/0 (0.10) |

## Hypotheses

- H4 (nets decides at least as many unique-label tasks as focusedBalanced in every size, and is faster at 32 atoms): {'decidedAtLeastOnUnique': True, 'fasterMedianOn32Unique': True, 'supported': True}.
- H5 (focusedBalanced finds more one-label 32-atom positives than nets): supported: True.
- H6 (balance pruning never loses to the committed baseline): supported: True.

## Interpretation boundary

Two search families on unit-free, cut-free MLL sequents under one budget on one
machine. The result says where rule-order redundancy or linking redundancy
dominates for these corpora; it says nothing about proof assistants at the
scale of Lean or Mathlib, and it claims no general advantage for proof nets.
