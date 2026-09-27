# Matched search v0.2: pruned arms and count-preserving negatives

Five arms, the sequent as the only input, 5000 ms of wall clock per arm per task; definitions, corpus, and hypotheses are frozen in
`preregistration.json` (SHA-256 `cf7609daf36d52da846e515fd6a9f945fe29acb164b1bc11559b6bf3615f0a47`).

Tasks: 983. Wrong answers: {'focused': 0, 'focusedBalanced': 0, 'nets': 0, 'netsPruned': 0, 'focusedStrict': 0}.

Cells: found/refuted/timeout (median ms).

| Stratum | Tasks | focused | focusedBalanced | nets | netsPruned | focusedStrict |
| --- | ---: | --- | --- | --- | --- | --- |
| atoms-16:one-label:negative-count | 40 | 0/40/0 (24.64) | 0/40/0 (3.05) | 0/19/21 (5000.24) | 0/40/0 (288.84) | 0/40/0 (0.28) |
| atoms-16:one-label:negative-flip | 40 | 0/40/0 (93.02) | 0/40/0 (15.51) | 0/21/19 (4727.09) | 0/40/0 (0.04) | 0/40/0 (0.01) |
| atoms-16:one-label:positive | 40 | 40/0/0 (0.34) | 40/0/0 (0.15) | 40/0/0 (297.38) | 40/0/0 (0.84) | 40/0/0 (0.10) |
| atoms-16:two-label:negative-count | 40 | 0/40/0 (38.25) | 0/40/0 (1.68) | 0/40/0 (71.69) | 0/40/0 (4.39) | 0/40/0 (0.17) |
| atoms-16:two-label:negative-flip | 40 | 0/40/0 (192.32) | 0/40/0 (14.05) | 0/40/0 (70.49) | 0/40/0 (0.04) | 0/40/0 (0.01) |
| atoms-16:two-label:positive | 40 | 40/0/0 (1.65) | 40/0/0 (0.29) | 40/0/0 (9.92) | 40/0/0 (0.67) | 40/0/0 (0.11) |
| atoms-16:unique:negative-count | 40 | 0/40/0 (271.52) | 0/40/0 (3.27) | 0/40/0 (0.27) | 0/40/0 (0.06) | 0/40/0 (0.28) |
| atoms-16:unique:negative-flip | 40 | 0/40/0 (433.97) | 0/40/0 (7.64) | 0/40/0 (0.28) | 0/40/0 (0.03) | 0/40/0 (0.02) |
| atoms-16:unique:positive | 40 | 40/0/0 (21.14) | 40/0/0 (0.34) | 40/0/0 (0.60) | 40/0/0 (0.48) | 40/0/0 (0.13) |
| atoms-32:one-label:negative-count | 30 | 0/2/28 (5095.30) | 0/20/10 (3236.05) | 0/0/30 (5003.08) | 0/0/30 (5002.89) | 0/30/0 (15.59) |
| atoms-32:one-label:positive | 40 | 39/0/1 (1.30) | 40/0/0 (0.55) | 0/0/40 (5002.52) | 21/0/19 (2521.43) | 40/0/0 (0.36) |
| atoms-32:two-label:negative-count | 40 | 0/0/40 (5029.43) | 0/21/19 (3299.52) | 0/0/40 (5001.44) | 0/0/40 (5002.48) | 0/40/0 (26.07) |
| atoms-32:two-label:positive | 40 | 30/0/10 (136.89) | 40/0/0 (2.17) | 2/0/38 (5001.81) | 18/0/22 (5000.21) | 40/0/0 (0.62) |
| atoms-32:unique:negative-count | 40 | 0/0/40 (5017.62) | 0/36/4 (1849.07) | 0/40/0 (13.66) | 0/40/0 (0.19) | 0/40/0 (12.62) |
| atoms-32:unique:negative-flip | 40 | 0/0/40 (5012.10) | 0/34/6 (3355.41) | 0/40/0 (17.63) | 0/40/0 (0.11) | 0/40/0 (0.03) |
| atoms-32:unique:positive | 40 | 3/0/37 (5011.34) | 40/0/0 (25.68) | 40/0/0 (3.03) | 40/0/0 (2.45) | 40/0/0 (1.06) |
| atoms-8:one-label:negative-count | 33 | 0/33/0 (0.15) | 0/33/0 (0.06) | 0/33/0 (1.18) | 0/33/0 (0.06) | 0/33/0 (0.02) |
| atoms-8:one-label:negative-flip | 40 | 0/40/0 (0.55) | 0/40/0 (0.26) | 0/40/0 (1.29) | 0/40/0 (0.01) | 0/40/0 (0.01) |
| atoms-8:one-label:positive | 40 | 40/0/0 (0.05) | 40/0/0 (0.04) | 40/0/0 (0.43) | 40/0/0 (0.17) | 40/0/0 (0.03) |
| atoms-8:two-label:negative-count | 40 | 0/40/0 (0.24) | 0/40/0 (0.06) | 0/40/0 (0.20) | 0/40/0 (0.03) | 0/40/0 (0.02) |
| atoms-8:two-label:negative-flip | 40 | 0/40/0 (0.77) | 0/40/0 (0.31) | 0/40/0 (0.26) | 0/40/0 (0.01) | 0/40/0 (0.01) |
| atoms-8:two-label:positive | 40 | 40/0/0 (0.07) | 40/0/0 (0.04) | 40/0/0 (0.24) | 40/0/0 (0.17) | 40/0/0 (0.03) |
| atoms-8:unique:negative-count | 40 | 0/40/0 (0.61) | 0/40/0 (0.10) | 0/40/0 (0.05) | 0/40/0 (0.02) | 0/40/0 (0.03) |
| atoms-8:unique:negative-flip | 40 | 0/40/0 (0.92) | 0/40/0 (0.29) | 0/40/0 (0.08) | 0/40/0 (0.01) | 0/40/0 (0.01) |
| atoms-8:unique:positive | 40 | 40/0/0 (0.08) | 40/0/0 (0.05) | 40/0/0 (0.20) | 40/0/0 (0.17) | 40/0/0 (0.03) |

## Hypotheses

Registered as H7 to H10; relabeled H68 to H71 by `amendment-1.json`, statements unchanged.

- H68 (netsPruned decides at least as many as nets everywhere and finds more 32-atom repeated-label positives): supported: True; tests: 18 vs 2 (one-sided p 1.53e-05); 21 vs 0 (one-sided p 4.77e-07).
- H69 (focusedStrict decides at least as many as focusedBalanced everywhere): supported: True.
- H70 (focusedStrict finds more 32-atom one-label positives than netsPruned): supported: True; 40 vs 21 (one-sided p 1.91e-06).
- H71 (netsPruned refutes fewer than half of the 32-atom one-label count-preserving negatives): supported: True; 0 of 30.

## Checks

- C15: {'flipNegatives': 280, 'violatingCount': 280, 'refutedAtRootByNetsPruned': 280, 'holds': True}
- C16: {'countNegatives': 343, 'holds': True}
- C17: {'holds': True}

## Interpretation boundary

Unit-free, cut-free MLL sequents under one budget on one machine. focusedStrict certified the
count-preserving negatives that have no countermodel, so its refutations of those are not an
independent measurement. Nothing here concerns proof assistants at the scale of Lean or Mathlib.
