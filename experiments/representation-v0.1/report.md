# Representation-as-target model study (v0.11 step 3)

One local model, one rendering, two output targets; prompts, corpus, model, and
hypotheses are frozen in `preregistration.json` (SHA-256 `ae738aa3219f8f93300363f8d828900e81444fef20bf1347270e1f3120154c86`).

Tasks: 180 (each run in both arms). Rates: {"proof": {"positiveValidRate": 0.0, "negativeCorrectRate": 0.0, "medianTokensValidPositives": null}, "net": {"positiveValidRate": 0.07777777777777778, "negativeCorrectRate": 0.7111111111111111, "medianTokensValidPositives": 22}}.

| Stratum | proof correct/valid/unprovable-claims/unparseable (median tokens) | net correct/valid/unprovable-claims/unparseable (median tokens) |
| --- | --- | --- |
| depth-2:one-label:negative | 0/0/0/0 (86.0) | 10/0/10/0 (8.0) |
| depth-2:one-label:positive | 0/0/0/0 (119.0) | 0/0/10/0 (8.0) |
| depth-2:two-label:negative | 0/0/0/0 (110.5) | 10/0/10/0 (8.0) |
| depth-2:two-label:positive | 0/0/0/0 (145.5) | 1/1/9/0 (8.0) |
| depth-2:unique:negative | 0/0/0/0 (212.0) | 9/0/9/0 (8.0) |
| depth-2:unique:positive | 0/0/0/0 (207.0) | 6/6/1/0 (22.0) |
| depth-3:one-label:negative | 0/0/0/1 (541.5) | 10/0/10/0 (8.0) |
| depth-3:one-label:positive | 0/0/0/1 (528.0) | 0/0/9/0 (8.0) |
| depth-3:two-label:negative | 0/0/0/1 (605.5) | 8/0/8/0 (8.0) |
| depth-3:two-label:positive | 0/0/0/2 (647.5) | 0/0/7/0 (8.0) |
| depth-3:unique:negative | 0/0/0/4 (862.5) | 4/0/4/0 (76.5) |
| depth-3:unique:positive | 0/0/0/2 (696.5) | 0/0/4/0 (44.0) |
| depth-4:one-label:negative | 0/0/0/8 (1024.0) | 6/0/6/0 (12.0) |
| depth-4:one-label:positive | 0/0/0/9 (1024.0) | 0/0/8/0 (11.0) |
| depth-4:two-label:negative | 0/0/0/7 (1024.0) | 6/0/6/0 (11.5) |
| depth-4:two-label:positive | 0/0/0/6 (1024.0) | 0/0/5/0 (87.5) |
| depth-4:unique:negative | 0/0/0/6 (1024.0) | 1/0/1/0 (170.5) |
| depth-4:unique:positive | 0/0/0/8 (1024.0) | 0/0/0/0 (161.5) |

## Hypotheses

- H7 (net arm has the higher Lean-verified rate on positives): supported: True.
- H8 (verified net outputs use fewer tokens than verified proofs): supported: None.
- H9 (negative-detection rates within ten points): supported: False.

## Interpretation boundary

One quantized local model at temperature zero without thinking, on held-out
unit-free, cut-free MLL sequents. The result concerns which representation this
model produces correctly under this budget; it is not a claim about proof
assistants at the scale of Lean or Mathlib, nor about other models.
