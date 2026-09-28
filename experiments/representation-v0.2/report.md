# Representation-as-target model study v0.2

Three output formats, one model at temperature zero without thinking, each answer decoded under its
format's grammar with 8,192 completion tokens; frozen in `preregistration.json` (SHA-256
`395327191a6cf118d611bc49aea8f48d7abcc0d3bc1780f7a57291c15880ef17`).

Tasks: 180 (90 positives, 90 negatives).

| Arm | Verified positives | Unprovable on positives / negatives | Unparseable | Truncated | Median tokens (verified) |
| --- | ---: | --- | ---: | ---: | ---: |
| proof | 0 | 0 / 0 | 28 | 28 | None |
| proofIds | 0 | 2 / 4 | 6 | 6 | None |
| net | 6 | 59 / 69 | 0 | 0 | 22.0 |

Verified positives within a token budget:

| Arm | 64 | 128 | 256 | 512 | 1024 | 2048 | 4096 | 8192 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| proof | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| proofIds | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| net | 6 | 6 | 6 | 6 | 6 | 6 | 6 | 6 |

| Stratum | proof valid/unprovable | proofIds valid/unprovable | net valid/unprovable |
| --- | --- | --- | --- |
| depth-2:one-label:negative | 0/0 | 0/0 | 0/10 |
| depth-2:one-label:positive | 0/0 | 0/0 | 0/10 |
| depth-2:two-label:negative | 0/0 | 0/0 | 0/10 |
| depth-2:two-label:positive | 0/0 | 0/0 | 0/10 |
| depth-2:unique:negative | 0/0 | 0/0 | 0/9 |
| depth-2:unique:positive | 0/0 | 0/0 | 6/0 |
| depth-3:one-label:negative | 0/0 | 0/0 | 0/10 |
| depth-3:one-label:positive | 0/0 | 0/0 | 0/7 |
| depth-3:two-label:negative | 0/0 | 0/0 | 0/5 |
| depth-3:two-label:positive | 0/0 | 0/0 | 0/8 |
| depth-3:unique:negative | 0/0 | 0/0 | 0/4 |
| depth-3:unique:positive | 0/0 | 0/0 | 0/4 |
| depth-4:one-label:negative | 0/0 | 0/2 | 0/10 |
| depth-4:one-label:positive | 0/0 | 0/2 | 0/10 |
| depth-4:two-label:negative | 0/0 | 0/1 | 0/8 |
| depth-4:two-label:positive | 0/0 | 0/0 | 0/7 |
| depth-4:unique:negative | 0/0 | 0/1 | 0/3 |
| depth-4:unique:positive | 0/0 | 0/0 | 0/3 |

## Hypotheses

- H72 (proofIds verifies more positives than proof): supported: False; 0 vs 0, 0 and 0 verified by one arm alone (one-sided p 1).
- H73 (net verifies more positives than proofIds): supported: True; 6 vs 0, 6 and 0 verified by one arm alone (one-sided p 0.0156).

Checks: C18 {'truncated': 34, 'holds': False}; C19 {'errors': 0, 'holds': True}.

## Interpretation boundary

One quantized local model on held-out unit-free, cut-free MLL sequents. The result concerns which output
format this model produces correctly under these conditions, not models in general or proof assistants.
