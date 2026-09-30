# Representation-as-target model study v0.3

Qwen3.8-27B, with and without thinking, on 90 positives; frozen in `preregistration.json` (SHA-256 `a5a4baa159ceadfcd9977849ede1058cd36f8275f44e7faa7d59b1b4f9044b7a`).

| Condition | Arm | Verified | Unprovable | Unparseable | Truncated | Median tokens |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| direct | proof | 0 | 48 | 16 | 15 | 8.0 |
| direct | proofIds | 0 | 27 | 18 | 16 | 256.0 |
| direct | net | 11 | 60 | 9 | 5 | 8.0 |
| thinking | proof | 30 | 1 | 29 | 13 | 6389.5 |
| thinking | proofIds | 32 | 1 | 22 | 2 | 6395.0 |
| thinking | net | 35 | 6 | 1 | 0 | 6190.0 |

## Hypotheses

- H74 (thinking/proofIds over direct/proofIds): supported: True; 32 against 0 verified by one side alone (one-sided p 2.33e-10, Holm 9.31e-10).
- H75 (thinking/net over thinking/proofIds): supported: False; 7 against 4 verified by one side alone (one-sided p 0.274, Holm 0.823).
- H76 (thinking/proofIds over thinking/net): supported: False; 4 against 7 verified by one side alone (one-sided p 0.887, Holm 0.887).
- H77 (thinking/proofIds over thinking/proof): supported: False; 5 against 3 verified by one side alone (one-sided p 0.363, Holm 0.823).

Checks: C20 {'errors': 0, 'holds': True}; C21 {'thinkingTruncated': 15, 'thinkingAnswers': 270, 'holds': True}; C22 (amendment 1) {'serverFailures': 0, 'holds': True}.

## Server failures (amendment 1)

19 responses to 17 requests ended at the token limit in a run of one repeated character (by condition {'direct': 3, 'thinking': 16}, by arm {'proof': 3, 'proofIds': 8, 'net': 8}); they are kept in `server-failures.jsonl` and their requests were sent again. As registered, with each request's first failure in place:

- H74: supported: True; 28 against 0 (one-sided p 3.73e-09, Holm 1.49e-08).
- H75: supported: False; 10 against 5 (one-sided p 0.151, Holm 0.453).
- H76: supported: False; 5 against 10 (one-sided p 0.941, Holm 1).
- H77: supported: False; 6 against 7 (one-sided p 0.709, Holm 1).

Checks as registered: C21 {'thinkingTruncated': 29, 'thinkingAnswers': 270, 'holds': False}.

