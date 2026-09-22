# Representation-as-target model study v0.1

Step 3 of the v0.11 program ([design](../../docs/v0.11-design.md)): given
one rendering of a sequent and one budget, does the same model emit valid
proof-net linkings more often, and with fewer tokens, than valid
sequent-calculus proofs?

## Artifacts

- `preregistration.json`: corpus hash (the 180 held-out tasks of
  `experiments/model-v0.2`), both system prompts by hash, the model and its
  decoding settings, the verifier hash, and hypotheses H7 to H9, committed on
  `main` before any response was collected;
- `raw-responses.jsonl`: every model response verbatim, with its request
  hash and elapsed time;
- `results.jsonl`: per task and arm, the claim (`provable`, `unprovable`,
  `unparseable`), the parsed proposal, the Lean verdict and its reason,
  correctness, and completion tokens;
- `summary.json` and `report.md`: rates, the stratum table, and the
  hypothesis decisions.

Model: `Qwen3.6-35B-A3B-UD-Q4_K_XL` served locally, temperature 0, seed
20260921, 1,024 completion tokens, thinking disabled, as in the v0.2 study.
Verification: `proofnet_ir_representation_verify` converts a proof to a
`CutFreeDerivation` and requires `infer?` to return the sequent, and
completes a net into a certificate decided by `Certificate.check`.

## Reproduction

```text
python scripts/run_representation_study.py --check-committed
```

re-verifies every committed proposal with Lean and checks the artifact
hashes (about a second); CI runs it. `--run` re-collects the responses from
a local server, which is not deterministic across hardware or server builds.

## Outcome

- Proof arm: no valid proof on any of the 90 positives and no correct answer
  on any of the 90 negatives. The model never answered `unprovable`; on 63
  negatives it emitted a proof-shaped object that Lean rejected, and 55 of
  its 180 answers were unparseable, mostly truncated at the token budget
  (43 of the 60 depth-4 answers hit 1,024 tokens). The dominant rejection
  is position bookkeeping: 51 proposals apply a tensor rule at a position
  that does not hold a tensor.
- Net arm: 7 valid nets on the 90 positives (6 of the 10 depth-2 unique
  tasks, 1 of the 10 depth-2 two-label tasks, none at depth 3 or 4), with a
  median of 22 tokens; 64 of 90 negatives answered `unprovable`. That
  negative rate is not discrimination: the model also answered `unprovable`
  on 53 of the 90 positives.
- H7 supported as registered (7.8% versus 0%); H8 undecidable, because no
  proof was ever verified; H9 not supported (71% versus 0%), for the reason
  above.

Interpretation: under this budget and without thinking, the net format is
the only representation this model produces validly at all, and only on the
smallest unique-label sequents; the sequent-proof format collapses on the
position bookkeeping that proof nets do not require. This is a statement
about one quantized model and one prompt design on unit-free, cut-free MLL,
and it claims no general model or proof-net advantage.
