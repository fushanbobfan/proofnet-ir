# Representation-as-target model study v0.2

representation-v0.1 found that one local model writes valid proof-net linkings for a few small sequents (7 of
90 positives) and no valid sequent proof, with the proofs failing on position bookkeeping and many answers
cut off at 1,024 tokens. This study asks whether that lead survives when three conditions around the
representation are removed: every answer is decoded under a grammar that admits only its format's JSON
shapes, the budget is 8,192 completion tokens, and a third arm writes the same derivations over stable
subformula labels instead of positions that shift after every rule.

## Arms

- `proof`: representation-v0.1's position-based derivation, prompt and rendering unchanged;
- `proofIds`: the same derivations over labels (atoms `a0`, `a1`, ..., connectives `c0`, `c1`, ... in
  reading order, every subformula labelled in the rendering), converted to the position format before Lean
  verifies them;
- `net`: representation-v0.1's axiom linking, prompt and rendering unchanged.

The model, the corpus, and the decoding settings are representation-v0.1's: `Qwen3.6-35B-A3B-UD-Q4_K_XL`
served locally at temperature 0 with seed 20260921 and thinking disabled, on the 180 held-out tasks of
`experiments/model-v0.2`. Verification is v0.1's (`proofnet_ir_representation_verify`).

## Artifacts

- `preregistration.json`: the arms, the prompts and grammars by hash, the model settings, hypotheses H72
  and H73, checks C18 and C19, and the pilot's outcome, committed before any response was collected;
- `raw-responses.jsonl`: every response verbatim, with its request hash and elapsed time;
- `results.jsonl`: per task and arm, the claim, the proposal, the label conversion, the Lean verdict and its
  reason, correctness, and completion tokens;
- `summary.json` and `report.md`: the arm and stratum tables and the decisions.

## Reproduction

```text
python scripts/run_representation_v2.py --check-committed
python scripts/run_representation_v2.py --self-test
```

The first re-verifies every committed proposal with Lean and checks the hashes; CI runs it. The second checks
the label conversion on hand-made derivations. `--run` re-collects the responses from a local server (about
two and a half hours), which is not deterministic across hardware or server builds.

## Outcome

- **H73 holds**: nets verified 6 positives and labelled derivations none (one-sided p = 0.016). The six are
  depth-2 sequents with unique labels (6 of 10), as in v0.1; none is at depth 3 or 4.
- **H72 does not hold**: neither derivation format verified any positive (0 against 0).
- The failure moved with the format. With positions, 138 of 180 proposals apply a tensor rule at a position
  that does not hold a tensor (v0.1: 100). With labels, 167 of 180 fail conversion: 108 split a tensor's
  context with formulas that are not in the sequent at that point, 45 apply a rule to a label that names
  another connective, and 14 to a label no longer in the sequent.
- More tokens did not help. Every verified net took under 64 tokens (median 22), and 34 answers (28 position
  derivations, 6 labelled ones) ran to the 8,192-token limit, so **C18 fails**. No request failed (C19
  holds).
- The net arm answered `unprovable` on 59 of the 90 positives and 69 of the 90 negatives; as in v0.1, that
  is not discrimination.

## Interpretation boundary

For this model at temperature zero without thinking, the net format's lead over derivations survives grammar
constraints, eight times the budget, and stable labels: derivations fail on bookkeeping, of positions or of
context splits, in either format. This is a statement about one quantized model and one prompt design on
unit-free, cut-free MLL; it claims no general model or proof-net advantage. A model that reasons before it
answers has not been tested.
