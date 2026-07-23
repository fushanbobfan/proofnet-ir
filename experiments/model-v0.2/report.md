# Model-backed held-out experiment v0.2: final report

Run date: 2026-07-22 (America/Los_Angeles)

## Result

| Method | Correct / 180 | Rate | Positive / 90 | Negative / 90 | Main failure |
| --- | ---: | ---: | ---: | ---: | --- |
| Focused search | 85 | 47.2% | 55 | 30 | 95 budget-exhausted unknowns |
| Proof-net generation | 160 | 88.9% | 90 | 70 | 20 hard timeouts |
| Distance-ordered repair | 180 | 100.0% | 90 | 90 | none in this constructed task family |
| Model direct | 117 | 65.0% | 27 | 90 | 43 false `U` on positives; 10 direct truncations |
| Model repair | 2 | 1.1% | 2 | 0 | 91 truncations and invalid endpoint proposals |

This does not establish a model or proof-net advantage. The perfect repair
score is a property of this controlled construction: every positive starts
two or three reference axiom edges from a known solution, while every negative
has a per-label polarity imbalance that makes a complete typed axiom matching
impossible. The algorithm used only 123 checker calls across 180 tasks. It is
not evidence that arbitrary proof repair is easy.

## Preregistration and amendment

The corpus, prompts, implementation hashes, budgets, and success criteria were
committed in `3d767aa5aec53060272007209e91b7531b45929e` before any task-specific
model response. All 360 Qwen3.6-35B-A3B Q4 calls then completed with zero
transport errors. Their frozen raw-response SHA-256 is
`5cff2378c2d6d3454ec7dc51c0ae39db3f8cbaa612a5b6faef00c977b48f0bef`.

The original runner exposed a real execution bug before any formal result or
aggregate existed: its 60-second wall-clock threshold was tested only after a
method returned. After 120.2 minutes it had not reached Lean verification.
[Protocol amendment 1](protocol-amendment-1.json), publicly committed before
amended scoring, preserved every task, prompt, response, method, budget, and
success rule while isolating each task/method in a child process with a real
60-second deadline and atomic per-task checkpointing.

The amended run took 2,644,471 ms, including scoring and final Lean batch
verification. Worker startup is included in algorithmic timings, so raw
latencies should not be interpreted as hardware-normalized compute comparisons
against the already-running model server.

## Stratified findings

| Stratum | Focused | Net generation | Algorithmic repair | Model direct | Model repair |
| --- | ---: | ---: | ---: | ---: | ---: |
| Depth 2 (60) | 60 | 60 | 60 | 41 | 0 |
| Depth 3 (60) | 19 | 60 | 60 | 46 | 2 |
| Depth 4 (60) | 6 | 40 | 60 | 30 | 0 |
| Unique labels (60) | 24 | 60 | 60 | 38 | 1 |
| Two labels (60) | 26 | 50 | 60 | 41 | 0 |
| One label (60) | 35 | 50 | 60 | 38 | 1 |

Model-direct overall accuracy is dominated by the deliberately easy negative
invariant: it returned `U` on all 90 negative tasks and was correct on all of
them. On provable tasks it succeeded only 27/90. It solved 11/30 depth-2 and
16/30 depth-3 positives, but 0/30 depth-4 positives; 21 depth-4 positives were
declared unprovable and nine ended as response errors.

Model repair did not exploit the supplied corrupted matching. It returned no
`U`, solved only `model-44-positive` and `model-45-positive`, and failed every
negative. The fixed 128-token completion cap caused 91 length finishes. Among
responses that stopped normally, invalid/self/non-atom endpoints and incomplete
coverage remained common. This is evidence against the current prompt/budget,
not evidence that model-guided repair is impossible.

Proof-net generation solved every positive and every depth-2/3 negative. Its
20 failures were exactly the depth-4 negative tasks in the two-label and
one-label strata. Those searches were killed at the amended hard deadline;
unique-label depth-4 negatives completed. Focused search had no wall-clock
timeout but exhausted its 1,000-state/partition budget on 95 tasks.

## Lean verification

The final cross-language batch contained 276 distinct certificates:

- all 184 expected-invalid inputs were rejected by Lean;
- all 92 certificates accepted by the independent oracle were accepted by the
  Lean checker;
- all 92/92 Lean-accepted certificates successfully executable-sequentialized.

Thus the experiment found no checker disagreement and no checker-accepted
counterexample to executable sequentialization. This empirical result supports
the implementation, while the universal guarantee still comes from the Lean
theorem `Certificate.sequentialize_complete`, not from the sample.

## Artifact hashes

- corpus: `0bb9a950ebb5f3706cd0f0629d668801ae7174e97c6fa9f4f175c7c299d36dc2`
- raw responses: `5cff2378c2d6d3454ec7dc51c0ae39db3f8cbaa612a5b6faef00c977b48f0bef`
- per-task results: `ece2210e47f18db8fda9bbe02959d6978fb084251c9127053b25bea765c87421`
- summary: `af64c103b497bb6316aa83078047242c4ec67881e817e65dd057293faff08db8`

Recheck every committed hash and the Lean-verification equality with:

```text
python scripts/run_model_experiment_amended.py --check-committed
```

The result is limited to unit-free, cut-free MLL with a supplied connective
skeleton. It says nothing directly about ordinary Lean/mathlib goals, cuts,
units, additives, exponentials, arbitrary graph isomorphism, or a general
proof-search advantage.
