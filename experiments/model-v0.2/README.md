# Preregistered model-backed MLL experiment v0.2

Registration date: 2026-07-22 (America/Los_Angeles), before any task-specific
model response, formal aggregate, or result artifact was generated. Corpus
engineering did validate fixture construction, the independent checker, and
the exact-distance repair enumerator before registration; those development
checks are disclosed in the machine-readable registration.

This study is the first genuinely model-backed held-out experiment for
ProofNet-IR. It is intentionally an MLL experiment, not a claim about ordinary
Lean or mathlib theorem proving.

## Frozen corpus

- 90 fresh Lean-generated bases use seeds 10,000 through 10,089, disjoint from
  the v0.1 algorithmic corpus's seeds 0 through 999.
- Each base yields one accepted positive task and one negative task formed by
  flipping one atom occurrence and recomputing every connective ancestor.
  The resulting nonzero per-label positive-minus-negative atom count is a
  proof-invariant witness that the negative sequent is unprovable.
- Depths 2, 3, and 4 each contribute 30 bases.
- Within each depth, ten bases retain unique labels, ten collapse to two atom
  labels, and ten collapse all atoms to one label.
- Pairing positive/negative polarity gives 18 strata of exactly ten tasks,
  for 180 tasks total.
- Every positive repair source differs from its reference in exactly two or
  three axiom links, alternating by base index, and is independently rejected.

The committed [corpus](corpus.jsonl) SHA-256 is
`0bb9a950ebb5f3706cd0f0629d668801ae7174e97c6fa9f4f175c7c299d36dc2`.
The machine-readable [preregistration](preregistration.json) freezes the exact
strata, implementation and prompt hashes, model parameters, budgets, and
success criteria.

## Frozen methods and budgets

The same tasks are evaluated by focused sequent search, exhaustive axiom-
matching net generation, distance-ordered checker-guided repair, a model
direct proposal, and a separate model repair proposal. Direct and repair use
different model requests, so the corrupted repair source cannot leak into the
direct condition.

Algorithmic methods receive at most 1,000 complete candidates/states and a
60-second per-task wall-clock outcome budget. Each model condition receives
one deterministic request, one complete proposal, at most 128 completion
tokens, and a 60-second timeout. These are transparent system budgets, not a
claim that unlike search mechanisms consume identical compute.

The repair enumerator visits complete matchings by exact edge distance from
the supplied source. It constructs only candidates inside the 1,000-candidate
budget; it does not materialize or sort the factorial matching space before
the clock starts. The reported repair time covers enumeration and checking.

A positive task succeeds only when the output passes the independent Python
oracle, the compiled Lean checker, and executable Lean sequentialization. A
negative task succeeds only when bounded algorithmic search completes without
a proof, or the model explicitly returns `U`. Invalid model guesses do not
count as correct abstention.

## Reproduction boundary

The preregistration can be regenerated and checked without calling a model:

```text
python scripts/run_model_experiment.py --check-preregistered
```

The formal run uses the active local llama.cpp Qwen3.6-35B-A3B Q4 endpoint and
will commit raw responses, per-task results, a summary, and all content hashes.
No positive or negative outcome is promised in advance. Even a strong result
would remain limited to held-out unit-free, cut-free MLL with a supplied
connective skeleton; it would not establish a general model or proof-net
advantage.
