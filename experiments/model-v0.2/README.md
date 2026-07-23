# Preregistered model-backed MLL experiment v0.2

Registration date: 2026-07-22 (America/Los_Angeles), before any task-specific
model response, formal aggregate, or result artifact was generated. Corpus
engineering did validate fixture construction, the independent checker, and
the exact-distance repair enumerator before registration; those development
checks are disclosed in the machine-readable registration.

## Protocol amendment 1

All 360 frozen model calls completed with zero transport errors. Before any
formal aggregate or task result was written or inspected, the preregistered
runner exposed an execution bug: its 60-second algorithmic wall-clock budget
was classified only after a method returned. After 120.2 minutes total wall
time, including roughly 100 minutes of algorithmic scoring, it had still not
reached Lean batch verification. The exact process was stopped and the raw
response capture was frozen at SHA-256
`5cff2378c2d6d3454ec7dc51c0ae39db3f8cbaa612a5b6faef00c977b48f0bef`.

[Protocol amendment 1](protocol-amendment-1.json) leaves the corpus, prompts,
model parameters, all raw responses, method definitions, candidate budgets,
and success criteria unchanged. It runs each algorithmic task/method in a
fresh child process with a real 60-second deadline, counts worker startup
inside that deadline, and atomically checkpoints each scored task. The
original preregistered runner remains unchanged and hash-verifiable; the
amended runner is a separate file. This is a disclosed execution amendment,
not a claim that the original formal run completed.

## Final outcome

Amended scoring and Lean verification are complete. The headline correct-task
counts are focused search 85/180, proof-net generation 160/180,
distance-ordered repair 180/180, model direct 117/180, and model repair 2/180.
All 92 distinct Lean-accepted outputs executable-sequentialized; all 184
distinct expected-invalid inputs were rejected. The [final report](report.md)
contains the positive/negative, depth, label, timeout, truncation, and
interpretation breakdown. In particular, model direct was 90/90 on the
atom-imbalanced negatives but only 27/90 on positives, so its 65% overall rate
must not be presented as general proof-generation success.

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
python scripts/run_model_experiment_amended.py --check-amendment
```

The amended formal scoring run reuses the frozen raw calls:

```text
python scripts/run_model_experiment_amended.py --write
```

The committed per-task results, summary, and content hashes can be audited
with `--check-committed`. The outcome remains limited to held-out unit-free,
cut-free MLL with a supplied connective skeleton; it does not establish a
general model or proof-net advantage.
