# Library-readiness audit

Audit date: 2026-07-21  
Audited version: v0.2.0 (`f4ec45b`)

## Verdict

ProofNet-IR v0.2.0 is a usable research prototype and reference checker. It is
not yet a mature reusable Lean library. The published checker can validate its
documented unit-free, cut-free MLL certificates; the dataset and focused-search
baseline can be reproduced. It cannot yet support the stronger claim that any
accepted net can be converted back into a derivation, nor can a downstream
consumer parse arbitrary v0.2 JSON directly into a checked Lean object.

## What is logically established

- involutive linear negation;
- proposition-level local link/resource semantics equivalent to the Boolean
  structural checker;
- exact enumeration of one-edge-per-par switchings;
- checker soundness for independent unbounded walk semantics;
- checker soundness and completeness for the independent fuel-indexed path
  semantics;
- exhaustive differential agreement for all 33,868 simple graphs through six
  vertices and two separate 1,000-certificate corpora;
- exact reconstruction for the recursive identity family;
- after v0.2.0, successful first-order derivation inference denotes a genuine
  kernel-typed `Derivation` (`CutFreeDerivation.infer?_sound`).

## Logical gaps blocking a mature-library claim

1. `Connected` versus `FuelConnected` completeness is not proved for arbitrary
   finite walks, so the standard unbounded correctness predicate lacks an iff
   theorem even though executable behavior has extensive differential tests.
2. The independent `infer?` derivation semantics is not yet formally related
   to every field produced by `build?`; `desequentializeChecked?` safely
   post-checks its output, but a general desequentialization soundness theorem
   is still missing.
3. General sequentialization of every accepted MLL proof net is absent.
4. The edge-count tree characterization is used correctly, but no explicit
   acyclicity predicate/equivalence theorem is exposed as public API.
5. Canonicalization preservation and invariance under vertex reindexing are
   not proved.

## Engineering gaps blocking a mature-library claim

- serialization is write-only; there is no trusted Lean JSON parser with
  structured errors and validation;
- many APIs return `Option`, losing the location and reason for failure;
- no clean-room downstream Lake project currently consumes a pinned release;
- no API stability/compatibility policy or migration test suite exists;
- no generated API reference or tutorial beyond repository-local examples;
- no fuzz/property suite covers arbitrary malformed serialized inputs;
- no performance budget protects users from exponential switching blowups;
- the focused baseline is a Python experiment component, not a Lean library
  module;
- no model-backed matched experiment has established the research hypothesis.

## Current usability boundary

It can currently be used for:

- constructing MLL certificates in Lean;
- checking structural and Danos-Regnier switching correctness;
- generating/desequentializing the first-order derivation syntax and retaining
  only checker-accepted results;
- regenerating the labeled v0.2 corpus;
- running the focused-search comparison baseline.

It should not yet be presented as:

- a general Lean/mathlib proof assistant extension;
- a complete proof-net sequentializer;
- an isomorphism-canonical proof identity library;
- evidence that proof-net generation reduces search redundancy in practice.

## Release gate for library readiness

The macro goal may call the project a library only after all logical gaps above
are closed, a clean downstream Lake consumer passes on Windows and Linux, JSON
round trips have structured diagnostics and fuzz coverage, public API docs and
compatibility rules are published, performance limits are measured, and the
matched experiment reports its result whether positive or negative.
