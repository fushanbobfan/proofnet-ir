# Library-readiness audit

Audit date: 2026-07-22
Audited baseline: v0.3.0 plus the v0.3.1 release candidate on `main`

## Verdict

ProofNet-IR v0.3.1 is a usable research prototype and reference checker. It is
not yet a mature reusable Lean library. The published checker can validate its
documented unit-free, cut-free MLL certificates; the dataset and focused-search
baseline can be reproduced. It cannot yet support the stronger claim that any
accepted net can be converted back into a derivation. Post-release `main` now
lets a downstream consumer parse v0.2/v0.3 JSON directly into a checked Lean
object and migrate v0.2 to a reindex-invariant v0.3 key, but that closes only
part of the engineering and proof-identity gap.

## What is logically established

- involutive linear negation;
- proposition-level local link/resource semantics equivalent to the Boolean
  structural checker;
- exact enumeration of one-edge-per-par switchings;
- checker soundness for independent unbounded walk semantics;
- checker soundness and completeness for the independent fuel-indexed path
  semantics;
- after v0.2.0, loop erasure and finite vertex counting prove completeness for
  the standard unbounded walk semantics as well
  (`check_iff_declarativelyCorrect`);
- exhaustive differential agreement for all 33,868 simple graphs through six
  vertices and two separate 1,000-certificate corpora;
- exact reconstruction for the recursive identity family;
- after v0.2.0, successful first-order derivation inference denotes a genuine
  kernel-typed `Derivation` (`CutFreeDerivation.infer?_sound`).
- `CutFreeDerivation.elaborate?` returns only when the inferred sequent has a
  kernel-typed derivation, the certificate boundary labels are that same
  sequent, and the reference checker accepted the certificate.
- the post-release parser accepts the canonical serializer for all 250
  generated derivation-tree fixtures and returns the normalized certificate.
- after v0.2.0, bounded vertex reindexing is lossless and forms an explicit
  equivalence relation; structural validation, graph/tree semantics, switching
  correctness, and the final checker are invariant under it.
- v0.3 proves that every `ReindexEquivalent` certificate has the same
  `reindex-v1` serialized key; 250 generated certificates round-trip through
  the native checked parser and an independent audit exercises all 1,000
  committed records under deterministic vertex permutations.
- v0.3.1 proves structural well-formedness gives a complete traversal,
  normalization is an in-class representative, and normal-form equality is an
  iff/decision procedure for the exact order-preserving reindex relation.
- post-v0.3.1 `main` defines a broader `ProofNetEquivalent` relation generated
  by bounded reindexing and link-list permutation. Lean proves that link
  permutation preserves all structural conditions, transports every par
  switching to a tree-equivalent graph, and preserves declarative correctness,
  `Correct`, and the Boolean checker.
- the v0.4 worktree implements checker-gated terminal-par and splitting-tensor
  inverse candidates, with 250 generated nets exposing an accepted recursive
  step; the supporting vertex-deletion graph layer now proves the complete
  theorem that deleting a leaf preserves `IsTree`. Terminal-par preservation is
  complete, and a genuine splitting tensor now produces two universally
  structurally well-formed components whose every switching is an induced
  input restriction and remains an `IsTree`. Checker/declarative preservation
  for this reduction is complete. Universal terminal-par-or-splitting-tensor
  existence, strict decrease of both reductions, and the axiom-only recursive
  base are now kernel checked. Boundary transport and well-founded logical
  recursion are also complete: every accepted certificate has a kernel
  `Derivation` of exactly its ordered conclusion formulas. First-order rule
  tree construction and desequentialized-net equivalence remain open.

## Logical gaps blocking a mature-library claim

1. The safe `elaborate?` return type relates inference, derivation existence,
   certificate boundary labels, and checker acceptance. A general theorem that
   every successfully inferred well-formed rule tree must make `elaborate?`
   succeed is still missing.
2. Logical sequentialization of every accepted MLL proof net is proved, but
   the stronger `GenerallySequentializable` result is not yet complete: the
   current recursion returns a kernel `Derivation`, not a first-order tree
   whose executable desequentialization is proved `ProofNetEquivalent` to the
   input. The generated equivalence is now proved to flatten to one reindexing
   plus link permutation, and `build?`/`infer?` boundary synchronization is
   kernel checked; inverse-rule congruence for reconstructed certificates is
   the remaining mathematical step.
3. The edge-count tree characterization is used correctly, but no explicit
   acyclicity predicate/equivalence theorem is exposed as public API.
4. A semantic relation modulo reordered links is now defined, but it does not
   yet have a complete canonical form or executable decision procedure.
   Conclusion-order canonicalization and arbitrary graph isomorphism remain
   outside the current claim. The v0.3.1 wire theorem remains intentionally
   about the narrower, order-preserving `ReindexEquivalent` relation.

## Engineering gaps blocking a mature-library claim

- v0.2/v0.3 serialization now has a native Lean parser, path-aware parse
  errors, normalization validation, migration, and a checker-gated
  untrusted-input API;
- many APIs return `Option`, losing the location and reason for failure;
- separate path-dependency and clean pinned-v0.2.0 Lake consumers now pass;
  they must remain in CI for future compatibility releases;
- an initial compatibility policy and v0.2-to-v0.3 migration suite now exist;
  long-term API documentation and deprecation automation are still incomplete;
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
- producing stable v0.3 cache/dataset keys across bounded vertex renamings;
- running the focused-search comparison baseline.

It should not yet be presented as:

- a general Lean/mathlib proof assistant extension;
- a complete proof-net-to-first-order-tree sequentializer with certified
  graph reconstruction;
- a complete isomorphism-canonical proof identity library;
- evidence that proof-net generation reduces search redundancy in practice.

## Release gate for library readiness

The macro goal may call the project a library only after all logical gaps above
are closed, a clean downstream Lake consumer passes on Windows and Linux, JSON
round trips have structured diagnostics and fuzz coverage, public API docs and
compatibility rules are published, performance limits are measured, and the
matched experiment reports its result whether positive or negative.
