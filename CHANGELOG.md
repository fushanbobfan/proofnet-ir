# Changelog

## Unreleased

- added an independent conclusion-inference pass for first-order derivation
  trees and proved `infer?_sound`: every successful inference denotes a
  kernel-typed `Derivation`;
- strengthened explicit exchange validation with a checked `List.Perm`
  boundary and `reorder?_perm` theorem;
- added `elaborate?`, whose result connects the inferred sequent, a
  kernel-typed derivation, matching proof-net conclusion labels, and checker
  acceptance in one public boundary;
- added honest source-coverage and library-readiness audits so targeted reading
  and research-prototype functionality cannot be presented as completion.
- added a separate downstream Lake consumer that imports the public library,
  exercises certificate checking and `elaborate?`, and runs in CI.
- recorded a representation-level comparison with the primary Rocq proof-net
  formalization to guide sequentialization without silently copying a theorem
  for a different graph model.
- added a native Lean parser for canonical v0.2 JSON, path-aware parse errors,
  canonical-form validation, and a safe checked-input boundary for untrusted
  external certificates.

## v0.2.0 - Derivation trees, canonical data, and focused baseline

### Included

- first-order arbitrary cut-free MLL derivation trees with explicit resource
  positions and exchange permutations;
- validated general desequentialization from those trees to proof-net
  certificates, plus a checked result that carries `certificate.check = true`;
- a deterministic derivation generator whose first 250 depth-two trees all
  desequentialize and pass the reference checker;
- versioned canonical certificate JSON that normalizes link order, conclusion
  order, and symmetric axiom orientation while preserving formula-array vertex
  identities;
- a committed, deterministic 1,000-record JSONL dataset with 250 valid
  derivation outputs and 750 labeled corruptions, checked again by the
  independent Python oracle;
- a runnable focused cut-free one-sided MLL search baseline with eager par
  decomposition, exhaustive tensor/resource-split search, memoization, and
  search counters;
- schemas, dataset manifest/checksum, regeneration checks, smoke fixtures, and
  GitHub CI coverage for the entire path.

### Explicit boundaries

- canonical serialization is not graph-isomorphism canonicalization;
- desequentialization is general, but reverse sequentialization of every
  checker-accepted proof net is still not implemented;
- the dataset is a correctness/repair substrate, not evidence that graph
  generation outperforms focused proof search.

## v0.1.1 - Mathematical audit hardening

### Changed

- audited the compiled checker against an independent Python oracle on all
  33,868 simple undirected graphs through six vertices and 1,000 generated or
  mutated proof-net certificates;
- added proposition-level link, node, and certificate structural semantics and
  proved `wellFormed_iff_structurallyWellFormed`;
- strengthened `DeclarativelyCorrect` and `FuelDeclarativelyCorrect` so their
  structural premise no longer calls the Boolean checker;
- changed formula Boolean equality to the lawful instance derived from
  `DecidableEq`;
- added multigraph parallel-edge regression coverage and made the audit a
  required CI step.

No v0.1 certificate schema or accepted-fragment semantics changed.

## v0.1.0 - Verified MLL reference core

### Included

- pinned Lean 4.32.0 toolchain and reproducible Lake build;
- unit-free, cut-free MLL formulas, occurrences, axiom/tensor/par links, and
  structural certificate checks;
- exhaustive par-switching enumeration plus an independent inductive
  one-edge-per-par selection semantics;
- finite graph tree checking with independent unbounded and fuel-indexed walk
  semantics;
- checker soundness for declarative switching correctness and soundness/
  completeness for the independent fuel-indexed contract;
- explicit exchange and recursive identity derivations for `A, A-dual`;
- recursive canonical identity-certificate generation and certificate-gated
  reconstruction;
- labeled invalid mutations, 61 compile-time assertions, and a 210-formula
  generated sanity corpus;
- versioned JSON Schema and valid/invalid fixtures;
- CI, architecture, trust-boundary, literature, experiment, and reading-ledger
  documentation.

### Explicit non-goals

- general sequentialization of every accepted MLL proof net;
- a proof that every unbounded walk normalizes within `vertexCount` steps;
- units, Mix, cut, additives, exponentials, quantifiers, or a Lean tactic;
- a claim that graph generation outperforms focused sequent proof search.

These items remain tracked in `docs/roadmap.md` and are not implied by the
v0.1.0 release label.
