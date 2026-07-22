# Changelog

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
