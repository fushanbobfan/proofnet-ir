# Roadmap

## v0.1 - Verified MLL reference core

- [x] Pin Lean 4 toolchain.
- [x] Define unit-free MLL formulas and involutive negation.
- [x] Define formula occurrences and axiom/tensor/par links.
- [x] Check local structural invariants.
- [x] Enumerate all switchings.
- [x] Implement the reference tree checker.
- [x] Prove semantic soundness against an independent inductive walk relation.
- [x] Prove completeness/iff for the exact finite-computation contract.
- [x] Reconstruct one supported canonical sequent derivation.
- [x] Add at least 20 compile-time positive/negative assertions.
- [x] Add a versioned JSON Schema and fixtures.
- [x] Prove finite closure membership implies an inductive graph walk.
- [ ] Prove every in-bounds graph walk is found by finite closure.
- [ ] Prove general sequentialization for the supported representation.
- [ ] Add generated proof-tree-to-net fixtures and mutation tests.

## v0.2 - Dataset and repair loop

- Generate valid derivation trees first, then desequentialize to proof nets.
- Produce labeled invalid mutations: non-dual axiom, missing edge, duplicated
  resource, cycle, disconnection, and wrong connective attachment.
- Canonicalize certificates and define graph edit operations.
- Compare direct sequent generation, graph generation, and graph repair.
- Report validity, repair success, Lean calls, token cost, and redundancy
  collapse without claiming theorem-proving gains before measurement.

## v0.3 - Persistent LeanProp bridge

- Add a two-context design for persistent and linear hypotheses.
- Make weakening and contraction explicit.
- Support conjunction, implication, equality rewriting, universal
  instantiation, and existential witness nodes.
- Reconstruct Lean proof terms for a generated template corpus.

## Later research

- certified contraction/linear-time correctness checking;
- cut links and cut elimination as graph rewriting;
- additives, exponentials/boxes, and unification nets;
- hierarchical proof graphs for dependency-rich mathlib theorems;
- a `proofnet_ai` tactic that treats all model output as untrusted input.

The success criterion is empirical and kernel-checked. A visually appealing
graph or a lower token count without matched proof success is not enough.
