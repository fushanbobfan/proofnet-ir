# Mathematical and implementation audit of v0.1.0

Date: 2026-07-21  
Audited release: `v0.1.0`, commit `756545b3cde6c8154484fedd38909e42d68dcf86`

## Verdict

No certificate or graph whose mathematical classification disagreed with the
v0.1.0 executable checker was found. Within its declared scope—unit-free,
cut-free multiplicative linear logic without Mix—the checker implements the
Danos–Regnier correctness criterion: every formula occurrence is used exactly
once according to its link type, and every graph obtained by retaining exactly
one premise edge at each par link is a tree.

The audit found one assurance gap, not a behavioral counterexample. Formula
Boolean equality was automatically generated but did not expose a
`LawfulBEq Formula` instance to proofs, and the structural half of
`DeclarativelyCorrect` still referred to `wellFormed = true`. The patch release
uses the lawful equality derived from `DecidableEq`, introduces independent
propositions `LinkWellFormed`, `NodeWellFormed`, and
`StructurallyWellFormed`, and proves the executable structural checker
equivalent to that specification. The complete checker theorem now has a
Boolean-free structural premise.

## Mathematical scope checked

| Component | Required meaning | Evidence |
|---|---|---|
| Formula | Atoms with polarity; tensor/par; involutive De Morgan dual | `Formula.dual_dual`; generated identity corpus |
| Axiom link | Two distinct atomic dual occurrences | `LinkWellFormed`; Boolean/specification iff |
| Tensor/par link | Distinct premise/conclusion occurrences and exact conclusion label | `LinkWellFormed`; Boolean/specification iff |
| Linear resource use | Each atom has one axiom source; each compound has one producer; every non-conclusion has one parent; every conclusion has none | `NodeWellFormed`; `wellFormed_iff_structurallyWellFormed` |
| Switching | Exactly one premise edge retained for each par link | independent inductive `ChoiceSelection`; `mem_switchingGraphs_iff` |
| Tree | Nonempty bounded loop-free undirected graph, connected, with `|E| = |V| - 1` | independent `Walk`/`WalkN` semantics; executable iff for `FuelTree` |
| Certificate acceptance | Structural specification and every switching tree | `check_sound_declarative`; `check_iff_fuelDeclarativelyCorrect` |
| Reconstruction | Only exact certificates in the documented recursive identity family | `reconstructIdentity?_isSome_iff`; negative gate tests |

The edge-count characterization is valid for finite undirected multigraphs:
connectedness plus `|E| = |V| - 1`, after excluding loops and out-of-bounds
endpoints, is equivalent to being a tree. Parallel edges are counted with
multiplicity and therefore cannot pass the two-vertex tree case; an explicit
regression test covers this boundary.

## Differential tests

`python scripts/audit_v010.py` obtains subject results from compiled Lean
executables and compares them with code that does not import or translate the
Lean graph traversal:

- all 33,868 simple undirected labeled graphs with zero through six vertices;
- a union-find tree oracle that rejects cycles while constructing components;
- 1,000 proof-net certificates from 250 generated formulas, consisting of a
  valid identity certificate and three independently labeled corruptions per
  formula;
- an independent certificate oracle for duality, link labels, occurrence
  ownership, conclusion discipline, all par switchings, and union-find trees.

The audit fails on the first disagreement and is a required GitHub CI step.
The observed result was:

```text
ProofNet-IR differential audit passed: 33868 exhaustive graphs, 1000 certificates
```

## Findings

### AUD-001: declarative structural contract retained a Boolean premise

- Severity: assurance defect; no observed acceptance/rejection defect.
- v0.1.0 behavior: `DeclarativelyCorrect` used `wellFormed = true` for local
  structure while giving independent propositions only for switching and
  graph reachability.
- Resolution: added proposition-level link, node, and certificate structure
  definitions and proved them equivalent to the executable checks. Formula
  equality now uses the lawful comparison generated from `DecidableEq`.
- Regression: the canonical certificate is proved
  `StructurallyWellFormed`; full build and both differential corpora pass.
- Status: resolved.

No unresolved mathematical correctness finding remains from this audit.

## Deliberate boundaries, not defects

- The theorem equating arbitrary unbounded `Walk` connectivity with the
  `vertexCount`-fuel relation is not yet formalized. Accepted certificates are
  nevertheless sound for unbounded `Graph.IsTree`, and the checker has an iff
  theorem for the independently defined bounded-path contract.
- v0.1.x does not sequentialize every correct net. Reconstruction is exact and
  intentionally limited to canonical identities; it never substitutes a
  preselected derivation merely because an arbitrary certificate passed.
- Units, Mix, cut, additives, exponentials, quantifiers, proof-net
  isomorphism, and performance claims remain outside this release.

These boundaries are explicit so that an implementation test cannot be
mistaken for the still-future general sequentialization theorem.

## Post-release resolution on main

Post-v0.2 `main` closes the first deliberate boundary without changing the
historical v0.1.0 artifact. `Walk.toSimple` performs loop erasure and
`SimpleWalk.toWalkWithin` proves the `vertexCount` bound for bounded graphs.
The resulting `check_iff_declarativelyCorrect` is a kernel-checked completeness
theorem for the original unbounded contract. General proof-net
sequentialization remains open.
