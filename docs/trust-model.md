# Trust model

## Trusted

- the Lean 4 kernel selected by `lean-toolchain`;
- the compiled definitions and theorems in this repository, after `lake build`;
- the small object-logic derivation type used for supported reconstruction.

## Untrusted

- an AI model or graph neural network proposing certificates;
- prompts, retrieved text, local-model summaries, and imported papers;
- a future Python/TypeScript dataset generator or visualizer;
- a future JSON parser until its output is revalidated in Lean;
- benchmark labels not regenerated from checked certificates;
- the high-level claim that proof geometry improves proof search.

## Current theorem boundary

`Certificate.check_sound` states that executable acceptance implies:

1. structural `wellFormed` acceptance;
2. every enumerated switching satisfies `Graph.IsTree`.

`Graph.IsTree` is a proposition over bounded edges, an independent inductive
`Graph.Walk` from vertex zero to every in-bounds vertex, and the edge-count
equation. `reachable_sound` proves that membership in the finite closure really
produces such a walk; the proof proceeds through closure preservation and does
not define a walk to mean "the algorithm returned true."

`WalkN` is a second independent relation indexed by its exact number of edge
steps. `closureN_walkWithin` and `walkN_mem_closureN` prove that finite closure
at depth `fuel` is equivalent to the existence of a path of at most `fuel`
steps, provided stored edges are in bounds. `isTree_iff_fuelTree` and
`check_iff_fuelCorrect` lift this to the complete graph and certificate
checkers.

The stronger normalization theorem saying that every arbitrary `Graph.Walk`
in an `n`-vertex graph has an equivalent walk of at most `n` steps remains
open. This no longer weakens completeness for `FuelCorrect`, but it is needed
to identify the original unbounded `Correct` predicate with `FuelCorrect`.
None of these results is the proof-net sequentialization theorem.

The supported reconstruction boundary is broader than a fixed fixture but
still explicit: `Derivation.identity` and `identityCertificate` cover the
recursive family `A, A-dual`, and `reconstructIdentity?` requires exact
certificate equality. It does not treat checker acceptance alone as permission
to return a preselected derivation.

## Failure containment

Even if a future graph proposer, optimized checker, or sequentializer is wrong,
the final Lean proof must still elaborate and pass the kernel. Experimental
metrics must distinguish:

- syntactically valid JSON;
- structurally well-formed certificates;
- switching-valid certificates;
- sequentialization success;
- Lean kernel success.

Collapsing these stages into a single "solved" label would hide the project's
most useful diagnostic signal.
