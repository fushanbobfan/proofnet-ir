# Architecture

## Design objective

ProofNet-IR separates proof proposal from proof checking. A model proposes a
certificate; deterministic Lean code validates its local typing and global
switching behavior; a sequentializer reconstructs an object-logic derivation;
the Lean kernel checks the final artifact.

The v0.1 fragment is cut-free, unit-free multiplicative linear logic. This is
the smallest setting in which proof nets have a nontrivial global correctness
criterion and proof-order bureaucracy can be measured cleanly.

## Data flow

1. `Formula` represents atoms with polarity, tensor, and par.
2. `Certificate.formulas` gives formula occurrences stable numeric identities.
3. `Link` records axiom pairings and tensor/par construction links.
4. `Certificate.wellFormed` checks local duality, connective labels, unique
   producers, unique axiom use, parent use, and conclusion boundaries.
5. `fixedEdges` emits axiom and tensor graph edges.
6. `parChoices` emits the two possible premise edges of each par link.
7. `switchingGraphs` exhaustively enumerates the resulting `2^k` graphs.
8. `ChoiceSelection` independently states that exactly one edge was chosen for
   each par link; `mem_switchingGraphs_iff` proves exact enumeration coverage.
9. `Graph.isTree` checks every switching.
10. `Graph.reachable_sound` proves computed reachability yields an inductive
   `Graph.Walk`, independent of the closure implementation.
11. `Graph.closureN_walkWithin` translates finite closure membership into an
    independent `WalkN` whose edge count is at most the supplied fuel.
12. `Graph.walkN_mem_closureN` and `mem_closureN_mono` prove the converse for
    bounded stored edges.
13. `isTree_iff_fuelTree` lifts the correspondence to the executable tree
    predicate.
14. `Certificate.check` accepts only when both local and global checks pass.
15. `check_sound_declarative` transports executable acceptance into the
    independent switching semantics;
    `check_iff_fuelDeclarativelyCorrect` additionally gives soundness and
    completeness for both the independent switching and path semantics.

## Why exhaustive switchings first

Exhaustive switching is exponential in the number of par links. It is still the
right reference implementation because it is simple, transparent, and useful
as an oracle for later linear-time or contraction-based checkers. Optimized
recognizers should be tested against this implementation before replacing it.

## Sequentialization boundary

`Reconstruct.lean` includes an explicit exchange rule with a `List.Perm`
witness. `Derivation.identity` then recursively constructs a kernel-checked
derivation of

```text
|- A, A-dual
```

for every formula in the unit-free MLL syntax. `Generate.lean` mirrors this
derivation recursively to build a canonical identity certificate, and
`reconstructIdentity?` gates reconstruction on exact certificate equality.
Consequently, the supported family now has arbitrary formula depth rather than
only two hand-written examples.

This still does not claim the general sequentialization theorem: an arbitrary
accepted proof net need not be a canonical identity net. The next formal step
is to represent the splitting-tensor argument and recursively turn every
accepted net into a `Derivation`, modulo explicit exchange.

## Representation invariants

- Formula occurrences, not formula strings, are the graph vertices.
- Axiom links connect distinct dual atomic occurrences.
- Tensor and par links must agree with the formula stored at their conclusion.
- Atomic occurrences participate in exactly one axiom link.
- Composite occurrences have exactly one producer link.
- Non-conclusions are used exactly once as a logical premise.
- Conclusions are distinct and are not used as premises.
- Every switching edge is in bounds and non-reflexive.

These invariants are deliberately explicit so that future JSON or AI-generated
certificates cannot smuggle malformed graph structure past the checker.
