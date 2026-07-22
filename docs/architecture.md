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
8. `Graph.isTree` checks every switching.
9. `Graph.reachable_sound` proves computed reachability yields an inductive
   `Graph.Walk`, independent of the closure implementation.
10. `Certificate.check` accepts only when both local and global checks pass.
11. `check_sound` transports executable acceptance into `Certificate.Correct`.

## Why exhaustive switchings first

Exhaustive switching is exponential in the number of par links. It is still the
right reference implementation because it is simple, transparent, and useful
as an oracle for later linear-time or contraction-based checkers. Optimized
recognizers should be tested against this implementation before replacing it.

## Sequentialization boundary

`Reconstruct.lean` currently supplies kernel-checked derivations for canonical
two- and three-axiom nested tensor/par families. The smallest family has the
shape

```text
|- p tensor q, p-dual par q-dual.
```

`reconstructCanonical?` also gates the two-axiom reconstruction on exact
certificate matching, so an arbitrary certificate cannot be ignored while a
fixed derivation is returned. This still does not claim a general
sequentialization theorem. The next formal step is to add exchange/permutation
explicitly and prove that every accepted net in the supported certificate
representation yields a `Derivation`.

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
