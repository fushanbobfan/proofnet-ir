# Architecture

## Design objective

ProofNet-IR separates proof proposal from proof checking. A model proposes a
certificate; deterministic Lean code validates its local typing and global
switching behavior; supported reconstruction or derivation-first generation
produces an object-logic artifact; the Lean kernel checks the final artifact.

The v0.1 fragment is cut-free, unit-free multiplicative linear logic. This is
the smallest setting in which proof nets have a nontrivial global correctness
criterion and proof-order bureaucracy can be measured cleanly.

## Data flow

1. `Formula` represents atoms with polarity, tensor, and par.
2. `Certificate.formulas` gives formula occurrences stable numeric identities.
3. `Link` records axiom pairings and tensor/par construction links.
4. `Certificate.wellFormed` checks local duality, connective labels, unique
   producers, unique axiom use, parent use, and conclusion boundaries.
   `wellFormed_iff_structurallyWellFormed` identifies this executable pass with
   its proposition-level specification.
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
13. `SimpleWalk` loop erasure proves that an arbitrary bounded inductive walk
    has an equivalent duplicate-free path within the `vertexCount` budget.
14. `isTree_iff_isTree` lifts the correspondence to the public unbounded tree
    predicate.
15. `Certificate.check` accepts only when both local and global checks pass.
16. `check_iff_declarativelyCorrect` proves soundness and completeness for the
    Boolean-free structural, independent switching, and unbounded path
    semantics. The fuel-indexed iff remains as a second executable contract.
17. `Reindex.lean` transports certificates and switching graphs along bounded
    vertex bijections. `check_reindex` proves exact Boolean invariance, while
    `ReindexEquivalent` packages renaming as an equivalence relation preserving
    executable and declarative correctness.
18. `Serialization.lean` discovers vertices from ordered conclusions and links
    and assigns first-occurrence indices. `equivalenceCanonicalString_reindex`
    proves that the v0.3 `reindex-v1` key is invariant under every admissible
    bounded vertex renaming.

Canonical v0.2 JSON continues to preserve submitted formula-array numbering.
The separate v0.3 key removes that numbering. It is not an arbitrary graph
canonical-labeling algorithm: list order and logical premise order remain part
of identity, and the converse from equal keys to `ReindexEquivalent` is not yet
kernel-proved.

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

## v0.2 derivation-first path

`DerivationTree.lean` represents arbitrary first-order cut-free rule trees.
Tensor/par nodes name the resource positions they consume and exchange nodes
store a full occurrence permutation. `build?` validates those choices while
constructing a net fragment; `desequentialize?` emits the certificate and
`desequentializeChecked?` returns it only with a proof of checker acceptance.

`Serialization.lean` supplies the versioned canonical wire format under fixed
formula-array vertex numbering. `ProofNetIRDataset.lean` deterministically
emits the 1,000-record corpus, while the Python wrapper checks every label with
an independent oracle. The focused Python baseline is deliberately separate
from this trust path.

## v0.3 reindex wire path

`traversalVertices` visits ordered conclusions and then ordered link vertices.
`traversalRelabel` uses first-occurrence positions as new names. The reindexing
proof shows this traversal commutes exactly with every `VertexRenaming`, so the
serialized v0.3 value is a stable key across submitted vertex permutations.
The parser retains both wire versions, and migration validates v0.2 before
emitting v0.3. Logical validity remains a separate checker-gated boundary.

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
