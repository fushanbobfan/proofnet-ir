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
19. `NetEquivalence.lean` proves that permuting the link list transports every
    par switching to an edge-permutation-equivalent graph and therefore leaves
    the checker unchanged. `ProofNetEquivalent` combines this storage-order
    quotient with bounded vertex renaming for the sequentialization boundary.

Canonical v0.2 JSON continues to preserve submitted formula-array numbering.
The separate v0.3 key removes that numbering. For structurally well-formed
certificates, Lean proves normalization is an in-class reindexing and that
normal-form equality is equivalent to `ReindexEquivalent`. It is not an
arbitrary graph canonical-labeling algorithm: list order and logical premise
order remain part of identity.

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
accepted proof net need not be a canonical identity net. The new
`ProofNetEquivalent` relation fixes the previously too-narrow conclusion type
by quotienting link storage order. The next formal step is to represent the
splitting-tensor argument and recursively turn every accepted net into a
`Derivation`, modulo explicit exchange, whose desequentialization is
`ProofNetEquivalent` to the input.

`Sequentialization.lean` now makes that final result type explicit: a successful
result must connect first-order inference, a kernel-typed derivation,
desequentialization, ordered boundary labels, and `ProofNetEquivalent` output.
It also implements vertex deletion/compaction and a checker-gated inverse for
terminal par links. All terminal-par candidates found across the 250 generated
derivation-tree regressions produce accepted premises. This is implementation
and regression evidence; the universal preservation theorem remains open.

The same module now discovers terminal splitting-tensor candidates by deleting
the tensor conclusion in the full occurrence graph, partitioning reachable
vertices, rejecting every cross-component link, locally renumbering both
components, and accepting the split only if both reference checks pass. Across
the 250 generated non-axiom nets, at least one accepted inverse par or tensor
step is found. The graph proof layer already establishes deletion compaction,
boundedness preservation, exact incident-edge accounting, the tree edge-count
equation for a deleted leaf, exact adjacency/walk embedding, simple-walk leaf
avoidance, connectedness after deletion, and the full `IsTree` preservation
theorem. Transporting each terminal-par switching to this general graph lemma
is now halfway formalized: structural ownership and par-choice counting prove
that a terminal par conclusion is a leaf in every switching. Exact equality up
to edge order between the generated premise switching and the deleted input
switching remains open. On the structural side, the pure reduction is now
proved equal to the executable candidate on well-formed terminal pars; formula
lookup under compaction, nonempty and bounded duplicate-free boundary output,
local well-formedness of every surviving link, and global node ownership are
all kernel theorems; hence the complete proposition-level structural
specification is preserved. Choice lifting now also proves every premise
switching is the terminal-leaf deletion of an input switching up to edge-order
permutation, so terminal-par correctness preservation is complete. The
universal existence of a splitting tensor and tensor-component switching
preservation remain current proof obligations.

For the tensor branch, the local theorem layer now proves unique conclusion
ownership, absence of any other incident link, non-boundary premises, zero
incident selected-par edges, and exactly the two fixed tensor edges at the
terminal conclusion in every switching. Thus terminal tensor degree is
universally two. A genuine splitting tensor now yields two structurally
well-formed restricted certificates; proving that some terminal tensor is
splitting and that both restrictions preserve every switching is the next
global combinatorial step.

`SplittingTensor` now states that global condition without mentioning the
algorithm: after removing the terminal conclusion from the full occurrence
graph, no graph walk connects its two premises. The full occurrence graph is
proved bounded from certificate structural well-formedness, and a general
finite-graph theorem proves `vertexCount` closure rounds equivalent to the
unbounded `Walk` relation. Consequently the candidate finder's reachability
rejection is sound and complete for this exact splitting condition; universal
existence remains a separate obligation.

The component constructor is now connected to that semantics as well. The
reachable and unreachable vertex lists are proved disjoint and exhaustive off
the removed conclusion. Internal full-graph walks force every remaining link
to lie wholly in one component, so the executable no-crossing guard is a
theorem for every splitting tensor. Both component boundaries are contained in
their vertex lists, making formula lookup and `idxOf?` reindexing total; hence
`splitTerminalTensorCandidate?` is proved to return two certificates. Exact
restriction equations, formula/index transport, local link typing, boundary
discipline, source ownership, and parent-use accounting prove both returned
certificates `StructurallyWellFormed`. Every switching of either child is now
proved to be the induced occurrence restriction of an input switching. The
separator proof shows same-side simple paths cannot traverse the terminal
tensor conclusion, so both induced graphs are bounded and connected. The exact
edge-count equation, and hence full `IsTree` preservation, remains the next
tensor obligation.

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
Structural ownership proves every formula vertex occurs in the traversal;
`traversalRelabel_eq_reindex` constructs the induced renaming, and
`reindexEquivalent_iff_equivalenceCanonicalize_eq` proves completeness.
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
