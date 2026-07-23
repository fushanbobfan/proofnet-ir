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
20. `ProofNetCanonical.lean` enumerates the finite link-order orbit, applies
    the proved v0.3 reindex normal form to every member, and proves that
    extensional family membership is an iff for `ProofNetEquivalent` on
    structurally well-formed certificates. The family is executable but
    factorial in the link count and is intended as a specification oracle.
    The released `proofNetCanonicalFingerprint?` projects this family to its
    lexicographically least v0.3 string. Its totality, candidate membership,
    and forward invariance are proved. `StructuralCode.lean` instead supplies
    an explicitly framed token encoder proved injective, and
    `proofNetCanonicalCode?` minimizes that encoding. Equality of this typed
    code is proved equivalent to `ProofNetEquivalent` on structurally
    well-formed certificates. `CanonicalKeyWire.lean` wraps the exact payload
    in the distinct `proofnet-canonical-key-0.1` JSON contract, enforces bounded
    parsing, supports semantic migration from checked v0.3 certificates, and
    proves that two accepted certificates matching one parsed opaque key are
    equivalent. Public generation and matching check a seven-link ceiling
    before factorial evaluation; the typed unbounded key remains a
    specification oracle.
21. `IntrinsicCanonical.lean` replaces factorial orbit enumeration with an
    ordered occurrence-forest construction. It follows unique producers from
    the ordered conclusions, emits links through orientation-sensitive owners,
    and applies the proved first-occurrence relabeler. Structural
    well-formedness proves exact vertex coverage, exact link permutation, an
    in-class representative, and canonical equality iff
    `ProofNetEquivalent`. `IntrinsicCanonicalKeyWire.lean` gives that code the
    distinct `proofnet-canonical-key-0.2` contract, bounded parser, safe matcher,
    and semantic migration from checker-accepted v0.3 certificates.
22. `ProofNetIdentity.lean` exposes the production pairwise identity boundary
    for checker-accepted certificates. `sameProofNet?` is proved equivalent to
    exactly `ProofNetEquivalent`. Its underlying candidate generator applies
    ordered-conclusion constraints during repeated-label occurrence search,
    and completeness is proved for every direct equivalence witness.

Canonical v0.2 JSON continues to preserve submitted formula-array numbering.
The separate v0.3 key removes that numbering. For structurally well-formed
certificates, Lean proves normalization is an in-class reindexing and that
normal-form equality is equivalent to `ReindexEquivalent`. It is not an
arbitrary graph canonical-labeling algorithm: list order and logical premise
order remain part of identity.

The broader `ProofNetEquivalent` relation has both a complete finite factorial
canonical family/specification oracle and an intrinsic non-factorial canonical
form. In both constructions, link-list storage order is quotiented, while
ordered conclusions, tensor/par premise order, formula labels, and axiom
endpoint orientation remain significant. The old JSON fingerprint has only
the forward equivalence-invariance theorem; both the factorial typed code and
the intrinsic typed code have exact iff theorems. The new direct implementation
does not enumerate permutations and has a conservative `O(VL + V^2)` bound,
but its serialized formula volume and the separate wire envelope still bound
large inputs. Neither construction claims arbitrary graph isomorphism.

The project retains exact pairwise decision as a supported identity API and
adds the intrinsic key as the scalable-by-link-count single-key path. The
v0.1 wrapper remains usable through seven links; the v0.2 wrapper removes that
ceiling and instead applies the common 100,000-token/1,000,000-character
envelope after polynomial generation.
Ordered conclusions, connective premise order, formula labels, and axiom
orientation are still part of identity. Worst-case internal repeated-label
pairwise search, the all-switchings checker, and sequentialization are not made
polynomial by the canonicalizer.

## Why exhaustive switchings first

Exhaustive switching is exponential in the number of par links. It is still the
right reference implementation because it is simple, transparent, and useful
as an oracle for later linear-time or contraction-based checkers. Optimized
recognizers should be tested against this implementation before replacing it.

`Certificate.isCuspAcyclic` is a second reference oracle over the single
unswitched occurrence multigraph. It validates exact simple-cycle traversals
and cyclic local colors, and Lean proves it decides precisely the
`CuspAcyclic` proposition used by the generalized-Yeo splitting development.
The current candidate enumeration is itself exponential. Exact retained-edge
transport and structural producer ownership now prove the acyclicity bridge
in both directions:

```text
StructurallyWellFormed →
  (CuspAcyclic ↔ every occurrence-order switching is Acyclic)
```

This does not yet supply switching connectedness, so it is not a replacement
for the production all-trees checker. No improved asymptotic bound is inferred
from the exhaustive oracle.

The remaining boundary is explicit rather than informal:

```text
check = true ↔
  StructurallyWellFormed ∧
  CuspAcyclic ∧
  AllOccurrenceSwitchingsConnected
```

The proof builds bounded, connected, acyclic retained graphs and transports
their tree property across the exact edge-list permutation used by the public
switching graph. Future contraction work must replace only the final
all-switchings connectedness field.

## Persistent LeanProp bridge

The v0.6-development bridge is a separate typed calculus, not an extension of
the proof-net certificate checker. `LeanProp.Derivation persistent linear goal`
records a Lean proposition goal with two ordered occurrence contexts. Binary
rules concatenate both contexts; persistent weakening and contraction are
explicit; no linear weakening or contraction constructor exists. Exchange is
carried by a proof-relevant `ContextPermutation`, because proposition-level
`List.Perm` cannot be eliminated into the heterogeneous proof-value
environment. Kernel theorems prove the converse at the correct constructive
boundary: `Nonempty (ContextPermutation left right)` is equivalent to
`left.Perm right`, and any such proposition-level permutation makes both
persistent and linear exchange admissible. The dependent proof environment
round trip is identity in both directions.

`LeanProp.Derivation.toProof` recursively interprets every template as a Lean
proof. `linearAxiomCount_eq_length` separately proves exact linear-resource
accounting. Under `#print axioms`, the interpreter is axiom-free; the resource
count and dependent-environment round-trip theorems use exactly `propext`, as
their indices contain propositions. Permutation completeness and the two
exchange-admissibility theorems are axiom-free. Ordinary Lean `And` and
implication are not identified with MLL tensor/par, and this layer does not
alter any v0.5 sequentialization or identity theorem.

`LeanProp.Derivation.normalizePersistentStructural` is a typed recursive
normalizer for the local contraction-over-weakening redex. Its result retains
the identical persistent context, linear context, and goal by construction.
Lean proves that the output contains no such redex, reduced derivations are
fixed points, normalization is idempotent, the persistent structural-node
count does not increase, the linear-axiom count is unchanged, and `toProof`
is preserved pointwise. This is not a claim that all intuitionistic proof
terms are canonical modulo every commuting conversion. The normalizer is a
noncomputable proof-construction API over proposition-indexed derivations;
runtime checking and elaboration of untrusted schema values remain separate.

The proposition-independent `LeanProp.Schema` layer codes atoms, conjunction,
and implication. `Schema.Raw.Derivation` is the unindexed boundary for
generated or otherwise untrusted in-memory templates. Its total `infer?`
checker either reconstructs an exact persistent/linear sequent or returns a
stable `ErrorCode`, detail, and child path. The
`Raw.Derivation.infer?_ofIndexed` theorem proves that erasing a well-indexed
schema and rechecking it recovers the original indices; its exact trust
dependency is `propext`. `Raw.Derivation.elaborate?` additionally builds an
indexed `Schema.Derivation`. The kernel theorem `inferAt_eq_elaborateAt` proves
that inference and elaboration have the same success/failure result and exact
diagnostic after erasing the typed witness, while `elaborate?_complete` proves
every inference acceptance lifts to that witness. The independent
`leanprop-schema-0.1` JSON format has a strict native parser and
`checkedFromString` composes parsing with typed elaboration; the returned
dependent record contains raw syntax, the indexed derivation, and its
elaboration equation. `CheckedDerivation.sound` then reconstructs a Lean proof
under every valuation and matching proof environment. This format is not an
MLL certificate version.

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

The general theorem is now stated and proved against `ProofNetEquivalent`,
which quotients bounded vertex renaming and semantically irrelevant link-list
order while preserving ordered conclusions and connective premises.
`SequentializationResult` connects first-order inference, a kernel-typed
derivation, executable desequentialization, ordered boundary labels, and an
equivalent output certificate. `sequentialization_of_check` constructs that
result for every checker-accepted certificate, and
`generallySequentializable` exposes the proposition-level theorem.

`ExecutableSequentialization.lean` supplies a separate computational path. It
enumerates checker-preserving terminal-par and splitting-tensor inverses with
an occurrence-count fuel bound. At each rebuilt node it enumerates all boundary
permutations compatible with formula labels, independently infers and
desequentializes the tree, reruns the checker, and requires the executable
direct proof-net-equivalence search to find a bounded vertex renaming followed
by a link permutation. A returned
`ExecutableSequentializationResult` therefore carries a kernel derivation and
an exact `ProofNetEquivalent` output proof. The broader relation is necessary:
the checker deliberately ignores link-list storage order, and an early
`ReindexEquivalent`-only prototype failed on a reversed-link-order accepted
certificate. `Certificate.sequentialize_complete` proves totality of this
particular runtime search for every checker-accepted input. Its proof connects
the terminal-rule dichotomy and checker-gated inverse candidates to complete
par/tensor rebuilding, exhaustive boundary alignment, and a strict
formula-occurrence fuel induction.

`DerivationVerifier.lean` and `ReconstructionChecker.lean` provide the
v0.9 alternative path. The verifier turns a proposed tree into a dependent
proof-bearing result using only structural validation, inference,
desequentialization, and intrinsic canonical-code equality. The reconstruction
layer has two executable tiers. A structure-guided fast path recursively
combines raw terminal-par and splitting-tensor candidates, uses
vertex-number-free boundary formula-tree/axiom profiles to align repeated
occurrences, and invokes the verifier once on the completed tree. If that
heuristic result is absent or rejected, the original recursively verified
exhaustive path remains the fallback. Neither tier calls the all-switchings
checker. Fuel completeness of the fallback and proof-bearing soundness combine
into the kernel theorem `Certificate.reconstructsDerivation_eq_check`.
Fallback backtracking and formula-order enumeration remain explicit
worst-case performance concerns.

`reconstructDerivationWithinLimits` is the fail-closed public resource
boundary around the fast tier. It checks configurable formula-occurrence,
link, and conclusion ceilings before search and never enters the exhaustive
fallback. Its structured limit and heuristic errors are intentionally
inconclusive, while every `.ok` result has the same dependent soundness
contract and is proved accepted by the exact reference semantics. The
qualified 128/96/24 default is a tested input envelope, not a wall-clock or
polynomial complexity theorem.

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
is formalized: structural ownership and par-choice counting prove that a
terminal par conclusion is a leaf in every switching. On the structural side,
the pure reduction is now
proved equal to the executable candidate on well-formed terminal pars; formula
lookup under compaction, nonempty and bounded duplicate-free boundary output,
local well-formedness of every surviving link, and global node ownership are
all kernel theorems; hence the complete proposition-level structural
specification is preserved. Choice lifting now also proves every premise
switching is the terminal-leaf deletion of an input switching up to edge-order
permutation, so terminal-par correctness preservation is complete.

For the tensor branch, the local theorem layer now proves unique conclusion
ownership, absence of any other incident link, non-boundary premises, zero
incident selected-par edges, and exactly the two fixed tensor edges at the
terminal conclusion in every switching. Thus terminal tensor degree is
universally two. A genuine splitting tensor now yields two structurally
well-formed restricted certificates. Every child switching is now an induced
restriction of an input switching and is proved to remain a tree. The
generalized-Yeo layer proves that when no terminal par is available, a
splitting terminal tensor exists.

`SplittingTensor` now states that global condition without mentioning the
algorithm: after removing the terminal conclusion from the full occurrence
graph, no graph walk connects its two premises. The full occurrence graph is
proved bounded from certificate structural well-formedness, and a general
finite-graph theorem proves `vertexCount` closure rounds equivalent to the
unbounded `Walk` relation. Consequently the candidate finder's reachability
rejection is sound and complete for this exact splitting condition; universal
existence follows from the proved terminal-rule dichotomy.

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
tensor conclusion, so both induced graphs are bounded and connected. A finite
connected-graph parent-edge theorem supplies the lower edge bounds; exact
vertex and edge partitions then force `E + 1 = V` in both components. Thus the
concrete `TerminalTensorReduction` preserves declarative correctness and the
Boolean checker for both premises. Exact occurrence-boundary reconstruction,
block-sum renaming, and binary inverse-rule composition rebuild a concrete
first-order tensor tree equivalent to the input. Together with the terminal-par
branch, strict decrease, and axiom base, this closes the well-founded
sequentialization proof.

## v0.2 derivation-first path

`DerivationTree.lean` represents arbitrary first-order cut-free rule trees.
Tensor/par nodes name the resource positions they consume and exchange nodes
store a full occurrence permutation. `build?` validates those choices while
constructing a net fragment; `desequentialize?` emits the certificate and
`desequentializeChecked?` returns it only with a proof of checker acceptance.
The kernel theorem `infer?_eq_some_iff_build?_conclusions` proves that the
independent formula pass and occurrence-aware builder have exactly the same
success domain and ordered formula boundary. Its exchange case works at the
index level, so duplicate formula labels do not require an invalid projection-
injectivity assumption. `GraphComposition.lean`,
`SwitchingComposition.lean`, and `StructuralComposition.lean` separately prove
that axiom/par/tensor/exchange construction preserves the graph-tree and full
structural certificate invariants. `DesequentializationSoundness.lean`
combines those results with the formula-table invariant: every successful
public desequentialization has the source tree's exact ordered boundary, is
declaratively correct, and is accepted by the executable checker.
Consequently `desequentializeChecked?` and `elaborate?` are total whenever the
independent `infer?` pass succeeds.

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
