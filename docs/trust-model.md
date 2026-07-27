# Trust model

## Trusted

- the Lean 4 kernel selected by `lean-toolchain`;
- the compiled definitions and theorems in this repository, after `lake build`;
- the small object-logic derivation type used for supported reconstruction.
- the `CutFreeDerivation` rule syntax only after its occurrence positions and
  explicit exchange have passed `build?`;
- the proof carried by `desequentializeChecked?` that the resulting
  certificate passed the reference checker.

## Untrusted

- an AI model or graph neural network proposing certificates;
- prompts, retrieved text, local-model summaries, and imported papers;
- a future Python/TypeScript dataset generator or visualizer;
- the Python focused-search baseline and dataset regeneration wrapper;
- external JSON and the parsing path; callers should use
  `Certificate.checkedFromString`, whose return value includes the revalidated
  Lean checker acceptance proof;
- generated or external unindexed LeanProp schemas; callers must pass them
  through `LeanProp.Schema.Raw.Derivation.elaborate?` before treating them as
  typed derivations; `infer?` alone exposes only the formula boundary;
- LeanProp schema JSON and its parser; callers should use
  `LeanProp.Schema.Raw.Derivation.checkedFromString`, whose result retains a
  successful indexed elaboration and exposes `CheckedDerivation.sound`;
- benchmark labels not regenerated from checked certificates;
- the high-level claim that proof geometry improves proof search.

## Current theorem boundary

`Certificate.check_sound_declarative` states that executable acceptance
implies:

1. the Boolean-free `StructurallyWellFormed` proposition, including local link
   legality and exact occurrence ownership;
2. every graph satisfying the independent inductive `ChoiceSelection`
   switching relation satisfies `Graph.IsTree`.

`wellFormed_iff_structurallyWellFormed` proves that the executable structural
pass is sound and complete for independent proposition-level definitions of
link, node, conclusion, and resource-use discipline. Formula Boolean equality
is supplied by `DecidableEq`, so Lean also has its `LawfulBEq` proof.

`mem_switchingGraphs_iff` proves that the executable enumeration contains
exactly those independently described switchings, closing the risk that an
enumerator bug could silently omit a par choice from the semantic contract.

`Graph.IsTree` is a proposition over bounded edges, an independent inductive
`Graph.Walk` from vertex zero to every in-bounds vertex, and the edge-count
equation. `reachable_sound` proves that membership in the finite closure really
produces such a walk; the proof proceeds through closure preservation and does
not define a walk to mean "the algorithm returned true."

`WalkN` is a second independent relation indexed by its exact number of edge
steps. `closureN_walkWithin` and `walkN_mem_closureN` prove that finite closure
at depth `fuel` is equivalent to the existence of a path of at most `fuel`
steps, provided stored edges are in bounds. `isTree_iff_fuelTree` and
`check_iff_fuelDeclarativelyCorrect` lifts both independent relations to the
complete certificate checker.

`Walk.toSimple` now erases loops from every arbitrary `Graph.Walk`.
`SimpleWalk.toWalkWithin` uses duplicate-free vertex counting to bound the
result by `vertexCount` when stored edges are bounded. Consequently
`connected_iff_connected`, `isTree_iff_isTree`, `check_iff_correct`, and
`check_iff_declarativelyCorrect` identify the executable checker with the
original unbounded public semantics. None of these results is the proof-net
sequentialization theorem.

An independent differential audit additionally compares the compiled checker
against a Python union-find/certificate oracle on every simple graph through
six vertices and 1,000 generated or mutated certificates. See
`docs/audit-v0.1.0.md`; this is regression evidence, not part of the trusted
kernel proof.

The supported reconstruction boundary is broader than a fixed fixture but
still explicit: `Derivation.identity` and `identityCertificate` cover the
recursive family `A, A-dual`, and `reconstructIdentity?` requires exact
certificate equality. It does not treat checker acceptance alone as permission
to return a preselected derivation.

v0.2 added the derivation-first direction for arbitrary first-order cut-free
trees: validated desequentialization constructs a candidate certificate and
gates the checked API on `Certificate.check = true`. The post-v0.5
`infer?_eq_some_iff_build?_conclusions` theorem proves that formula validation
and occurrence-aware construction succeed together. The subsequent
`desequentialize?_conclusionFormulas?` theorem proves that every successfully
constructed public certificate reads back exactly the inferred ordered
boundary. The composition proofs now additionally establish structural
well-formedness and every-switching tree correctness for every successful
build; `build?_check` and `desequentialize?_check` derive executable checker
acceptance rather than assuming it. The checked gate remains explicit in the
runtime API, while `desequentializeChecked?_exists_of_infer?` and
`elaborate?_exists_of_infer?` prove it cannot fail after successful `infer?`.
Release v0.4.0
also proves the reverse direction for the supported representation:
`sequentialization_of_check` maps every accepted certificate to a concrete
first-order tree whose executable output is `ProofNetEquivalent` to the
input. The theorem preserves the ordered formula boundary and does not identify
arbitrary unlabeled graphs. The v0.5 runtime path is independently tied to
that guarantee: `sequentialize_complete` proves that the public finite search
returns a proof-bearing result on every checker-accepted certificate.
The v0.9 development path separates verification from the reference checker:
`verifyDerivation?` checks a supplied tree through structural validation,
independent inference/desequentialization, and the non-factorial intrinsic
canonical code. `reconstructDerivation?` performs fuel-bounded terminal-rule
search and calls that verifier, never `Certificate.check`. Kernel theorems
prove every successful result accepted and prove the exact total decision
equality `reconstructsDerivation = check`. The proof may use the reference
semantics; the compiled search definition does not. No polynomial or linear
runtime theorem is currently claimed.

`unificationReconstruct?` adds a deterministic Guerrini-style candidate
producer. It manipulates ordinary runtime token/partition state and partial
derivation trees; none of that state is trusted. A result exists only after
`verifyDerivation?` validates the completed tree, and
`unificationFastCheck_sound` proves the resulting Boolean fast path cannot
accept an invalid certificate. `unificationCheck` is the exact public
decision: it short-circuits on the verified fast path and otherwise invokes
the already complete checker-free reconstruction decision. Lean proves
`unificationCheck = check`. Fast-path rejection alone is inconclusive, and no
linearity claim is made until its completeness and worklist/union-find
invariants are proved.

`unificationDerivationCandidateWithStats` and
`unificationReconstructWithStats` expose scan counters without adding a trust
assumption. Proof fields certify at most `|links|²` eager link-list visits, and
the public bound theorem is axiom-free. Those proof fields say nothing about
the cost of frontier search, representative lookup, verification, or fallback;
callers must not treat them as a whole-program deadline.

The event-driven worklist tier is subject to the identical trust boundary.
`unificationWorklistReconstructWithStats` returns only after
`verifyDerivation?`, and Lean proves both worklist fast-path soundness and
exact equality of its fallback wrapper with `check`. The worklist candidate
carries an axiom-free proof of the conservative `n(n+4)+1` link-attempt cap.
Current `main` additionally proves an exact distinct-firing history, bounded
enqueue sources, insertion/pop conservation, and canonical queue exhaustion
within that cap. The quiescent run now also gives an exact proof witness for
each submitted but unfired connective: an idle premise, a distinct-thread
registered par, or a same-thread tensor deadlock. Kernel-checked semantic
thread connectivity and reference-switching acyclicity now exclude the tensor
deadlock on declaratively correct inputs. Causal marking closure and the
converse retained-edge invariant additionally prove exact agreement between
active-reference components and union-find classes on reachable states. The
remaining waiting par is therefore known to have marked premises with no
active reference walk. Exact tree-edge exchange additionally produces a
reference simple path between those premises which avoids the par conclusion,
and the active-path theorem extracts an unmarked internal occurrence. The
current first-frontier theorem retains the exact traversed edge occurrence
from a marked source into an unmarked target and an entirely active prefix.
Exact component/thread correspondence additionally proves that the source
carries the waiting par's left token. Reverse-path extraction selects the
last inactive frontier, identifies its target with the right token, and
proves the two boundary occurrences are distinct and exactly ordered. Exact
retained-edge/source-link lookup,
completed axiom initialization, and causal closure classify the occurrence as
a forward premise-to-conclusion edge of a submitted par or tensor. Quiescent
scheduler coverage further isolates an unassigned omitted par premise, a
registered distinct-token par, or an unassigned opposite tensor premise at
both sides. A first-reentry suffix cut further proves that every traversed
occurrence strictly between the selected boundaries has two unmarked
endpoints. The resulting contiguous path-exposed inactive block has not yet
been excluded. Current development does retain every exact submitted
source-connective/premise step in the terminating formula chase and stores
that composable path inside each edge of a finite closed waiting-dependency
segment. Each such step is now tied to its exact full occurrence-graph
backward edge; nontrivial chases yield vertex-simple, internally cusp-free
paths, and a state-indexed witness retains unassigned evidence at every
visited formula occurrence. The occurrence-exact frontier cannot be
immediately reversed by the first nontrivial tail edge. The all-left mask is
now classified at that exact full-edge index; structural typing and unique
producer ownership synchronize the first formula tail and prove the local
turn is a par cusp or tensor-colored free turn. The retained-prefix lift
preserves each stored edge and orientation, and the dependency-segment
proposition now binds the classified frontier and formula edge to the actual
last prefix and first tail occurrences. Thus parallel equal-endpoint edges
cannot satisfy the classification on behalf of different traversed
occurrences. Every dependency carries that same-boundary classification
 together with an exact composable complete-graph segment, and the selected
 finite family is kernel-concatenated into a genuinely nonempty closed
 occurrence-aware `fullGraph` walk. Every individual segment is now
 kernel-proved to satisfy the exact-occurrence
 `Graph.EdgeWalk.NoImmediateReverse` predicate. This local theorem does not
 cover the junction between adjacent segments, so the concatenated walk may
 still backtrack there or repeat occurrences. Any actual junction reversal is
 now proved to force the preceding formula chase to be reflexive; nontrivial
 tails end backward and cannot reverse the next backward segment head. The
 reflexive witness now records the exact retained frontier occurrence, and the
 same full-edge index is proved to be the next waiting par's source incidence.
 One exact reverse pair can be cancelled with the endpoints and all other
 occurrences preserved; parallel endpoint-equal occurrences cannot stand in
 for it. A terminating normalizer now covers internal and cyclic closing
 reversals and returns a closed normal form which is either empty or cyclically
 nonbacktracking; surviving occurrences are proved to come from the original
 walk. It does not claim that nonempty input stays nonempty, because nested
 out-and-back walks refute that claim. A proof-relevant cyclic normalization
 trace now records every internal and rotated closing cancellation. If the
 trace ends at the empty traversal, Lean proves that the reverse of every
 represented directed-edge value occurs in the original obstruction at the
 same stored edge index. This is membership, not a proved bijection between
 list positions. The scheduler construction further proves that every
 forward-oriented occurrence in the original dependency walk is retained by
 the all-left reference switching. Thus an empty normal form implies retention
 of every original edge index, including backward occurrences via their
 forward reverses. This characterizes the empty branch as a fully retained
 nested reference-tree walk. The scheduler theorem now transports the original
 nonempty closed walk into `referenceSwitchingGraph`, while the public
 `DeclarativelyCorrect.referenceSwitchingTree` theorem independently packages
 that retained graph's tree property. This remains consistent because a closed
 tree walk can be nested backtracking; it does not exclude the branch. In the
 nonempty branch, Lean now preserves exact indices, edge values, orientations,
 and cyclic nonbacktracking through an arbitrary switching mask. It proves that
 par-pair sparsity would place the obstruction in one switching tree, then
 extracts a concrete par whose two occurrences both survive and proves the
 omitted right occurrence is backward from the scheduler's forward-retention
 invariant. In the empty branch, the proof-relevant normalization now exposes
 an exact cancellation site in the original traversal rather than only
 reverse-value membership: the site is internal or crosses the cyclic
 last/first boundary. Cyclically nonbacktracking inputs are fixed points of
 normalization, and any internal cancellation in the append of two
 individually nonbacktracking pieces is forced to their unique junction. The
 scheduler theorem now retains the finite segment family with exact chain
 indices and endpoint classifications, localizes the site to an adjacent or
 cyclic family junction, and proves that the same stored occurrence is both
 the preceding dependency's retained reflexive end and the following waiting
 par's left incidence. Removing every exact source/frontier pair now exposes a
 deterministic residual core with token-equal endpoints and assigned
 occurrences throughout. Each core is kernel-proved nonempty: emptiness would
 make adjacent waiting pars consume the same exact premise, contradicting
 structural one-parent ownership and simple-cycle injectivity. Each core also
 inherits exact no-immediate-reverse from its containing segment, and the
 deterministic active family records both properties. Lean composes the
 family into a nonempty closed full-graph walk with exact cyclic
 source-premise endpoints. All core occurrences are reference-kept, forcing
the core-only cyclic normal form to be empty; the proof-relevant normalizer
localizes its exact reversal to a cyclic junction between nonempty internally
reduced cores. The junction is now reindexed to one exact dependency step,
reconciled with both complete segment decompositions, and exposed as the
contiguous exact-occurrence word
`inner, outer, outer.reverse, inner.reverse`. Segment nonbacktracking proves
that the two cancellation layers are nondegenerate. Both original detailed
segments remain attached to that index; their `core ++ frontier` traversals
are pointwise reconciled with exact retained reference-prefix walks, and the
 successor reference prefix is proved to begin with the inner occurrence's
 exact reverse. Lean now also constructs the exact simultaneous complementary
 flip around every fully reflexive dependency cycle. Each flipped segment is
 vertex-simple, avoids the target waiting par's retained left occurrence, and
 the flattened family is a nonempty closed cyclically nonbacktracking walk.
 Every internal transition, adjacent segment junction, and last/first closing
 junction is cusp-free. The unavoidable stored par pair is now localized
  across two distinct indexed segments: its omitted right occurrence is the
  unique head of the source segment, while its retained left occurrence cannot
  lie in that same vertex-simple traversal. Prefix injectivity also proves that
  the common conclusion is not the holder segment's start but is reached in
  that segment's target list; the two incidences are identified exactly as
  retained-left and omitted-right in the reference mask. The holder segment
  is split at the conclusion into a nonempty incoming simple path and an
  outgoing simple path, with unique intersection at that conclusion and the
  retained-left occurrence on the orientation-correct side. The remaining gap
  is global: repeated vertices and this exact internal chord must be resolved
  using the nesting/switching structure while preserving those incidence pairings.
 Ordinary loop erasure is not sufficient because it can create a new closing
 cusp at the erased vertex. This is not yet the correct-state progress theorem
 needed for pure-worklist completeness.
 The
 attempt accounting also excludes
 consumer-table construction, waiting-list traversal, frontier work, and
 verification.

For LeanProp wire inputs, `inferAt_eq_elaborateAt` kernel-proves that the
formula-only raw checker and typed elaborator agree on acceptance, rejection,
error category, detail, and child path. `elaborate?_complete` proves every raw
checker acceptance has an indexed witness with the same boundary. The public
wire checker runs the elaborator directly, and `CheckedDerivation.sound`
forwards the resulting indexed term to `Schema.PackedDerivation.sound`. The
trust audit records the exact dependencies: the agreement/completeness
theorems and `CheckedDerivation.inferred` use `[propext, Quot.sound]`; the
permutation-boundary agreement and checked soundness theorem use `[propext]`.
At the typed context layer, permutation completeness and the two exchange-
admissibility theorems are axiom-free; the two dependent-environment inverse
laws use `[propext]`. Six public persistent-normalization theorems use
`[propext]`; the structural-size nonincrease theorem, whose arithmetic proof
uses the kernel-checked omega procedure, uses `[propext, Quot.sound]`.

Canonical v0.2 serialization trusts the formula-array numbering as occurrence
identity. Sorting links/conclusions and orienting axiom endpoints is a stable
wire-format rule, not a graph-isomorphism theorem. Dataset labels are emitted
by Lean and cross-checked by the independent Python oracle; the committed
dataset itself remains untrusted input when consumed by later experiments.

The separate v0.3 `reindex-v1` path first relabels vertices by their ordered
first occurrence in conclusions and links. Lean proves this value unchanged by
every bounded `VertexRenaming`. For structurally well-formed inputs, Lean also
proves traversal coverage, constructs the induced renaming, proves the normal
form is in the original class, and proves normal-form equality iff
`ReindexEquivalent`. The generic parser validates the declared algorithm and
normalized payload; logical acceptance is still rechecked separately.

For checker-accepted values, the supported production pairwise identity API is
`CheckedCertificate.sameProofNet?`. Lean proves its Boolean result is true iff
the two certificates satisfy exactly `ProofNetEquivalent`: bounded vertex
renaming followed by link-list permutation, preserving ordered conclusions,
connective premises, formula labels, and axiom orientation. The optimized
candidate generator enforces the ordered boundary during enumeration, and its
completeness feeds the already-audited exact decision theorem. This is neither
an arbitrary graph-isomorphism oracle nor a canonical serialization theorem.

The released `proofNetCanonicalFingerprint?` takes the lexicographic minimum
of the v0.3 strings in the complete finite canonical family. Lean proves that
the option is always populated, that a selected value belongs to the family
image, and that `ProofNetEquivalent` certificates have equal fingerprints.
This JSON-string result remains forward-only because the project does not
assume `Json.compress` injectivity. The separate `proofNetCanonicalCode?`
uses an explicitly length-framed structural token encoder whose injectivity is
proved in Lean. On structurally well-formed certificates, and therefore on
checker-accepted inputs, equality of this typed code is proved iff exactly
`ProofNetEquivalent`. These public boundary proofs use exactly
`[propext, Classical.choice, Quot.sound]`; no project-specific axiom or
unproved serializer premise is added.

`CanonicalKey.fromString` parses the distinct
`proofnet-canonical-key-0.1` envelope with token-count and aggregate-character
limits. Parsing establishes only wire shape: tokens arriving from outside are
opaque and are not trusted as proof-net evidence. The safe boundary recomputes
the bounded canonical key locally from checker-accepted certificates.
`proofNetEquivalent_of_matchesCanonicalKey` proves that two accepted
certificates matching one parsed key are equivalent. The generator still uses
factorial family materialization, so generation and matching check the
seven-link ceiling before computation and fail closed above it. The unbounded
typed `proofNetCanonicalKey?` remains a specification oracle.

`IntrinsicCanonicalKey.fromString` parses the separate
`proofnet-canonical-key-0.2` envelope. Its tokens are equally untrusted until
compared with a locally generated key. The local generator first requires
structural well-formedness, constructs the proved intrinsic representative,
and checks the token/character envelope. Lean proves that two such local
certificates matching one admissible key are exactly `ProofNetEquivalent`.
The intrinsic construction has no link-count ceiling and does not enumerate
permutations, but parsing a key alone still proves neither origin nor checker
acceptance.

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
