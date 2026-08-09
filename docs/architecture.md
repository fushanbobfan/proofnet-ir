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

Finite maximal-forest counting now supplies the connectedness bridge as well.
All occurrence switchings have the same retained edge count; therefore a
connected, acyclic deterministic reference switching fixes the tree count for
every other acyclic switching. No improved asymptotic bound is inferred from
the exhaustive colored-cycle oracle.

The remaining boundary is explicit rather than informal:

```text
check = true ↔
  StructurallyWellFormed ∧
  CuspAcyclic ∧
  ReferenceSwitchingConnected
```

`Certificate.compactCheck` executes exactly these three fields and is proved
Boolean-equal to the all-switchings checker. The proof builds bounded,
acyclic retained graphs, derives their common maximal forest count from the
reference graph, and transports their tree property across the exact
edge-list permutation used by the public switching graph.

`Certificate.unificationFastCheck` now implements the Figure-5
start/forward/unify token rules from Guerrini for the supported cut-free
fragment while constructing partial derivations. A completed tree is accepted
only after `verifyDerivation?` independently checks inference,
desequentialization, and intrinsic proof-net identity, so Lean proves the fast
path sound. `Certificate.unificationCheck` short-circuits through that path
and invokes the already complete checker-free recursive sequentializer on a
miss; Lean therefore proves `unificationCheck = check` for every input. This
is a switching-free exact API, but not yet the pure complete or linear
algorithm: the eager pass lacks a completeness proof and the fallback remains
exhaustive. The exact source/code boundary is recorded in
[guerrini-unification-audit.md](guerrini-unification-audit.md).

The `WithStats` variants retain a proof-relevant operational receipt. Their
candidate records satisfy `passes ≤ |links|` and
`linkVisits = passes * |links|`, yielding an axiom-free square bound on eager
link-list visits. That result characterizes the current scan schedule only;
the architecture still needs the Figures 7--8 sequential ready/waiting stacks,
token-age sequencing and special union-find invariants, plus a whole-program
cost model covering frontier manipulation, verification, and fallback. A
separate `SequentialUnification.lean` checkpoint now supplies a reusable
source-incidence index whose entries have exact submitted-link origin.
`SourceIndex.Sound` alone supplies only provenance, not lookup existence or
uniqueness; because both endpoints are registered, a malformed self-axiom
contributes twice to one bucket. Structural well-formedness now proves every
in-bounds occurrence has exactly one source entry. The checkpoint also
supplies a bounded/globally tagged `NEXTAXIOM` search and a dynamic Figure-5
start. Every search success retains the exact submitted axiom
index/endpoints, final tags, and trace, and proves tag-array size preservation,
monotonicity of old true tags, trace `Nodup`, input-false/output-true tagging of
the trace and endpoints, input-unmarked endpoints, and
`trace.length ≤ fuel`. Its touched carrier is the trace plus both endpoints;
successive successful calls have disjoint touched carriers when the second
call uses exactly `first.tags`. This is the scope of the global no-revisit
discipline; resetting or replacing tags is outside the theorem.
`SequentialRoute.lean` proves that every successful trace is the exact chain of
submitted connective conclusions to stored left premises and names the axiom
endpoint actually reached independently of the axiom's submitted
`left`/`right` order.

`SearchClearThrough` supports a separate local totality theorem. Under
structural well-formedness, state abstraction, rank-scoped untagged/unassigned
freshness, and fuel strictly greater than the starting formula complexity, the
production-index call succeeds. Full carrier freshness gives the exact
`complexity + 1` budget. This proves the initial/local call only; it does not
prove the existing carrier-size wrapper total or preserve the premise for
later Figures 7–8 scheduler states. A success tags complexity-zero axiom
endpoints, so the global low-rank predicate cannot itself be threaded to a
second call; the scheduler needs a route-local freshness invariant.

The dynamic update immediately allocates and assigns a token and refines
`UnificationStep.start` under `OrderedParents`. It is an independent eager
Figure-5 refinement, not the delayed Figures 7–8 `init`/`new` transition.
Regressions cover zero fuel, out-of-bounds, tagged and marked starts, missing
and ambiguous source buckets, threaded-result-tags repeat rejection,
stored-right orientation, all canonical initial starts under their rank
budgets, a depth-two exact rank-versus-`rank + 1` fuel boundary, and the
successful dynamic update.

`SequentialSchedulerState.lean` remains a separate delayed-state
specification. `SequentialSchedulerBridge.lean` connects that state to the
production carrier without identifying the two representations.
`ReservationState` stores the delayed `SequentialStackState`, production
`UnificationState`, and complete `NEXTAXIOM` tag array side by side.
`initializeReservation?` starts from the exact empty wrapper;
`reserveNewAxiom?` consumes a prior wrapper and threads its tags into one later
search. Both reserve the returned submitted axiom without marking its
endpoints. `InitialReservationStep` and `NewReservationStep` are typed,
proof-relevant decompositions of successful calls, and the
`initializeReservation?_some_iff` / `reserveNewAxiom?_some_iff` theorems make
those records equivalent to executable `some` results.

The state layer's `RawTokenAge` is the immutable discovery-order age, never a
union-find representative. `SigmaAgePartition` proves that the boundary list
is empty exactly at raw-age horizon zero, begins at zero at a positive horizon,
is strictly increasing, and contains only boundaries below that horizon.
`sigmaBoundary?` selects the greatest boundary not exceeding a raw age. Waiting
storage is fixed-capacity and intentionally has three observably different
cases: array lookup `none` (out of bounds), `some undefined` (`⊥`), and
`some (initialized [])` (`∅`).

The strict local initialization guard requires both stacks and the age horizon
to be empty, every mark and waiting cell to be undefined, and the two endpoints
to be distinct and in bounds. Global carrier agreement and the remaining
`WellShaped` obligations are separate preservation-theorem preconditions. Its
executable reservation produces `σ = [0]` and
ready buckets `[[reached, partner]]` while preserving the mark array and
leaving `W(0)` undefined. The literal `newEnqueue?` source-audit helper appends
the old horizon to `σ`, appends `[reached, partner]`, and initializes the fresh
waiting cell exactly as the printed Figure-7 display does. That helper
preserves the weak local `WellShaped` invariant but is not the production
transition. The production bridge uses `operationalNewEnqueue?`, which
initializes the old active `σ` boundary and leaves the freshly pushed active
top undefined. Lean proves that `initEnqueue?` and this operational transition
preserve `OperationalWaitingDomain`: among allocated ages, initialized waiting
cells are exactly `sigma.dropLast`. This is the project's one-cell
interpretation of the prose-defined nonactive waiting domain and the later
`wait`/`unify` behavior, not an author-confirmed erratum or a uniqueness
theorem.

`reserveAxiomAt?` creates a locally well-formed submitted-orientation live
axiom component and a fresh self-parent while leaving marks unchanged. Each
wrapper uses one `NextAxiomResult`: its delayed bucket keeps
`[reached, partner]`, while the production component keeps
`[result.left, result.right]`. Exact tag threading is part of the wrapper
composition. The typed-step theorems prove that an initial step followed by a
later step, or two later steps, cannot return the same submitted axiom-link
index. This is precisely scoped wrapper replay exclusion. It does not collapse
equal-valued duplicate axioms at distinct indices without another structural
premise. Resetting or replacing the tag array is outside the composable-step
replay theorem, and the lower-level reservation primitive can reserve the old
link index again.

`RealizesSigma` equates raw marks, the carrier horizon, and each executable
`sigmaBoundary?` lookup with the production representative. Initialization
establishes it, and `new_reserve_carrier_realizesSigma` preserves it on every
later reservation. For an old raw age,
`sigmaBoundary?_append_fresh_old` removes the appended boundary and
`reserveAxiomAt?_old_representative` keeps its representative unchanged. For
the fresh age, the `SigmaAgePartition` fresh-self append lemma matches
`reserveAxiomAt?_fresh_representative`. This argument intentionally depends on
the exact append transition. A deliberately arbitrary ordered parent forest
with parents `#[0, 1, 0]` and `sigma = [0, 1]` gives raw age `2` boundary `1`
but production representative `0`. It is not proved reachable by an actual
`unify`/union transition; the example only refutes obtaining `RealizesSigma`
automatically from `WellShaped`, marks/horizon alignment, and
`OrderedParents`.

`ReservationInvariant` is the preserved reservation-layer bundle:
delayed-state `WellShaped`, `OperationalWaitingDomain`, `RealizesSigma`,
production `OrderedParents`, `Abstractable`, and
`ComponentsFormulaConsistent`, component/parent carrier alignment,
`startedAxioms`/parent-counter alignment, and tag/formula-domain alignment.
The exact empty state satisfies it; a successful
`InitialReservationStep` establishes it; and every successful
`NewReservationStep` preserves it. The structure itself is not an inductive
reachability or tag-history characterization: `tags_size` records only the tag
carrier, so a reset-tag state may still satisfy the bundle. Its waiting-domain
field says which cells are initialized, not who owns their payloads or how
`wait`/`unify` transfers or drains them. The canonical
two-step fixture locks
submitted/ready orientation as `[0,1]`/`[1,0]`, then
`[2,3]`/`[3,2]`.

The next module, `SequentialFigure7New.lean`, now composes the project's
operational local Figure-7 `new` rule over a supplied
`ReservationInvariant`. It retains an
exhausted last ready bucket, writes the old top raw age in both state views,
uses the certificate's fixed sound-and-complete `ConsumerIndex` to obtain the
unique orientation-aware tensor and opposite premise, evaluates `NEXTAXIOM`
in the post-mark state, then appends and reserves the returned axiom through
`operationalNewEnqueue?`. The old active waiting boundary becomes initialized
and the fresh active top remains undefined. The dependent success witness
carries the input invariant and binds search to the post-mark core. This is not
yet a full-scheduler characterization: `ReservationInvariant` has only tag
carrier size, not tag provenance/monotonicity, and it lacks ready/waiting
payload ownership and global queue uniqueness.

`SequentialFigure7History.lean` adds a separate inductive
`InitNewHistory` whose constructors retain exact successful empty,
initialization, and operational-`new` witnesses. Unlike
`ReservationInvariant`, this type is reachability by execution. Its theorems
prove tags are true exactly at the union of recorded search-touched sets,
successive touched sets are disjoint, submitted axiom-link indices are
globally `Nodup`, and the history length equals both `stack.nextAge` and
`core.startedAxioms`. The type deliberately cannot be extended naively with
non-reserving rules: a future complete rule history must distinguish total
rule steps from axiom-reservation events.

`SequentialFigure7Rules.lean` adds a generic proof-carrying binary-consumer
view over the canonical consumer index, an explicit-conclusion view requiring
declared membership, local `NodeWellFormed` ownership, and an exactly empty
bucket, plus the synchronized `prepare?` prefix. `concl?`, `nop?`, `wait?`, and
`forward?` have dependent executable specifications and preserve the
reservation invariant. The bounded `unifyEmpty?` has a dependent executable
specification and direct correspondence; successful typed and executable steps
also preserve the complete occurrence-exact `SchedulerInvariant` when it is
supplied for the input state.
`concl` and `nop` return only the prefix state; `wait` then updates one exact
initialized waiting bucket. The ownership and empty-bucket guards
in `concl` reject out-of-range or unproduced declared boundaries;
`uniqueConsumer? = none` also describes a malformed bucket with distinct
candidates. `nop` instead retains an exact submitted par and requires its
opposite premise to remain raw unmarked after the selected premise is marked.
The mate-distinctness and pre-state guard theorem proves that this is exactly
the paper's `μ(u₂)=⊥` condition rather than a weakened post-state surrogate.
The dependent rule witnesses remain executable-shaped and retain `prepare?`
and query equations. `wait?` compares the mate's raw mark with the selected
raw age, resolves `sigmaBoundary? stack.sigma mateRawAge`, and performs one
initialized-cell cons update without scanning `queuedVertices`. A separate
direct `RulePrefixAt`/`ConclRule`/`NopRule`/`WaitRule` layer is Boolean-free
and independent of those functions. Executable soundness is kernel checked
from the supplied `ReservationInvariant`; completeness relative to that layer
uses whole-certificate `StructurallyWellFormed` as well. Direct outputs are
unique under their documented hypotheses. `WaitRule` uses a
proposition-level exact
`sigmaBoundary? = some boundary` equation and states the paper guard in
`before.core.marks`. `ForwardRule` now supplies the corresponding independent
direct relation for Forward without referencing a Figure-7 executable or
mutation wrapper. Its paper guard is exactly
`selectedRawAge ≤ mateRawAge`; the separate
`ForwardExecutableReadyNodup` predicate records only the executable list-shape
requirement. Under the stronger state-only `SchedulerInvariant`, every
successful `WaitStep` and executable `wait?` additionally preserves global
queue uniqueness and raw-unmarkedness and adds the exact positional submitted
par to `WaitingSpanExact`; the component forest and logical firing counter stay
unchanged. This is still a determinized list-level successful-step theorem,
not a complete dispatcher, applicability, or reachability result.

`forward?` composes the same prepared prefix with the exact submitted par
occurrence, requires the mate's raw mark and the paper's non-strict guard
`selectedRawAge ≤ mateRawAge`, queues that par in the production component,
and prepends its conclusion to the active ready bucket. A separate theorem
regression covers the distinct-age boundary case
`sigmaBoundary? [0] 1 = some 0`. The additional active-ready `Nodup` guard is
only a fail-closed shape check, not part of the paper rule. Every successful
typed `ForwardStep` and executable `forward?` preserves the complete
occurrence-exact `SchedulerInvariant`: the submitted par position,
component-occurrence forest, live frontier, ready/waiting queue, waiting spans,
pending-premise coverage, and fired-connective counter all transport exactly.
A typed `init → nop → forward → concl` regression checks this composition.
`ForwardStep.toRule` and `forward?_sound` refine executable success to the
direct rule. Structural validity, the reservation invariant, and the separate
ready-list shape predicate yield completeness, iff, and output uniqueness;
the complete scheduler invariant derives the shape predicate and yields the
corresponding higher-level completeness/iff. None of these results proves
Forward applicability or scheduler progress.

The same module now exposes a deliberately bounded empty-cell tensor slice.
`unifyEmpty?` accepts exactly `W(j) = []`, retains the exact submitted tensor
slot and stored orientation, and checks raw ages with
`j ≤ μ(mate) < i`. The adjacent-boundary lemma and `RealizesSigma` derive that
the production representatives are exactly `j/i`; the tensor core then binds
`parent[i] := j`, while the stack pops the active level, makes `W(j)` undefined,
and installs `conclusion :: (previousReady ++ activeReady)`. Independent
`UnifyEmptyRule` equations do not call the high-level executable or mutation
wrappers, although they explicitly reuse the low-level read-only
`unifyTokens?` and `componentAt?` observations. Soundness assumes
`ReservationInvariant`; completeness/iff additionally require structural
validity and the separate final-ready-list `Nodup` premise. Successful
execution preserves `ReservationInvariant`: the proof transports
`RealizesSigma` through both the active-boundary pop and the exact
`parent[i] := j` union. The stronger successful-step theorem additionally
transports the exact tensor-derived component witness through the
survivor/retired forest merge and preserves every remaining state-only
`SchedulerInvariant` field. This remains the empty-payload branch.

`SequentialFigure7UnifyOne.lean` adds the next deliberately bounded branch:
`unifyOne?` accepts exactly `W(j) = [c]`. `waitingParProducer?` resolves `c`
through the occurrence source index to a singleton bucket containing its exact
submitted par slot and stored orientation; missing, ambiguous, position-mismatched,
non-par, and malformed sources fail closed. One successful transition is
atomic in the order prepare, tensor construction/union, activation of that one
waiting par, then the two-level scheduler drain. Independent Boolean-free
`WaitingParActivationRule` and `UnifyOneRule` relations do not call the rule
executables or mutation wrappers. Lean proves typed/executable correspondence,
output uniqueness, `ReservationInvariant` preservation, complete
occurrence-exact `SchedulerInvariant` preservation, and an exact connective
counter increase of two. Empty and length-at-least-two waiting payloads are
rejected by this executable. The paper's `unify` presentation moves `W(j)`
into ready; constructing the corresponding par derivation before that move is
the project's provenance-carrying representation refinement, not an assertion
that Guerrini states that extra construction.

`SequentialFigure7Unify.lean` adds the local arbitrary-payload
production-core layer without yet defining a general scheduler rule.
`activateWaitingPayload?` deterministically threads the existing exact par
activation over the stored list from head to tail. Independent Boolean-free
and typed fold relations have exact executable correspondence and unique
output. Successful typed folds leave marks and parents fixed, preserve
component-array size and started-axiom count, transport abstraction, ordered
parents, formula consistency, and reservation alignment under their explicit
hypotheses, and increase `firedConnectives` by exactly `payload.length`.
Because Guerrini's `W(j)` is a set, neither this order nor the resulting nested
derivation-tree order is source-algorithm semantics. The fold contains no stack
state and establishes neither applicability from `SchedulerInvariant`, exact
component-forest transport, nor the atomic tensor/fold/drain transition.

`SequentialFigure7UnifyPayload.lean` supplies that local atomic transition.
`unifyPayload?` composes the common prepare prefix, one exact tensor
construction/union, the stored-head-to-tail activation fold, and
`mergeTopReadyWaiting?`. The high-level-executable-independent direct
`UnifyPayloadRule` and
typed `UnifyPayloadStep` give exact executable correspondence and unique output
under the explicit structural, `ReservationInvariant`, and final-ready `Nodup`
premises. `UnifyPayloadStep.exact` fixes the final stack equations, stored
tensor orientation, and total project counter increase
`1 + payload.length`; every successful typed/executable step preserves
`ReservationInvariant`. `SequentialFigure7UnifyPayloadInvariant.lean` adds
complete occurrence-exact `SchedulerInvariant` preservation for every
successful typed or executable arbitrary-payload step from a full input
invariant. Its fixed-final-stack `UnifyPayloadGapInvariant` represents the
unactivated stored suffix as a transient gap: each head activation establishes
the exact new component ownership, and the empty suffix closes back to the
ordinary ready/frontier invariant. Pre-activation forest-freshness,
non-production, exact submitted-par provenance, and boundary-token facts come
from the input invariant, with no history/reachability premise.
`SequentialFigure7UnifyPayloadEnabled.lean` separates applicability from
preservation. Its input-only `UnifyPayloadEnabled` fixes the ready occurrence,
two adjacent sigma levels, canonical tensor consumer, and mate interval. The
full invariant then derives all hidden executor guards and an
invariant-preserving output. No post-state or success equation occurs in the
predicate, and the invariant alone does not imply it. No full scheduler
invariant is claimed for physical intermediate tensor/fold states. The specialized `UnifyEmpty` and `UnifyOne`
successes embed one way into the new executor at the same exact output, without
general function equality or reverse equivalence. Stored order is an executable
and derivation-nesting choice, not a commutativity or source temporal-order
theorem.

`SequentialFigure7StableEnabled.lean` provides an independent input-only
applicability layer for `concl`, `nop`, `wait`, and `forward`; it imports the
state invariant rather than the dispatcher or tag-history modules. A shared
`ReadyHeadInput` fixes only the top ready occurrence/tail/raw age and exact
top/sigma equations. `SubmittedParInput` fixes only the exact submitted par
slot and selected premise orientation. The four rule inputs contain no
post-state or success equation. Wait stores only a marked mate age and the
strict older-age guard, so the invariant must derive the active/inactive sigma
boundary and initialized waiting payload. Forward stores only a marked mate
age and the non-older guard, so the invariant must derive the active token,
shared component, exact occurrence picks, and final ready `Nodup`. Each enabled
predicate plus the full invariant therefore yields executable success and a
full-invariant output. The local submitted-par theorem classifies only an
already supplied ready head and exact submitted par as `nop`, `wait`, or
`forward`; it is not a global scheduler partition and says nothing about
conclusions, tensors, `new`, unification, dispatcher priority, or progress.
The same module now exposes occurrence-exact coverage one layer below rule
selection. From structural well-formedness, every in-bounds occurrence falls
into a conclusion, exact submitted-par-consumer, or exact
submitted-tensor-consumer case; `SchedulerInvariant` supplies the bound for an
already selected ready head. Combining this with the stable par classification
and exact mate lookup gives four stable enabled alternatives plus unmarked and
marked tensor alternatives. The nested disjunction proves coverage only, not
pairwise exclusivity or a unique selected case. The bare unmarked tensor case
is not promoted to `NewEnabled` from coverage alone. The source-region bridge
below performs that promotion only after exact route reconstruction, endpoint
queue separation, and strict fresh-cell capacity are supplied. The separate
`SequentialFigure7TensorAdjacency.lean` layer promotes a marked tensor to
`UnifyPayloadEnabled` only when an input-only witness supplies an actual sigma
predecessor and resolves the mate age to that predecessor. The bare marked
alternative does not derive this adjacency evidence. This is not merely a
structural warning: a checker-rejected one-axiom/one-tensor fixture reaches a
full state-only `SchedulerInvariant` after initialization and the common
prepare prefix while retaining singleton sigma, a ready tensor premise, and a
marked mate, yet `UnifyPayloadEnabled` is false. The fixture proves no
correct-certificate or canonical-dispatcher reachability fact, and no progress
theorem is claimed. Its fixed initialization uses `native_decide`, so this is
private executable regression evidence rather than another public theorem in
the library's three-axiom trust boundary. `SigmaPredecessorInput` itself stores
the active-top equation as well as the predecessor and mate-boundary lookups;
the active boundary is not a phantom index.

`SequentialFigure7Dispatcher.lean` composes the six canonical successful rule
executors under one fixed precedence:
`concl`, `nop`, `new`, `wait`, `forward`, then `unifyPayload`. The dependent
`DispatchStep` specification records all preceding failed branch equations, so
its exact iff is stronger than an unprioritized sum of rule witnesses. Every
selected branch maps to a typed local step and transports the complete
state-only scheduler invariant. Empty- and singleton-payload executors remain
compatibility APIs rather than additional dispatcher constructors. The module's
`ExecutedHistory` is deliberately certified: each later event stores the exact
dispatcher witness and the invariant supplied to that call. It is useful for
auditable execution composition, but it neither synthesizes a guard nor proves
that a nonterminal state has a successor. The earlier `InitNewHistory` remains
separate because its event-count and explicit reservation-only shape laws are
stronger and reservation-specific. `SequentialFigure7TagHistory.lean` recovers
the selected typed branch from every exact `DispatchStep` and augments the
existing history without widening reachability. Stable branches preserve tags
exactly; `new` retains its search touch and submitted slot. The full augmented
trace proves tag-touch equivalence, touch separation, history independence,
submitted-slot `Nodup`, and exact recorded-slot length equal to final
`nextAge`, but no applicability, totality, progress, or
concrete forged-state nonreachability.

`SequentialFigure7ProgressInvariant.lean` keeps future waiting storage separate
from the ordinary state invariant. `FutureWaitingUndefined` constrains only
in-bounds cells at or beyond `nextAge`; it is established by exact empty and
initial states and preserved by the common prepare prefix, all six successful
rules, dispatch, `ExecutedHistory`, and certified reachability. It does not
assert capacity at `nextAge`, endpoint queue separation, enabledness, or
progress. A
private native-computed test changes only the first future cell of an otherwise
full-invariant tensor-ready state and retains `NewGuard` plus an exact
`FreshSourceLeftRun`, while the enqueue guard and `NewEnabled` fail. The forged
state is not reachable evidence. The result isolates storage cleanliness as a
history-preserved prerequisite. `SequentialFigure7NewRegion.lean` combines it
with exact route reconstruction and three explicit region facts.
`SequentialFigure7FreshCapacity.lean` now discharges strict fresh formula
capacity conditionally from structural well-formedness, a canonical history,
and an exact current-tag `FreshSourceLeftRun`; it does not produce that run.
`SequentialFigure7QueueHistory.lean` now discharges both endpoint queue-absence
facts from the same canonical history. Its induction is intentionally limited
to endpoints of one exact submitted axiom, because stable rules may enqueue
untagged connective conclusions. Deriving the run or an exact route from the
weaker correct-certified-reachable unmarked-tensor branch, and then proving
global progress, remain separate obligations.

`SequentialFigure7PriorityEnabled.lean` is a one-way downstream bridge from
the dispatcher and all six input-only enabled predicates. It does not change
an executor. Successful typed steps reconstruct their input-only enabled
witnesses; conversely, those witnesses plus `SchedulerInvariant` produce
existential executor success. The `new` field and all stored `new` negations
now use `NewEnabled`. `NewExecutableEnabled` remains only as an operational
compatibility proposition with an exact iff and compatibility constructor.
Indexed `PriorityEnabled` adds exactly the negative predicates needed by the
fixed dispatcher order. It is equivalent to the matching `DispatchStep`,
classifies an exact selected dispatcher kind, characterizes dispatcher `none`,
and makes the selected priority kind unique. The characterization is relative
to the current executor order. In particular, a completed reachable stack
`[[]]` can satisfy `SchedulerInvariant` while every priority kind is disabled;
no intended-state exhaustiveness, nonterminality, progress, or completeness
theorem follows.

`SequentialFigure7NewInputCore.lean` supplies the lower-layer read-only
projection used below both `NewEnabled` and the priority interface;
`SequentialFigure7NewInputNecessary.lean` retains the historical facade.
`NewGuard` contains the ready head,
exact valid tensor-below witness, and input-unmarked mate;
`FreshSourceLeftRoute` contains a bounded exact source-left trace, input tag
freshness, whole-trace production readiness, and ready terminal axiom
endpoints. Successful typed/executable
`new` steps reconstruct `NewInputNecessary`, but no unconditional converse is
exposed. The
witness omits recursive per-step tag-update equations and the later operational
enqueue guard. Structural reconstruction now recovers the exact run and proves
terminal-partner exclusion. Canonical queue/tag history now reconstructs the
remaining enqueue region and proves a history-indexed
`NewEnabled ↔ NewInputNecessary` under the complete state invariant. Without
that history, this remains only a necessary observation, not an `*Enabled`
predicate or progress premise. The canonical priority layer uses the stronger
`NewEnabled`.

`SequentialFreshSourceLeftRun.lean` is the exact proof-relevant input layer
below the newer local criterion. Its four constructors mirror the two terminal
axiom orientations and the stored-left tensor/par recursion of
`nextAxiomWithFuel?`; source-bucket and submitted-slot equations retain exact
occurrence identity, while the fixed production state and evolving tag array
record raw readiness and each recursive tag update. The relation is defined
for arbitrary certificates and is equivalent to an exact named executor
execution. Structural well-formedness enters only at the terminal reservation
bridge. `SequentialFigure7NewEnabledCore.lean` combines `NewGuard`, one exact run at
the certificate fuel bound, and `OperationalNewReadyAt` at the selected head's
raw age. The resulting `NewEnabled` is input-only—there is no result,
equation, output, history, or reachability field—and, under the complete
`SchedulerInvariant`, is equivalent to existential `new?` success. The
dedicated lower-layer split lets the priority module import this predicate
without a cycle and store it directly, while the dispatcher executable and
precedence remain unchanged. `SequentialFigure7NewEnabled.lean` is the
historical compatibility facade: importing it still exposes the priority
classifier and `PriorityEnabled.newInputNecessary`; default-build facade and
narrow-priority sentinels protect both import surfaces. This layering fact does not establish
reachable-state exhaustiveness, totality, progress, completeness, fallback
removal, or a cost theorem.

`SequentialFigure7NewRegion.lean` closes the declarative-route/exact-run gap.
For a structurally well-formed certificate, source-incidence singletonhood
proves that each nonterminal connective conclusion differs from the terminal
axiom partner, and terminal axiom well-formedness separates the last reached
endpoint from that partner. Thus `FreshSourceLeftRoute` reconstructs a
formula-bounded `FreshSourceLeftRun` with no executor or reachability premise.
`NewSourceRegionInput` then records the exact run plus only two endpoint
queue-absence facts and strict capacity at the fresh raw age. Together with
`SchedulerInvariant` and `FutureWaitingUndefined`, these facts derive
`OperationalNewReadyAt` and `NewEnabled`. This bridge is local and conditional;
it does not itself show that a correct reachable unmarked-tensor branch supplies
the exact route, nor progress or totality. The separate fresh-capacity theorem
derives strict capacity from structural well-formedness, canonical history, and
the exact run. The exact axiom-endpoint queue-history induction proves that any
currently queued run endpoint must be a recorded touch and therefore have a
true current tag, contradicting run freshness. It derives both post-pop
queue-absence fields and upgrades `NewInputNecessary` to `NewEnabled` on a
canonical history; certified dispatcher reachability packages the same
equivalence. Arbitrary queued occurrences are not classified as tagged.

`SequentialFreshSourceBlocker.lean` sits below those history-indexed bridges.
`SourceLeftRegionVertex` is the structurally determined carrier of one search:
it contains every recursively visited stored-left vertex and additionally the
other endpoint of the terminal submitted axiom. `FreshSourceBlocker` chooses
one such occurrence and records exactly one dynamic availability failure: its
input tag lookup is not `some false`, or its raw-mark lookup is not
`some none`. For every structurally well-formed certificate and in-bounds
start, `freshSourceLeftRun_or_blocker` returns either a formula-budget
`FreshSourceLeftRun` or a nonempty blocker. Structural link shape, source-index
singletonhood, and sufficient fuel are therefore discharged before the
scheduler/history layer. The theorem does not inspect canonical history or
declarative correctness, and it neither excludes the blocker nor proves queue
absence, fresh capacity, enabledness, reachability, progress, totality, or
completeness. Queue and capacity remain downstream obligations after the exact
run has been obtained. The companion `freshSourceLeftRun_of_regionAvailable`
corollary makes the remaining interface explicit: a future history theorem may
close the gap by proving freshness and raw-unmarkedness for every region
occurrence, without changing the structural classifier.

`SequentialFigure7BlockerHistory.lean` is the next history-indexed layer. Under
an authentic `CanonicalTagHistory`, the complete `SchedulerInvariant`, and the
selected `NewGuard`, its pointwise tag classifier turns any false-tag lookup
failure into an exact earlier touch. Its raw classifier compares the pure
post-pop/mark expression with the input production core: the failure is either
the one mark introduced at the selected ready head or an old concrete raw mark.
The component-forest field resolves the latter to an
`ExactMarkedOccurrenceOwner`, retaining representative slot, component lookup,
occurrence derivation, accounting, and membership. The combined
`CanonicalSourceLeftObstruction` is the disjunction of those three
possibly-overlapping provenance forms. It assumes neither another exact run nor
`NewEnabled`, so it does not circularly solve the search obligation.

The first local elimination theorem now separates recursive-route geometry
from terminal-axiom geometry. `SourceLeftStep.formulaComplexity_lt` makes each
stored-left source step strictly rank-decreasing, and
`SourceLeftReachable.eq_or_exists_lastStep` exposes the exact final consumer.
Combining those facts with structural unique-consumer provenance proves
`NewGuard.not_sourceLeftReachable_mate_head`: a route launched at the selected
tensor's opposite premise cannot revisit the selected ready head. The
history-level `classifyVisitedFreshRawBlocker` and
`classifyVisitedFreshBlocker` therefore remove the selected-head alternative
on `visited` occurrences without assuming correctness or another search.
`SequentialFigure7TerminalPartnerGeometry.lean` discharges the distinct
`terminalPartner` case once reference-switching acyclicity is supplied. It
embeds exact source-left and terminal-axiom occurrences into a simple all-left
reference path, excludes the selected tensor conclusion from that path by
complexity, and closes a forbidden occurrence-aware cycle with the tensor's
two fixed edges if the partner is the head. `DeclarativelyCorrect` packages
the required acyclicity. The resulting full-region classifiers retain only
prior canonical touch or old exact live-component ownership. Those alternatives
are intentionally inclusive. A canonical reachable vertex may satisfy both,
and a historical touch need not be owned by the component created by that
touch's reservation. The next theorem must therefore reason about intersection
with the exact current run carrier, not assert global disjointness or
absorption between the two provenance classes.

`SequentialFigure7TouchOrigin.lean` opens the prior-touch alternative without
weakening its provenance. `SourceLeftChain.reachable_of_head_mem` and
`NextAxiomRoute.touched_sourceLeftRegion` place every trace or terminal-endpoint
touch in the exact historical source-left region. The indexed
`CanonicalTouchOrigin` then follows an authentic `CanonicalTagHistory` back to
one stored event witness carried by that tag augmentation, and
`reservationRegion` recovers the submitted slot, oriented terminal axiom,
reachability, and region membership. This does not relate that old event to a
current component or raw age; those are separate ledger/realization layers.

`SequentialFigure7ReservationLedger.lean` supplies the history layer's first
of those two missing pieces. `ReservationEvent` is inductive over exact
initialization and `NewStep` evidence, so callers cannot forge an event from a
raw state or choose an unrelated search result. Folding those events through
`CanonicalTagHistory` produces an oldest-first ledger whose raw-age projection
is exactly `List.range final.stack.nextAge`; an allocated raw age therefore has
an exact event lookup. Its chronological submitted slots are the reverse of
the legacy newest-first `linkIndices`, and every `CanonicalTouchOrigin` maps to
a ledger member that really touched the vertex. A local bridge also separates
the old selected active age from the fresh reservation age by a strict
inequality. This ledger is historical: it neither realizes an old reservation
as a final live component nor turns an arbitrary touched route vertex into
current ownership. Raw event age, final representative, reserved axiom
endpoints, and all vertices touched by the historical search remain four
distinct notions.

`SequentialFigure7TouchCompleteness.lean` identifies two of those historical
notions without collapsing them into current ownership. Structural
well-formedness makes the stored successful source-left run complete for the
event's whole structural region: a region vertex lies in the exact trace or is
the terminal partner. The event wrapper reconstructs that run from its
initialization or `new` equation, yielding
`ReservationEvent.touched_iff_sourceLeftRegion`. A bare
`ReservationSearchEvent` is not covered by a corresponding theorem in this
module; the current proof uses the equation retained by `ReservationEvent` and
makes no claim about whether route-only data would suffice. The equivalence
says nothing about current representatives, candidate regions, owners, or
progress.

`SequentialFigure7CrossRepresentativeInvariant.lean` defines the exact
future-work side of the next history invariant. A ready occurrence retains the
same list position in `sigma` and `ready`; a waiting occurrence retains the
exact initialized waiting cell. `WaitingSpanExact` prevents an arbitrary
initialized but semantically dead cell from entering the live boundary set.
Consequently every `FutureWorkAt` boundary belongs to `sigma`, is below the
allocation horizon, and is a current union-find root. A
`FutureNewCandidateAt` additionally retains its exact tensor-below witness and
the opposite premise's raw-unmarked lookup.

The history-indexed `OlderSourceRegionSeparated` quantifies over exact members
of the chronological reservation ledger. Its antecedent is
`representative event.rawAge < representative candidate.rawAge` in the
*current* production state. It neither compares immutable allocation ages nor
requires disjointness for a candidate below an event in current component
order. The consequent separates the two complete structural source-left
regions, including terminal partners. Empty history is vacuous; after exact
initialization every candidate boundary and the only event occupy the same
representative, so the strict antecedent is impossible. This foundation does
not yet prove preservation by later Figure-7 transitions. In particular, new
ready/waiting conclusions created by `new`, `wait`, `forward`, and `unify`
require genuine region-disjointness arguments, not merely field transport.

`SequentialFigure7OlderEventTouchSeparation.lean` gives that same invariant a
proof-friendly historical form without changing its domain. An authentic
event is `TouchSeparatedFrom` another start exactly when its complete
source-left region is disjoint from the other region, with structural
well-formedness needed only for the touch-to-region reverse direction. The
history wrapper retains the exact ledger membership, future candidate, and
strict current-representative premise of `OlderSourceRegionSeparated`; the two
predicates are equivalent under `StructurallyWellFormed`. This module does not
establish either predicate for all histories or discharge a rule-created
candidate obligation.

`SequentialFigure7SameRepresentativeEventTouch.lean` handles the equality
case for exact historical reservation events. A touched vertex structurally
reaches the event's stored-left axiom endpoint; exact reservation realization
and representative equality align that endpoint with the active occurrence
component. Source-left paths on both sides plus the component-internal path
would bypass the selected tensor conclusion in the reference switching, which
declarative correctness forbids. This theorem does not reconstruct a fresh
run and does not cover a strictly older event, an old marked owner, or any
rule-created candidate preservation premise.

`SequentialFigure7CrossRepresentativeStablePreservation.lean` discharges the
field-transport part exactly once. `FutureWorkAt.beforePrepared` restores the
selected head only in the old active ready bucket while preserving every
surviving occurrence's common `sigma`/`ready` position; waiting storage is
unchanged. The prepared core changes only the selected raw mark, so all
union-find representatives are identical before and after. A future tensor
candidate whose mate remains unmarked cannot use that selected head and is
therefore already a valid input candidate. The generic preservation theorem
still requires a concrete output equality and equality of complete
reservation ledgers, since the prepared middle state has no independent
history edge. Canonical `concl` and `nop` provide exactly those equalities and
preserve the invariant. Candidate-creating branches remain separate proof
obligations rather than consequences of this transport lemma.

`SequentialFigure7CrossRepresentativeNewPreservation.lean` isolates the New
branch's two genuinely new effects. Every output work occurrence is either
retained marked-middle work or one of the reached/partner endpoints appended
at the fresh boundary. The new reservation event itself is a fresh maximal
root and therefore cannot satisfy the strict-older antecedent against any
output candidate. `NewCreatedCandidate` records only an appended endpoint's
actual tensor-below witness and marked-middle unmarked mate. Conditional
preservation consumes `NewCreatedRegionSeparated` for prior ledger events
whose marked-middle representative is strictly smaller than the fresh root.
That side condition is not derived from the scheduler invariant, so the module
makes no unconditional New claim.

`SequentialFigure7CrossRepresentativeWaitPreservation.lean` isolates the
first such branch without assuming its missing geometry. Exact waiting-cell
equations classify every post-Wait future-work occurrence as either retained
middle-state work or the conclusion inserted at the destination boundary.
The retained case transports through the stable theorem. The inserted case is
captured by `WaitCreatedCandidate`, which stores only its tensor-below witness
and middle-state mate-unmarked lookup. Conditional preservation then consumes
`WaitCreatedRegionSeparated`: prior ledger events with a strictly smaller
middle-state representative must have source-left regions disjoint from that
new tensor mate's region. This side condition is the open geometry itself, not
a renamed output invariant, executor equation, or reachability premise. The
module therefore proves no unconditional Wait preservation.

`SequentialFigure7CrossRepresentativeForwardPreservation.lean` isolates the
same candidate-creation seam for Forward. Exact active-ready equations classify
every output future-work occurrence as retained prepared-middle work or the
submitted par conclusion inserted at the active boundary. Production-side par
queuing preserves marks and union-find parents, so retained candidates use the
stable theorem. The inserted case is represented by
`ForwardCreatedCandidate`, which stores only the tensor-below witness and
prepared-middle mate-unmarked lookup. Conditional preservation consumes
`ForwardCreatedRegionSeparated`: every strictly older prior ledger event must
have a source-left region disjoint from the created tensor mate's region. That
side condition is not derived from the current scheduler invariant, and the
module makes no unconditional Forward claim.

`SequentialFigure7CrossRepresentativeUnifyPayloadPreservation.lean` isolates
the representative-changing arbitrary-payload Unify branch. Exact stack
equations cover every output future-work occurrence by a same-boundary
survivor, an active-ready item moved to the previous boundary, or the sole
inserted tensor conclusion. The alternatives need not be disjoint. The tensor
union redirects exactly the prepared active representative class to the
previous root; payload activation changes no parents. Since every output
candidate boundary is at most the surviving previous boundary, a prior event
that is strictly older after the step cannot have belonged to the retired
class. Survivors and moved candidates therefore transport to the prior
invariant. The inserted conclusion is handled only under
`UnifyPayloadCreatedRegionSeparated`, which quantifies prior ledger events and
actual created candidates in the prepared state and does not refer to the
desired output invariant. The module makes no unconditional Unify claim.

`SequentialFigure7ReservationRealization.lean` supplies the second missing
piece for the reserved axiom itself.  Under explicit certificate structural
well-formedness, an event-specific
`OccurrenceDerivation` is transported across unchanged prefixes, fresh axiom
append, par extension, tensor union, arbitrary waiting-par activation folds,
and the complete canonical dispatcher.  It retains the event's exact submitted
axiom slot at the live component indexed by the event raw age's current
representative.  `OccurrenceDerivation.owned_unique` then aligns that
event-specific derivation with the final invariant forest, so both exact axiom
endpoints are in the same accounted owned list.  Different event raw ages may
resolve to one final component, as the checker-accepted two-axiom tensor union
consumer demonstrates.  This does not make all historical trace vertices
owned, preserve one component per event, or solve current-route intersection.

The layer also exposes the precise conditional seam for the remaining
geometric argument. If every vertex in the structural source-left region is
proved free of the two remaining historical obstruction forms under
correctness, the structural dichotomy yields a
formula-budget `FreshSourceLeftRun`; existing route, queue-history, and capacity
bridges then yield `NewInputNecessary` and input-only `NewEnabled`. Conversely,
once an exact run is already supplied, its own input-false tags and
raw-unmarked carrier separate it from prior touches and old marked owners.
`SequentialFigure7RegionBoundaries.lean` exposes these two run-indexed
theorems over `trace ∪ {partner}` and no larger structural region. That
converse separation does not construct the run from shallow `NewGuard`, so it
cannot be used circularly as the missing clear-premise proof. The companion
consumer freezes both a correct canonical touch/owner overlap and a deeper
correct initialization touch that remains unmarked and outside its event's
final-component owned list. No
dispatcher progress or totality, pure-worklist completeness, fallback removal,
or complexity bound follows here.

The root executable `ProofNetIRNewProgressAudit.lean` is a bounded
falsification layer over that boundary. It never inserts arbitrary states:
each path begins with `initializeReservation?` and recursively applies the
canonical `dispatch?`, carrying `ReachableByImplementedDispatcher` and deriving
`SchedulerInvariant` from the actual history. At each state it independently
reconstructs `NewGuard`, calls the actual `new?`, and hard fails with a complete
replayable witness on a mismatch. The default CI corpus is finite at seed 0,
depths 0 through 4, every formula start, and six labelled order variants;
`--extended` adds depth 5. Candidate acceptance uses `unificationCheck` and the
kernel equality `unificationCheck_eq_check`; a direct all-switchings sentinel
remains at depths 0 through 2. This executable architecture supplies regression
evidence and diagnostics, not a `NewGuard` success converse or a scheduler
progress theorem.

The same executable's `--cross-representative-search` mode maintains a
lightweight raw-age and source-start ledger that mirrors exact initialization
and successful `new` allocations. The legacy `--wait-search` spelling selects
the same bounds and hard gates. It decodes successful canonical New, Wait, and
Forward transitions, detects when an appended endpoint or inserted conclusion
is a genuine future-New tensor candidate, and checks every strictly older
prior-event pair by computing both complete structural source-left regions,
including terminal axiom partners. Decode, ledger-horizon, and
region-computation drift fail closed. The New decoder independently replays
the full reservation transition and checks fresh-root and old-representative
transport. The Wait decoder requires the exact old-to-new
`conclusion :: oldPayload` update; the Forward decoder independently replays
prepare, submitted-par lookup, paper guards, par queueing, active-ready
prepend, and the complete output state. Separate hard gates require nonzero
step, endpoint-kind, created-candidate, and strict-pair coverage. The frozen
depth-5, 16-seed corpus covered 1,182,816 reachable states. New contributed
328,848 steps, 222,246 created candidates (59,706 reached and 162,540 partner),
and 3,333,924 strict pairs. Wait contributed 5,682 steps, 636 candidates, and
1,068 pairs; Forward contributed 158,766 steps, 33,582 candidates, and 117,324
pairs. All three had zero intersections and zero decoder or region failures.
Those numbers are finite falsification evidence and discharge none of
`NewCreatedRegionSeparated`, `WaitCreatedRegionSeparated`, or
`ForwardCreatedRegionSeparated` in Lean.

`Unification.lean` contains the narrower production-core
`queuePar?`/`queueTensor?` mutations. They reuse the actual frontier picker and
component constructors and preserve raw marks so the queued conclusion is not
prematurely assigned. Separate theorems preserve formula consistency only
from a prior `ComponentsFormulaConsistent` invariant plus an explicit
`LinkWellFormed` hypothesis; the helpers themselves have no certificate
argument. Abstraction, ordered parents, carrier sizes, and
reservation-counter alignment are preserved locally. The tensor helper
merges generic guarded representatives by `min`/`max` and increments only the
tensor's own counter. `SequentialSchedulerState.lean` independently provides
`prependReadyTop?` and a two-level `mergeTopReadyWaiting?`; the latter chooses
the deterministic internal order
`conclusion :: (payload ++ previousReady ++ activeReady)`, drains the previous
waiting cell, makes it the undefined active boundary, and pops one stack
level. The paper's cells are sets, so the list order is an executable project
choice. Component-frontier derivation/exchange order is not scheduler-ready
list order; the eventual wrapper must relate them by membership/permutation,
not definitional list equality. Shape preservation requires explicit merged
`Nodup` and payload-bound proofs and performs no global queue scan.
The successful local `forward?` now composes `queuePar?` with the active-ready
prepend. The primitives remain independently useful lower-level mutations and
do not by themselves state a complete rule.
Directly composing `queueTensor?` with `mergeTopReadyWaiting?` without the fold
cannot establish the intended local construction: the stack move exposes
delayed conclusions before the production core has built their par
derivations. `UnifyPayload` now inserts the exact stored-order fold between
those operations and proves the total `1 + |W(j)|` counter equation. What
remains open for payload length at least two is deriving the explicit enabled
predicate exhaustively at the selected reachable dispatcher branch and global
progress, not conditional applicability, the local tensor/fold/drain
composition, or successful-step transport of the occurrence-exact
component/scheduler invariants.

`SequentialSchedulerInvariant.lean` now supplies that semantic foundation
without defining reachability in terms of the invariant. The bundle carries
`StructurallyWellFormed` explicitly. `ComponentDomainExact` identifies raw live
component slots with `sigma` boundaries;
`ReadyBucketFrontierExact` relates each aligned ready bucket by membership to
the raw-unmarked frontier of that live component; live frontiers and the
combined ready/waiting queue are globally `Nodup`, every queued occurrence is
raw-unmarked, and `PendingPremisesCoveredExceptReady` keeps marked premises of
not-yet-constructed connectives on a live frontier. `Produced` records
observable production by a concrete raw mark or live-frontier membership,
while `ProducedPremisesMarked` requires concrete raw marks on both submitted
premises of every such par/tensor. Combined with the pre-prefix unmarkedness
of a selected ready premise, this is the necessary causal contradiction for
an observably produced conclusion. It does not yet bind internal
derivation-tree nodes to exact certificate-link occurrences: repeated formula
labels make `FormulaConsistent` insufficient for that purpose.
`WaitingSpanExact` records
each delayed par's unique submitted producer, raw-unmarked conclusion, two
marked premises, and strict older-to-younger scheduler span; and
`FiredCounterExact` counts logical
connective constructors actually present in live component trees. The exact
empty state and every successful initial reservation on a structurally
well-formed certificate satisfy their combined `SchedulerInvariant`. The
initial proof explicitly handles the possible search/submitted axiom
orientation reversal. The common `PreparedStep` additionally preserves all
current state-only fields. Its proof uses the active top boundary to recover
the exact live component, removes the selected occurrence extensionally from
the ready/frontier correspondence, transports ready/waiting global `Nodup`,
and handles the new raw mark either as an old marked premise or as the
selected live-frontier premise. Exact `concl`/`nop` witnesses and their
successful executables inherit this result through `prepared.after`.
`SequentialComponentProvenance.lean` separately provides occurrence-faithful
internal component provenance without changing the runtime representation.
Its inductive relation records exact submitted link positions, exact
first-occurrence derivation focuses, complete owned formula vertices, and
exchange permutations. Local witnesses require `Nodup` link/vertex
accounting; the proof-only forest assigns a witness to each live raw slot,
requires cross-slot disjointness, binds every marked owned vertex's raw age
to that exact representative slot, keeps every unmarked owned vertex on the
same frontier, and conversely assigns every concrete raw mark to the component
at its representative. It implies `FormulaConsistent`, initializes on exact
submitted axiom reservations, and has sound local par/tensor queue extensions.
The queue witnesses do not carry certificate link identity, so
those extensions correctly require the submitted link index and lookup from
the future rule wrapper. A concrete repeated-label fixture shows why this
extra relation is necessary. Two additional predicate fixtures reject
cross-representative ownership and a forest-external raw mark.
The forest is now a `SchedulerInvariant` field. The empty core and exact
initial axiom reservation establish it, and a generic raw-mark theorem
preserves it when the selected occurrence lies on the live component at its
current representative. `PreparedStep` supplies that owner exactly, so
`concl`/`nop` inherit the strengthened invariant. The deterministic
`NewStep` proof now closes its successful-transition obligation as well: old
owned but unmarked occurrences are forced into the old queue, the submitted
axiom endpoints are excluded from that queue and hence from every old live
frontier, and the exact fresh axiom witness extends the forest. The same proof
transports all other current state-only fields, so
`NewStep.schedulerInvariant` and `new?_schedulerInvariant` cover every
successful typed/executable `new`. They do not show that `new?` returns `some`
for every intended later state and do not establish reachability. Successful
typed/executable `wait` now preserves the same complete state-only invariant:
the prepared state supplies the existing live owner, exact submitted-par
source lookup fixes positional identity, and the waiting-cell cons preserves
the global queue while adding one strict waiting span. Successful
typed/executable `forward` preserves that invariant through exact submitted-par
construction, live-frontier replacement, active-ready insertion, unchanged
waiting spans, pending-premise transport, and exact counter increment. Its
extra ready-list `Nodup` guard is only fail-closed shape validation. Independent
Boolean-free `ForwardRule` semantics and successful-step correspondence are now
present. The bounded Boolean-free `UnifyEmptyRule` and strict-singleton
`UnifyOneRule` executable correspondences are also present; every successful
typed/executable bounded step preserves this stronger state-only invariant.
The arbitrary-payload production-core fold and atomic `UnifyPayload`
composition are present. The latter now preserves the component forest and
complete `SchedulerInvariant` on every successful step from a full input
invariant, without an intermediate-state claim. Conditional `UnifyPayload`
applicability from input-only `UnifyPayloadEnabled` plus that invariant is now
proved. The invariant alone does not imply the predicate.
Forward/UnifyOne applicability, exhaustive `UnifyPayload` branch enabledness,
later-state totality, dispatcher progress, and
scheduler/pure-worklist completeness remain open.
In particular, the local `wait?` only records a waiting promise; it does not
falsely count that par as already constructed.

The local atomic arbitrary-payload transition, conditional input-only
applicability, and successful-step occurrence-exact invariant preservation are
implemented. Derivation of `UnifyPayloadEnabled` from reachable intended branch
states, exhaustive dispatcher enabledness, generalizing whole-history
oriented-route laws, unconditional
full-rule reachability, later-state totality, correct-state progress,
pure-worklist completeness, fallback removal, faithful
`NEXTAXIOM`/token-age sequencing, and whole-program linearity remain open. The
atomic rule connects the head-to-tail fold to one tensor and the scheduler
drain, derives total `1 + |W(j)|` accounting, and transports the complete
state-only invariant through a transient fixed-final-stack gap proof. Future
guards must continue to compare
raw assigned ages, not union-find representatives. The current global
ready/waiting absence check scans stored lists and is not a linearity result.
The separate event-driven worklist tier described next is already implemented.

The next executable layer,
`Certificate.unificationWorklistFastCheck`, precomputes an occurrence-to-link
consumer table. Newly marked conclusions enqueue only their consumers; tensor
unions requeue a deduplicated flat set of waiting par links. Its generated
derivation crosses the same independent verifier, so Lean proves worklist
success sound and the worklist-first fallback wrapper equal to `check`.
The proof layer also charges all successful dependency and waiting insertions
to distinct submitted-link firings, proves the cumulative total fits
`n(n+4)+1`, and proves that the canonical run exhausts its concrete queue
within that budget. At quiescence, every submitted but unfired connective is
kernel-classified as idle, a distinct-thread waiting par, or a same-thread
tensor deadlock. A least-formula-complexity argument then recovers a concrete
submitted source whose premises are already assigned, so an incomplete
canonical run cannot be witnessed only by an idle premise.

This flat scheduler has no Figure-7 token-age interval or LIFO invariant. A
stable small accepted certificate starts three axiom tokens in ages 0, 1, and
2; reverse connective queuing fires a tensor over ages 0 and 2 first. The
worklist succeeds in two attempts with zero waiting requeues and two successful
firings. These public counts are a regression receipt, not an observation of
the internal class: the noncontiguous merge follows from the fixed links and
the eager-start/reverse-queue definitions. Likewise,
`tagSchedulerFamily.step` indexes one selected waiting-dependency segment,
not firing time, token age, or stack depth.

Two broader confluence observations are too fine. Exact executable-state
confluence fails even on a derivation-generated correct certificate, and
structural-only confluence fails on a structurally well-formed certificate.
The remaining candidate quotient keeps exactly the marked occurrence domain
and the induced occurrence-thread partition. No committed reproducible
artifact, local-diamond theorem, confluence result, progress theorem, worklist
completeness result, or complexity bound currently follows.

A separately proved active-reference invariant connects every semantic thread
by already active all-left switching edges. Closing such a path with the two
fixed edges of an unfired same-thread tensor would form an edge-simple
reference-switching cycle, so declarative correctness excludes that
obstruction. Reachable-state semantics also proves causal marking closure and
the converse edge invariant:
active-reference walks between marked occurrences are equivalent to
  union-find thread equality. The remaining missing progress argument is now
  path-localized and cycle-indexed. Occurrence-aware tree-edge exchange first
  supplies an exact reference simple path between each waiting par's premises.
  For a fully reflexive dependency cycle, Lean flips every such path to the
  complementary backward-right-par/reversed-suffix traversal, proves each
  segment vertex-simple and target-left-avoiding, and composes the family into
  a nonempty closed cyclically nonbacktracking walk. Every internal transition,
  adjacent segment junction, and cyclic closing junction is cusp-free. The
  unavoidable concrete par pair is now localized across two distinct indexed
  segments: its omitted right occurrence is the source-segment head, and its
  retained left occurrence cannot inhabit that same vertex-simple traversal.
  Prefix injectivity further makes the common conclusion a non-start vertex
  reached in the holder segment's target list, with the holder edge proved
  exactly retained-left and the source head proved exactly omitted-right.
  The holder segment is split there into a nonempty incoming simple path and
  an outgoing simple path whose only common vertex is the conclusion; the
  retained-left occurrence is assigned to the orientation-correct side.
  An exact before/middle/after decomposition orders the two indexed conflict
  segments, and cutting the cyclic family at the shared conclusion constructs
  two closed full-graph arcs. The first is nonempty and contains the omitted
  right occurrence; the retained left occurrence is assigned to one of the
  two, and together they cover the flipped occurrences up to the induced
  cyclic-rotation permutation. The exact rotation equation transports internal
  cusp-freedom to the rotated concatenation and hence to each arc separately.
  A forward retained-left occurrence is now the incoming chord path's exact
  last edge, while omitted-right is the first arc's exact head; their new
  closing turn is proved to be a par cusp. A backward retained-left occurrence
  is the outgoing chord path's exact first edge and the nonempty second arc's
  head. The backward closing turn is now fully classified: the rotated
  concatenation's closing boundary is cusp-free, and the two reversed chord
  incidences have the same par color, so the second arc closes cusp-free at
  every possible last edge. It is consequently a nonempty closed cyclically
  nonbacktracking walk, and it is strictly shorter than the original flipped
  walk because the first arc is nonempty. It is not yet an
  `EdgeSimpleCycle`, since vertices can repeat. Pure completeness therefore
  now transports pointwise scheduler provenance and reference retention along
  the strict descent. Correctness supplies another exact backward-right par in
  the shorter arc; its omitted right is the head of one classified flipped
  segment, its retained left lies in a distinct classified segment, and their
  conclusion is the first segment's start but an internal target of the
  second. A generic cyclic scheduler-subarc state now retains the closed walk,
  internal and closing cusp-freedom, forward reference retention, pointwise
  scheduler provenance, and the located par chord across arbitrary cuts. After
  rotating omitted-right to the head, a backward retained-left starts a
  strictly shorter state. Every step records the exact larger-list rotation
  and the smaller contiguous cyclic interval in a proof-relevant descent trace;
  well-founded recursion on list length therefore reaches a terminal forward
  retained-left par-cusp interval while preserving an interval-cut trace back
  to the original flipped family. Every backward cut now shares one indexed
  witness with the positioned par obstruction that generated it. The terminal
  object similarly binds its generator, arc, exact complementary cyclic
  interval, derived strict cut, closed complement walk, reverse-shell
  normalization, and nesting trace. This complement is nonempty, closed,
  internally cusp-free, and strictly shorter. A kernel theorem shows that any
  closing cusp of the complement is necessarily the exact last/first reverse,
  because a nontrivial par cusp would violate the inherited boundary freedom.
  Ordinary loop erasure is not used: erasing at a repeated vertex can re-pair
  incidences and create a new closing cusp. Instead, proof-relevant cyclic
  normalization now strips exact first/last reverse shells and retains the
  positional context, length equation, pointwise scheduler provenance, and
  cyclic-interval descent. A cusp-free nonempty core recursively yields a
  strictly nested terminal forward cusp, so well-founded descent terminates at
  either an empty shell core or a scheduler-located nontrivial closing-par
  core. The empty alternative is now excluded directly: its nonempty opening
  is followed at the shell midpoint by the exact reverse of its last
  occurrence, which is necessarily a cusp and contradicts the inherited
  `CuspFreeTraversal`. The terminal proof object now binds its concrete cusp
  and scheduler coordinates to one position-aware obstruction, and terminal
  bases no longer admit unrelated duplicate existential witnesses. The next
  layer no longer
  treats an equal `DirectedEdge` value as an occurrence identity:
  `SchedulerOccurrence` tags every visit by its segment step and in-segment
  offset, the complete tagged family is proved duplicate-free, and erasure is
  proved to recover the original flattened traversal. Cyclic cuts and complete
  descent traces map from tagged occurrences to edge values. A general edge cut
  carrying exact append decompositions still has an existential positional
  lift to tags; this is not a canonical choice from repeated edge values. The
  terminal-complement path no longer uses that lift: its tagged complement and
  strict cut are fixed directly by the same indexed terminal witness. The
  cyclic state now retains a tagged descent from the initial
  family, inverts every surviving tag to its original segment/offset lookup,
  recomputes its positioned obstruction after each cut, and reaches the
  terminal forward cusp by tagged well-founded recursion. Tagged reverse-shell
  normalization is defined, erases soundly, and retains a source-fixed
  positional lift from each graph shell's stored
  singleton/middle/singleton decomposition. The terminal complement cut is
  derived without the first generic cut lift, and all later normalized cores
  retain exact tags through the complete nested-base recursion; the final
  tagged base carries one composed state-and-interval ancestry and its
  projected descent back to the original family. Every backward-chord
  constructor carries a generator-exact semantic cut whose positioned
  obstruction, endpoint tags, rotation, retained suffix, and strict interval
  are one witness. The terminal forward-cusp/complement constructor now has
  the analogous indexed relation, including its complement walk,
  reverse-shell normalization, and trace. This closes identity drift but does
  not itself replay the artificial closing seam.
  If that base has an empty core, every exact visit is now paired with a
  distinct reverse-valued visit from a different scheduler step; a same-step
  pair would repeat one edge index inside a simple path. Its terminal object
  retains the complement's exact closed-walk and cusp-free witnesses. The
  pairing makes every complement edge reference-kept, so the complement
  transports to a nonempty closed walk in the reference-switching tree, while
  the omitted/kept mask conflict excludes every scheduler-segment head.
  Lean also selects one concrete reverse pair, orients it by strict scheduler
  step order, and records the exact segment family before, between, and after
  the pair. A positive offset is now inverted to the concrete omitted head,
  retained suffix, and suffix walk to the classified target. Both endpoint
  segment heads are furthermore proved present in the initial tagged family
  and absent from the retained complement, yielding an exact head-skipping
  reverse chord. Each endpoint is now classified by its exact scheduler source,
  complete reference-kept suffix walk to the next scheduler conclusion, and
  the exact retained-left occurrence of that target waiting par avoided by the
  whole segment. This endpoint-classified terminal outcome is connected to the
  global fully reflexive dependency-cycle extraction. The two selected suffix
  occurrences are now transported to the compacted reference graph and proved
  to remain exact reverses. The empty shell is also retained as two nonempty
  reference walks through one midpoint; exact compacted index/orientation
  equations prove that its closing half is the complete reverse traversal of
  its opening half. This occurrence-exact shell nesting is exposed by the same
  global terminal outcome. The shell midpoint then gives the exact local cusp
  that rules out this branch; no tree-acyclicity claim about an arbitrary
  out-and-back walk is used. The sole surviving nontrivial closing-par base now
  retains exact first and last scheduler tags, source-segment/offset
  classifications, and reference retention of its forward last incidence. One
  dependent package now ties those tags to the same par link, normalized core,
  closed walk, and exact `first :: middle ++ [last]` split. Lean also proves
  that the resulting artificial closing seam is neither same-segment nor
  segment-boundary adjacent in the original scheduler coordinates.
  Generic cyclic-interval descent is not itself a convexity invariant because
  a nested cut may wrap around a boundary introduced by an earlier cut. The
  terminal base, its data-indexed global ancestry, the closing outcome, and the
  normalized endpoint split are now assembled into one exact closing package
  whose first three components share
  `(base, complementBase, taggedComplement, taggedNormalized)` and whose
  endpoint split shares the same `taggedNormalized`. The arc, rotations, link
  decomposition, occurrences, scheduler coordinates, and segments of the
  underlying `SchedulerTaggedTerminalComplementStepAt` remain existential
  inside the stored step wrapper, not global package indices. A private
  structural replay opens each wrapper once, reuses that same frame, and folds
  terminal, reverse-shell, backward-search, nesting, and global ancestry into
  both the older boundary cursor and an occurrence-position endpoint zipper.
  The zipper's gap is definitionally the complete complementary arc between the
  fixed tagged endpoints, not the cursor's candidate gap.

  Every indexed flipped segment is nonempty. Thus an empty exact gap in the
  initial tagged family would force the scheduler-coordinate adjacency already
  excluded by the endpoint witness; the exact gap is nonempty. More directly,
  the canonical endpoint replay of the fixed terminal step always first-opens
  before ancestry begins. Its first reverse-shell frame inserts
  `closing ++ opening`; when that list is empty, the generator's nonempty
  omitted arc opens the gap in the second frame instead. The construction
  retains
  `closing.map erase = reverseTraversal (opening.map erase)`, the omitted-right
  zero-offset backward anchor at the arc head, the forward retained-left last
  occurrence, and the exact base gap
  `closing ++ taggedArc ++ opening`.

  Erasing the outer `taggedArc` gives a closed `EdgeWalk` at the complement
  base and satisfies `CuspFreeTraversal` internally. Its exact cyclic closing
  pair from the outer last occurrence to the anchor is nevertheless a cusp,
  and those occurrences are not directed reverses. The closing cusp is
  therefore a wraparound fact rather than an internal turn forbidden by the
  linear cusp-free predicate. The shell case split constructs the
  first-opening proof, but the returned first-opening proposition does not
  expose a consumer-facing frame/origin sum or bind that frame to the anchor.

  Endpoint splices preserve the old complete gap as a sublist. The ancestry
  replay therefore transports the entire outer `taggedArc` in its original
  linear order into the initial scheduler-family gap, including its named head
  and last occurrences. A generic head/getLast-plus-sublist theorem now gives
  the exact decomposition
  `g0 ++ anchor :: g1 ++ outerLast :: g2`; combining it with the zipper
  rotation yields
  `CyclicFourPointDisplayAt firstTag lastTag anchor outerLast`. The generic
  relation allows empty intervening lists and repeated values. It is not the
  missing strict scheduler-rank theorem: this result establishes neither
  contiguity, a fixed linear rank, crossing, cyclic betweenness, nor a
  model-specific scheduler-order/proper-nesting contradiction. Closing-par exclusion and
  correct-state progress therefore remain open. Pure-worklist completeness,
  recursive-fallback removal, and whole-program linearity remain later gates.
  On the complete initial `tagSchedulerFamily`, exact scheduler coordinates are
  duplicate-free even when erased directed-edge values repeat. The four-point
  display therefore yields
  `[firstTag, lastTag, anchor, outerLast].Nodup`, but this does not imply
  distinct erased edges, edge endpoints, or vertices. The endpoint replay now
  also retains the exact outer positioned choice naming `anchor` and
  `outerLast`. Membership transport through ancestry lifts that same outer
  witness and the inner normalized closing witness to the complete initial
  family. A specialized theorem returns both positioned witnesses, the
  four-point display, and four-tag `Nodup` together.
  Their cyclic order is `firstTag → lastTag → anchor → outerLast`, so the inner
  and outer pairs are separated rather than alternating: this is not a crossing
  witness. No intervening interval is proved nonempty, and there is still no
  contiguity or fixed/modular rank. Ordinary laminarity permits these separated
  pairs as siblings, and the small accepted regression refutes generic flat
  token-age/LIFO containment. Exact-state and structural-only confluence are
  separately refuted. Flat-worklist completeness may still be proved through
  residual-parsing-witness preservation or a theorem modulo the
  marked-domain/occurrence-thread quotient. The bounded/tagged `NEXTAXIOM` and
  dynamic-start primitive is now kernel checked, including per-call trace/tag
  invariants, exact oriented routes, initial/local rank-scoped totality, and
  touched-set disjointness for successive calls that strictly thread
  `first.tags`. That result does not cover reset tag arrays. Later-state
  selection and faithful full `R`/`W` transitions are still required for the
  later Guerrini linearity layer. The independent delayed-state checkpoint
  already proves the raw-age `σ` partition, three waiting-cell states,
  reached/partner reservation order, and local shape preservation. The
  production bridge now adds typed initial/later wrappers, exact
  `some_iff` success witnesses, composable-call axiom-link-index replay
  exclusion under complete tag threading, later `RealizesSigma` preservation,
  and a `ReservationInvariant` preserved across initialization and later
  reservations, including the exact `OperationalWaitingDomain`. A shared
  public `ConsumerIndex` and the invariant-bound operational local Figure-7
  `new` pipeline now add pop/raw-mark, orientation-aware tensor-mate lookup,
  post-mark search, and later reservation with the old-boundary/fresh-top
  waiting update. Every successful typed/executable `new` now preserves the
  complete current occurrence-exact state-only `SchedulerInvariant`; the
  same is now true for every successful typed/executable `wait`, `forward`, and
  bounded `UnifyEmpty` and strict-singleton `UnifyOne`.
  None of these theorems supplies applicability, success, reachability, or
  totality. Reset
  tags can replay low-level
  search, but the operational
  stack guard rejects endpoints already stored in ready or waiting payloads;
  the low-level reservation primitive itself remains replayable. The
  proof-relevant `InitNewHistory` now characterizes exact empty/init/new
  executions and proves tag provenance, global submitted-slot non-reuse, and
  reservation-count alignment. This fragment is not a full reachable
  scheduler. The local `concl`/`nop`/`wait`/`forward` and compatibility
  `UnifyEmpty`/`UnifyOne` rules exist outside this reservation-only history;
  `wait` has exact-span/queue preservation and `forward` has
  exact submitted-par/forest/frontier/queue/pending/counter preservation, while
  bounded `UnifyEmpty` and strict-singleton `UnifyOne` preserve the same full
  state-only invariant. The local arbitrary waiting-payload fold and atomic
  `UnifyPayload` composition are also outside `InitNewHistory`, and successful
  atomic steps preserve the same complete occurrence-exact state-only
  invariant from a full input invariant. Pure input-only
  `UnifyPayloadEnabled` plus that invariant now implies executable success;
  the invariant alone does not imply the predicate. The separate canonical
  dispatcher history accounts for all six successful rule families.
  `SequentialFigure7TagHistory.lean` adds a branch-indexed augmentation of that
  exact history: only `new` records a `NEXTAXIOM` event, the other five branches
  preserve tags exactly, and current true tags are equivalent to recorded
  initialization/`new` touches. Touched sets are separated across the complete
  trace and submitted axiom-link positions are globally duplicate-free. The
  augmentation is derived from `ExecutedHistory`/certified reachability; it
  does not turn `SchedulerInvariant.tags_size` into tag provenance, and it does
  not prove the concrete same-sized all-true replacement unreachable.
  Canonical-history reservation counting is now exact against final
  `nextAge`; exhaustive branch enabledness, whole-history oriented-route
  generalization, and unconditional full-rule reachability remain open. Planarity
  is not assumed for
  commutative MLL. Closing-par exclusion, progress, and pure-worklist
  completeness remain open.
`Certificate.unificationCheck` now orders its tiers as worklist, eager scan,
then complete recursive reconstruction. This is still not Guerrini Figures
7--8 sequential unification: its production path still starts all axioms
eagerly and uses flat waiting requeues. The separate bounded/tagged
`NEXTAXIOM` primitive now has an exact initial/later reservation bridge and an
invariant-bound operational local `new` transition in the delayed
`SequentialSchedulerState`. The literal printed fresh-cell update remains a
separate display-only helper. Exact init/new execution history is integrated;
successful `new`, `wait`, and `forward` preserve the full current state-only
invariant, and Forward additionally has an independent Boolean-free direct
relation with exact executable correspondence. Bounded `UnifyEmpty` and
strict-singleton `UnifyOne` have direct correspondences, and their successful
typed/executable steps preserve the complete occurrence-exact
  `SchedulerInvariant`. The arbitrary production-core fold and atomic
  tensor/fold/drain `UnifyPayload` are present and preserve the complete
  occurrence-exact invariant on successful steps from a full input invariant;
  input-only `UnifyPayloadEnabled` plus that invariant proves conditional
  arbitrary-payload success. A canonical priority dispatcher and proof-carrying
  certified history now integrate every implemented successful rule family;
  its canonical tag augmentation proves exact touch provenance, global
  submitted-slot non-reuse, and exact reservation-event counting against final
  `nextAge` through stable and `new` branches alike. Exhaustive later-state
  branch enabledness/totality, unconditional full-rule reachability, and a public whole-history
  oriented-route theorem are not proved. General
checker-accepted sequentialization remains complete through the recursive
tier; recursive fallback removal and whole-program linearity remain separate
open gates.

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
