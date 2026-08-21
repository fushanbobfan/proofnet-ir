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

The canonical operational-`new` regression freezes one exact post-step state:
`μ(0)=0`, `σ=[0,1]`, `R=[[1],[2,3]]`, `W(0)=∅`, and `W(1)=⊥`. This is an
executable state-transition receipt for that fixture, not a general
queue-shape, reachability, progress, or complexity theorem.

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

`SequentialComponentSourceLeftGeometry.lean` supplies the complementary
occurrence-carrier theorem below the scheduler layer. If the source of a
`SourceLeftRegionVertex` belongs to an exact `OccurrenceDerivation` owned
list, every recursively visited stored-left occurrence and the terminal axiom
partner belongs to the same owned list. This is a structural carrier-closure
fact; it identifies no scheduler component and proves no chronological
separation, reachability, or progress.

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

`SequentialFigure7CommitmentSpine.lean` records the exact allocation ancestry
still visible in the final `sigma` stack. For every adjacent parent/child raw
age, the child ledger slot contains the authentic `new` event that selected
the parent and allocated the child. Concl, Nop, Wait, and Forward preserve the
stack; New appends the final edge; UnifyPayload pops only the active top edge.
This is a retained-boundary theorem, not a vertex-level path, target-avoidance,
queue-origin, raw-seam, enabledness, progress, completeness, or complexity
theorem. Boundaries removed by UnifyPayload are deliberately outside its final
state statement.

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

`SequentialFigure7ActiveRegionTouchOrder.lean` combines those equality and
strict-order interfaces. Ledger membership and `RealizesSigma` bound every
historical event representative by the active sigma root; the theorem above
excludes equality whenever the event touched the active mate region. Such an
overlap is therefore strictly older in current-representative order, and the
sigma-top interval law also makes its immutable raw age strictly smaller than
the active raw age. Under `OlderEventTouchSeparated`, that strict order rules
out every ledger-event touch in the active region and blocker provenance makes
every region tag `some false`. This remains conditional on the supplied
history invariant and does not construct a route/run, establish raw readiness
or queue capacity, prove `NewEnabled`, or discharge a created-candidate
preservation premise.

`SequentialFigure7ActiveConclusionTouch.lean` decomposes a reservation-event
touch of any future candidate tensor conclusion through the tensor's
stored-left premise. Depending on tensor orientation, the event must touch the
candidate mate or queued head. For the active candidate, the preceding
tag-freshness theorem eliminates the mate alternative, including when the
event has the active boundary itself, so an active conclusion touch implies an
active head touch. The head alternative remains: this layer does not prove the
conclusion untouched, exclude raw marks, construct a target-avoiding path,
discharge a created-candidate seam, or establish scheduler progress.

`SequentialFigure7ActiveRegionAvailability.lean` then runs the complete
structural source-left search against that tag-fresh region. A successful run
is upgraded by canonical queue history to `NewSourceRegionInput`, including
endpoint queue absence and fresh waiting capacity. A failed search is
classified, under declarative correctness, as a historical touch or an exact
old marked occurrence owner; tag freshness eliminates the touch. The resulting
dichotomy is therefore `NewSourceRegionInput` versus exact old owner, and then
`NewEnabled` versus exact old owner after consuming the existing
`FutureWaitingUndefined` history invariant. Only an explicit pointwise
no-owner premise closes `NewEnabled`; the module does not prove that premise or
global older-event separation.

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

`SequentialFigure7OlderEventFutureWorkTouchSeparation.lean` packages the
orthogonal queued-head obligation. Its history-indexed predicate excludes a
strictly older authentic ledger event from every future candidate's exact
queued head. Combining it with `OlderEventTouchSeparated` and the structural
mate-or-head decomposition excludes the same event from the candidate tensor
conclusion. Empty, structurally well-formed init, and Prepared/concl/nop
preservation are proved. The
predicate is not reconstructed from correctness, the state invariant,
canonical history, or queue provenance. This base layer alone does not cover a
candidate-creating rule. A downstream theorem closes the successful New case.
Later structural theorems derive the Wait, Forward, and UnifyPayload residuals
and then preserve the invariant. A capstone induction now establishes the
queued-head invariant for every structurally well-formed canonical history.
The separate global mate-region and raw-mark invariants remain open. A later
active-guard-local layer bypasses both for `NewEnabled`, but does not turn them
into preserved history invariants or establish dispatcher progress.

`SequentialFigure7OlderRawMarkedRegionSeparation.lean` adds the parallel
state-only raw-mark invariant. Its generic primitive takes a candidate raw age
and source-left start, so it also describes a rule-local candidate that has not
yet entered the ready or waiting queues; the bundled form quantifies over all
current future-New candidates. Empty and exact initialization have no raw
marks. The prepared prefix preserves the invariant because its sole new mark
is the active sigma top and cannot be strictly older than a surviving
candidate; all previous marks, candidates, and representatives transport from
the input. Exact `concl` and `nop` inherit that result. For an active
`NewGuard`, every concrete marked representative is at most the active root,
while same-representative correctness geometry excludes equality inside the
mate region. The resulting strict inequality lets the invariant exclude the
mark, and occurrence-exact component provenance converts that statement into
the owner-clear premise used by `ActiveRegionAvailability`. This is still
conditional: the module does not establish the raw-mark invariant for an
arbitrary history or preserve it through candidate-creating `new`, `wait`,
`forward`, or `unifyPayload`.

`SequentialFigure7ActiveRegionEnabledness.lean` bypasses that global
preservation requirement for one already established active guard. A concrete
raw mark in the active mate region determines its same-age authentic ledger
event and final owned component through `RawMarkReservationAnchor`. The active
source-left path and the event's owned path splice into an
`ActiveMateEventAnchor`, while representative order makes the event strictly
older; the local touch-separation layer rules out the anchor. This gives both
raw-mark absence and exact-owner absence. Canonical touch provenance separately
makes every active-region tag false. The structural run-or-blocker API can then
return only the run branch, which queue history, fresh capacity, and
`FutureWaitingUndefined` package as `NewSourceRegionInput` and input-only
`NewEnabled`. No executor result, output state, dispatcher choice, or newly
constructed history enters this data flow. Global preservation through
candidate-creating rules, exhaustive enabledness, progress, totality, fallback
removal, token-age scheduling, and whole-program linearity remain downstream.

`SequentialFigure7ReadyHeadDispatchResidual.lean` composes the occurrence-level
ready-head coverage with the stable enabled predicates, the preceding active
`NewEnabled` theorem, marked-tensor adjacency, and fixed dispatcher priority.
For an already supplied `ReadyHeadInput`, its first theorem returns an inclusive
disjunction: an existential `PriorityEnabled` branch, or
`ReadyHeadMarkedTensorPredecessorGap`. The residual retains the exact tensor
consumer and mate mark, resolves that mark to a retained sigma boundary strictly
below the active top, and records only that no `SigmaPredecessorInput` identifies
it with the active top's immediate predecessor. The alternatives are not stated
as exclusive. Under `ReachableByImplementedDispatcher`, the positive branch is
lowered to an exact successful `dispatch?` equation. The module does not prove
that a semantic nonterminal state has a ready head or that the residual is
unreachable by itself.

`SequentialFigure7OlderMarkedTensorPredecessorInvariant.lean` supplies the
non-circular state layer immediately above that residual. Its indexed invariant
ranges over every `FutureWorkAt`, including ready-bucket members and waiting
work rather than only the selected head. When a marked tensor mate's current
representative is strictly below the work's current representative, it stores
the two adjacent sigma positions and the exact mate-boundary lookup. The
ready-head projection combines that carrier with the scheduler
invariant and returns the existing `SigmaPredecessorInput`; consequently a
supplied `ReadyHeadMarkedTensorPredecessorGap` is impossible whenever this
invariant is available.

The base layer proves the invariant for empty and initial-reservation states and
preserves it through the shared prepared prefix and the stable `concl` and
`nop` branches. `SequentialFigure7OlderMarkedTensorPredecessorNewPreservation.lean`
adds canonical `new`: retained work transports across the fresh sigma append,
while an old marked mate of a created endpoint is forced to the prior active
boundary immediately below the appended one.
`SequentialFigure7OlderMarkedTensorPredecessorWaitPreservation.lean` adds the
canonical successful `wait` case. Retained work transports through the prepared
prefix and the sigma-preserving destination update; private reference, touch,
and commitment geometry supplies the predecessor for the inserted conclusion.
The module now also exposes a source-visible conditional child-anchor bridge.
That bridge consumes strict older-event separation and an exact child-event
anchor; it does not derive either premise or prove branch applicability or
progress.
`SequentialFigure7OlderMarkedTensorPredecessorForwardPreservation.lean` closes
the canonical successful `forward` case. Retained work transports through the
prepared prefix, while private Forward history, component, and touch geometry
discharges the bridge premises for the inserted par conclusion. Its public
theorem requires declarative correctness, the complete scheduler invariant,
canonical history, typed Forward dispatch, a `ForwardStep`, and the supplied
prior predecessor invariant.
`SequentialFigure7OlderMarkedTensorPredecessorUnifyPayloadPreservation.lean`
closes the canonical successful `unifyPayload` case. Its carrier-free raw
touch dependency, `UnifyPayloadStep.createdConclusionTouchSeparated`, proves
that every strictly older prior event leaves the inserted tensor conclusion
untouched without requiring the future-candidate carrier used by the existing
wrapper. Retained candidates transport their predecessor evidence across the
final sigma pop. A moved active candidate would make its marked mate resolve
both to and strictly below the surviving boundary and is therefore impossible.
For the created conclusion, final component provenance constructs the exact
child anchor, and the raw touch result supplies the separation premise consumed
by the public conditional child-anchor bridge. The public preservation theorem
still requires declarative correctness, the complete scheduler invariant,
canonical history, typed Unify dispatch, an already-successful
`UnifyPayloadStep`, and the supplied prior predecessor invariant. The branch
prefix is therefore closed through UnifyPayload, but this transition module by
itself does not package the invariant over complete histories or prove
ready-head existence, applicability, dispatcher progress or totality, global
raw seams, fallback removal, faithful token-age scheduling, Figure-7
pure-worklist completeness, sequentialization, or whole-program linearity.

`SequentialFigure7OlderMarkedTensorPredecessorHistory.lean` packages that
closed prefix over every exact `CanonicalTagHistory`. Its induction handles the
empty and initial histories with the base theorems. In the later case it splits
the exact `DispatchStep` into all six rule constructors, recovers the typed step
from the stored executor equation, and applies the corresponding preservation
theorem. `ExecutedHistory.olderMarkedTensorPredecessorInvariant` obtains the
canonical history and exposes the result for every executed dispatcher history
under declarative correctness. Finally, at a dispatcher-reachable state with an
explicitly supplied `ReadyHeadInput`, the complete invariant rules out the
marked-tensor predecessor residual; the positive priority branch is lowered to
one exact successful `dispatch?` result. This history theorem alone does not
construct a ready head; the following structural module classifies the exact
shape of its absence, and the subsequent debt and continuation-exit layers give
conditional semantic reductions. The endpoint-locality obstruction below rules
out the unrestricted locality law as a full-history invariant across successful
Wait transitions. The queue-tail and history-tail layers then isolate one exact
caller-supplied carrier. The first-boundary parent-escape layer below instead
states what declarative correctness and the scheduler invariant force without
that carrier. The later re-entry-target classifier identifies the exact
submitted parent edge and reduces no-tail failure to selected-raw or
concretely-marked targets. Eliminating those cases remains before dispatcher
progress or later-state totality; global raw seams, fallback removal, faithful
scheduling, pure-worklist completeness, sequentialization, and whole-program
linearity remain separate.

`SequentialFigure7ActiveTopResidual.lean` removes the ambiguity in that gate.
`ActiveTopDrained` stores the last sigma boundary, its exact live component, and
the fact that no occurrence on that component frontier is raw-unmarked. In a
started state, stack well-shapedness aligns the last sigma and ready entries;
`ReadyBucketFrontierExact` identifies the final ready bucket with precisely the
raw-unmarked frontier of that live component. Splitting the bucket into empty
or nonempty cases therefore proves that absence of `ReadyHeadInput` is exactly
`ActiveTopDrained`. For a correct dispatcher-reachable state, the full-history
ready-head theorem lowers the nonempty case to an exact dispatcher result, so
the remaining outcome is an explicit dispatch-or-drained disjunction. The
drained branch is not called terminal and, by itself, does not imply
`core.allMarked = true`.

`SequentialFigure7ActiveTopMarkedNonconclusionDebt.lean` supplies the next
conditional layer. `ActiveTopMarkedNonconclusionDebt` says that every concretely
marked, nonconclusion occurrence on the active frontier has another
raw-unmarked nonconclusion witness on that frontier. The predicate holds for
empty and initial-reservation states. New establishes it without a scheduler-
invariant premise, Concl transports a prior instance, and Forward and
UnifyPayload establish it under the prior complete scheduler invariant when the
conclusion they create is not a global conclusion. Under declarative correctness
and the complete scheduler invariant,
`ActiveTopDrained` contradicts any outstanding debt witness and switching
connectivity then forces `core.allMarked = true`. This closes the conditional
state reduction, not its full history induction.

`SequentialFigure7ActiveTopDebtBranchResidual.lean` characterizes the four
branch-local boundaries. Given prior debt, post-Nop and post-Wait debt are
equivalent to the prepared prefix retaining a distinct raw-unmarked
nonconclusion after selecting its head. For global-created Forward and
UnifyPayload, the prior complete scheduler invariant makes post-debt equivalent
to marked-nonconclusion presence implying a non-global vertex in the exact
ready tail. Presence only detects vacuity. Canonical history derives neither
witness, so full debt preservation and downstream progress remain open.

`SequentialFigure7ActiveTopDebtQueueTail.lean` normalizes the selected-away
boundary without introducing another public predicate. Given the prior debt and
the input `SchedulerInvariant`, both Nop and Wait post-debt are equivalent to an
exact existential: `prepared.stackResult.remainingTop` contains a vertex that
is not a global conclusion. The reverse direction reconstructs the prepared
selected-away witness from ready-bucket/frontier exactness; the forward
direction extracts that tail vertex from the same exactness and ready-bucket
nodup. Neither theorem creates a tail witness from correctness, history, or
reachability.

`SequentialFigure7ActiveTopDebtHistoryTail.lean` packages those local
obligations as the reset-aware `CanonicalTagHistory.ActiveTopDebtTailLaw`.
Concl recurses unchanged. Nop and Wait require the current non-global
`remainingTop` witness and recurse to the prior law. New resets the obligation.
Forward and UnifyPayload also reset history recursion and retain only their
current exact alternative: a non-global created conclusion, or the existing
global-created ready-tail implication. Given a matching `CanonicalTagHistory`
and this law, the endpoint theorem derives
`ActiveTopMarkedNonconclusionDebt`. The law itself is an ordinary assumption;
the module does not derive it from declarative correctness, canonical history,
or reachability. In particular it gives no unconditional all-marked result,
progress, termination, totality, or completeness theorem. The parent-escape
reduction below neither requires nor derives this law.

`SequentialFigure7ActiveTopDebtParentEscape.lean` kernelizes the next bounded
first-boundary reduction. An explicit `ReadyHeadInput` whose
`ConnectiveBelow` witness is a `par`, together with declarative correctness and
`SchedulerInvariant`, exposes the active component occurrence/accounting data
and then returns either a non-global vertex in `readyTail` or
`ActiveCarrierParentEscape`. The latter is a marked non-global frontier premise
distinct from the selected vertex whose exact submitted connective parent
conclusion lies outside the active owned carrier. These outcomes are not
exclusive. The failure-conditioned wrapper proves that absence of the tail
witness forces the escape; it does not eliminate the escape.
`CanonicalTagHistory` appears only in the separate provenance theorem, where it
authenticates the escape's concrete mark as an earlier prepared-selection
event. No theorem in this layer assumes or derives `ActiveTopDebtTailLaw`. A
public computational coexistence receipt is not part of this checkpoint. The
downstream re-entry classifier identifies exact submitted-parent target status,
and its stored-right no-tail specialization eliminates the selected target.
The concretely marked target remains open. Unconditional progress, completion,
termination, totality, and completeness also remain open.

`SequentialFigure7ActiveTopDebtParentEscapeTemporal.lean` now normalizes that
failure-conditioned escape without assuming the tail law. With a matching
canonical tag history and the existing correctness/invariant receipts, the
par source is aligned to its authentic reservation event and its parent
continuation is raw-sibling, strictly older future work, or a strictly older
marked conclusion. The tensor source is aligned to the active representative,
while its sibling and conclusion are outside the active carrier; the existing
older marked-tensor predecessor invariant is retained, but its strict-order
trigger is not invented. The combined residual is an exact case split, not a
tail witness or an impossibility theorem. Eliminating these temporal residuals
and closing the global-created tail alternatives remain the next debt gates.

`SequentialFigure7ActiveTopDebtParentTemporalOutcome.lean` then consumes the
canonical continuation-credit theorem in the tensor same-boundary branch and
puts both source branches behind one endpoint-level interface. A raw sibling
is the selected head or lies outside the active owned carrier. Future parent
work and concretely marked parent conclusions lie outside that carrier at a
strictly older boundary or representative. The marked case can continue the
chain, so “outcome” does not mean terminal exit. This theorem is a common
temporal reduction target; it still supplies no distinct ready-tail payer
and proves no history tail law or residual impossibility.

`SequentialFigure7ActiveTopDebtParentExternalTemporalOutcome.lean` specializes
that target to actual Nop and Wait failures. Given the typed step, complete
input invariant, correctness, matching canonical history, and explicit absence
of a non-global prepared tail, the step guards eliminate the selected raw
endpoint. What remains is external raw work, external future work at a strictly
older boundary, or an external marked parent at a strictly older
representative. Here “external” means outside the active occurrence carrier;
the theorem does not return that endpoint to the ready tail. It proves no
re-entry, tail law, progress, completion, termination, totality, or
completeness result.

`SequentialFigure7ActiveTopDebtParentExternalCommitmentOutcome.lean` locates
the two strictly older branches on the retained `sigma` stack. It records the
last adjacent predecessor-to-active edge and the exact canonical commitment
reference path carried by that edge. The external raw branch is preserved
without inventing a boundary.

`SequentialFigure7ActiveTopDebtParentExternalEndpointCrossing.lean` uses the
active child occurrence of that commitment edge and reference-switching
connectedness to construct an exact simple path from inside the active owned
region to each older external endpoint. It retains a concrete stored-edge
occurrence whose source is active owned and whose target is outside. The
carrier does not retain a named child-endpoint equality or classify that edge
as a distinct raw payer, prove endpoint re-entry, derive the history-tail law,
or establish progress or completion.

`SequentialFigure7ActiveTopDebtParentExternalCommitmentReentry.lean` composes
all adjacent commitment paths across the positive retained `sigma` interval.
For ready future work and older marked endpoints, the result is an exact path
from the endpoint back into the active owned carrier and a concrete
outside-to-inside re-entry edge. The waiting branch retains its exact waiting
cell without inventing ownership, while the external raw branch is unchanged.
The re-entry edge is not classified as a distinct ready-tail payer, so this is
not a history-tail, progress, or completion theorem.

`SequentialFigure7ActiveTopDebtParentExternalReentryTarget.lean` classifies
that edge structurally. An outside-to-inside edge is the reverse of one exact
submitted connective-parent edge; its target is a non-global premise on the
active component frontier and its conclusion remains outside the occurrence
carrier. Exact ready-bucket accounting then splits the target into the selected
raw head, a raw ready-tail occurrence, or a prior concrete mark. Under the
explicit negation of a non-global tail, the middle case disappears. Canonical
raw-mark history authenticates a marked target and aligns its representative
with the active boundary. If the retained path also avoids the current par
conclusion, parent-link uniqueness eliminates the selected target, leaving a
distinct marked active-frontier premise. The module does not derive that path
avoidance, convert the marked history into a distinct payer, derive
`ActiveTopDebtTailLaw`, or prove progress or completion.

`SequentialFigure7ContinuationCredit.lean` and
`SequentialFigure7ContinuationCreditPreservation.lean` close a deliberately
weaker history invariant. `ContinuationCredit` records an unmarked connective
mate, scheduled work for the connective conclusion, or an already marked
conclusion. `MarkedNonconclusionContinuation` requires one such receipt for
every concretely marked nonconclusion. Fresh events receive a receipt in all
six dispatcher cases. The six branch transports plus the two dispatcher-level
transports need only structural well-formedness; Nop and New additionally use
the old owner's concrete mark, and the old-credit dispatcher theorem carries
that mark uniformly. Induction over an exact `CanonicalTagHistory` establishes
the state predicate without assuming declarative correctness. A receipt need
not be a distinct raw-unmarked occurrence on the active frontier, so this
full-history result proves neither the selected-away/exact-tail residuals nor
full `ActiveTopMarkedNonconclusionDebt`, semantic completion, or progress.

`SequentialFigure7ContinuationExit.lean` finitely normalizes that credit.
Every step follows a concretely marked, non-global connective conclusion and
strictly increases formula complexity, so the exit has one of three forms: an
unmarked raw mate, scheduled work for a future conclusion, or a concretely
marked global conclusion. Under the complete scheduler invariant and a drained
active top, eliminating the normalized receipt makes the raw endpoint
non-global and unmarked, or the future endpoint unmarked at a strictly older
boundary; the global branch retains its concrete mark. This normalization
requires an already supplied continuation receipt and does not establish
arbitrary history or state existence.

The same file keeps endpoint ownership separate. `LocalizedContinuationExit`
has only raw-mate and future-conclusion cases, binds that exact endpoint to one
component frontier, and deliberately has no marked-global case.
`ActiveTopContinuationExitLocalized` asks for this receipt at every marked
nonconclusion on the active frontier. Together with structural well-formedness
and `QueuedVerticesUnmarked`, the law yields
`ActiveTopMarkedNonconclusionDebt`; declarative correctness, the complete
scheduler invariant, `ActiveTopDrained`, and the locality law therefore imply
`core.allMarked = true`. Both implications remain valid.

`SequentialFigure7EndpointLocalityObstruction.lean` proves the exact limit on
that law. Every successful typed `WaitStep` from an input satisfying
`SchedulerInvariant` refutes `ActiveTopContinuationExitLocalized` at its output.
The law therefore cannot be an unrestricted invariant of complete canonical
histories across successful Wait transitions. The theorem proves neither that
the output is drained nor that any canonical history reaches a Wait transition;
it supplies no progress or existence result. It also does not refute direct
active-top debt or a Wait-compatible drained, temporal, or cross-component
weakening. The concrete `native_decide` trace used during research remains
outside the production theorem and public trust surface. Unconditional
progress, completion, terminality, and totality remain open. The subsequent
history-tail carrier is compatible with Wait, but remains assumed; the next
gate is to derive it from correctness plus `CanonicalTagHistory`.

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

`SequentialFigure7OlderEventFutureWorkTouchNewPreservation.lean` closes the
orthogonal queued-head invariant through an already-successful typed New step.
Retained candidates are transported through the prepared prefix. For a created
reached/partner endpoint, an old ledger-event touch would be both a prior
history touch and the current New search touch, contradicting canonical
cross-event disjointness. The fresh event is excluded by maximal raw-age order.
The theorem requires the prior canonical history and its supplied
`OlderEventFutureWorkTouchSeparated`; it does not derive global availability,
cover the same-boundary case or another candidate-creating rule, discharge a
raw seam, or establish progress.

`SequentialFigure7OlderRawMarkedRegionNewPreservation.lean` uses that exact New
candidate decomposition to close the parallel raw-mark transport once its
transition-local residual premise is supplied. Retained work uses prepared
preservation. For a created endpoint, reference-switching acyclicity excludes
the selected head from its source-left region in both tensor-complexity orders.
Thus only marks already present in the input remain to be separated from
created regions; `NewRetainedRawMarksSeparated` states precisely that
obligation. The fresh age is the marked-middle horizon, so no middle-state
future candidate can express this case through the old bundled invariant. The
module does not derive the residual premise from history or reachability and
adds no Wait, Forward, UnifyPayload, or progress theorem.

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

`SequentialFigure7OlderEventFutureWorkTouchWaitPreservation.lean` closes the
orthogonal Wait state transport under one exact transition-local head premise.
Retained candidates transport through the destination and prepared prefix.
For an actual inserted future-New candidate,
`WaitCreatedHeadTouchSeparated` states precisely that every strictly older
prior ledger event leaves the inserted par conclusion untouched. Wait adds no
reservation event, so there is no current-event branch. Relative to the
supplied prior canonical history and queued-head invariant, this premise is the
exact residual. The module does not derive it from the scheduler invariant,
history, or reachability and makes no unconditional/global Wait,
Forward/UnifyPayload, same-boundary, raw-seam, or progress claim.

`SequentialFigure7OlderEventFutureWorkTouchWaitDischarge.lean` discharges that
Wait created-head premise under structural well-formedness. A hypothetical
old-event touch of the inserted par conclusion continues through the exact
submitted par's stored-left premise. The premise is either the selected
occurrence or its already-marked mate, while reservation realization places
the event endpoint in its strictly older live carrier. Exact component-forest
disjointness excludes both orientations. A direct corollary therefore
preserves the queued-head invariant for an already-successful typed Wait step
from the supplied prior invariant without an explicit created-head premise.
It does not discharge `WaitCreatedRegionSeparated`, the raw seam, the final
equal-boundary commitment callback, global availability, or progress.

`SequentialFigure7OlderRawMarkedRegionWaitPreservation.lean` closes the
parallel raw-mark transport under one explicit transition-local premise. The
typed Wait inequalities give
`rep(destination) <= destination <= mateRawAge < selectedRawAge = rep(selected)`,
so the selected mark cannot be strictly older than a created destination
candidate. Retained candidates use Prepared preservation. Consequently only
input-retained marks against actual `WaitCreatedCandidate` regions remain, and
`WaitRetainedRawMarksSeparated` states exactly that obligation. It is distinct
from history-side `WaitCreatedRegionSeparated`, needs no declarative-correctness
or reachability witness, and is not derived by the module. The result is
conditional successful-step preservation, not unconditional Wait or progress.

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

`SequentialFigure7OlderEventFutureWorkTouchForwardPreservation.lean` closes
the orthogonal Forward state transport under one exact transition-local head
premise. Retained candidates transport through Prepared and the exact Forward
representative equality. For an actual inserted future-New candidate,
`ForwardCreatedHeadTouchSeparated` says precisely that every strictly older
prior ledger event leaves the inserted par conclusion untouched. Forward adds
no reservation event, so there is no current-event branch. Relative to the
supplied prior canonical history and queued-head invariant, this is the exact
residual. The module does not derive it from scheduler invariants, history, or
reachability and makes no unconditional/global Forward, UnifyPayload,
same-boundary, raw-seam, or progress claim.

`SequentialFigure7OlderEventFutureWorkTouchForwardDischarge.lean` discharges
that Forward created-head premise under structural well-formedness. An
authentic old ledger event places its stored-left endpoint in the old
representative's owned carrier. If it touched the inserted Forward conclusion,
the generic source-left carrier theorem would place the same endpoint in the
active par carrier. Strict representative order gives distinct live slots, so
component-forest disjointness yields a contradiction. A direct corollary
therefore preserves the queued-head invariant for an already-successful typed
Forward step from the supplied prior invariant without an explicit created-head
premise. It does not discharge `ForwardCreatedRegionSeparated`, the raw seam,
the separate final equal-boundary commitment callback, global availability, or
progress.

`SequentialFigure7OlderRawMarkedRegionForwardPreservation.lean` closes the
parallel raw-mark transport under one explicit transition-local premise. The
selected mark and the inserted Forward candidate have the same active raw age,
so their strict representative comparison is irreflexive. Retained candidates
use Prepared preservation. Consequently only input-retained marks against
actual `ForwardCreatedCandidate` regions remain, and
`ForwardRetainedRawMarksSeparated` states exactly that obligation. It is
distinct from history-side `ForwardCreatedRegionSeparated`, needs no
declarative-correctness or reachability witness, and is not derived by the
module. The result is conditional successful-step preservation, not
unconditional Forward or progress.

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

`SequentialFigure7OlderEventFutureWorkTouchUnifyPayloadPreservation.lean`
closes the orthogonal UnifyPayload state transport under one exact
transition-local head premise. Survivors reuse the prior invariant. Moved work
is recovered at the prepared active boundary, while strict output order proves
that an older event is outside the retired active representative class and thus
keeps its representative across the union. For an actual inserted future-New
candidate, `UnifyPayloadCreatedHeadTouchSeparated` states precisely that every
strictly older prior ledger event leaves the tensor conclusion untouched.
UnifyPayload adds no reservation event. Relative to the supplied prior history
and invariant, this is the exact residual. The module does not derive it from
scheduler invariants, history, or reachability and makes no unconditional or
globally available UnifyPayload, same-boundary, raw-seam, or progress claim.

`SequentialFigure7OlderEventFutureWorkTouchUnifyPayloadDischarge.lean`
discharges that candidate-indexed head premise under structural well-formedness.
The typed tensor queue combines the previous and active live occurrence
carriers. A hypothetical old-event touch puts its stored-left axiom endpoint in
that tensor output carrier, while reservation realization puts the same endpoint
in the event representative's carrier. Strict order separates the event from
both tensor-input roots in either orientation, so live-slot disjointness is
contradicted. The direct corollary still consumes the supplied prior invariant
and an already-successful typed UnifyPayload step. It does not close
`UnifyPayloadCreatedRegionSeparated`, the raw seam, the final equal-boundary
callback, global availability, or progress.

`SequentialFigure7OlderRawMarkedRegionUnifyPayloadPreservation.lean` performs
the parallel raw-mark transport across the representative-changing branch. A
strictly older output raw mark cannot belong to the retired active class:
after the union that class represents the previous boundary, while every
output candidate boundary is at most the previous boundary. Same-boundary
survivors and active-to-previous moved candidates therefore reduce to the
prepared-state raw invariant. Inserted tensor candidates use only
`UnifyPayloadCreatedRawMarksSeparated`, measured before the union. This raw
seam is distinct from history-side `UnifyPayloadCreatedRegionSeparated`, is
not derived from correctness or reachability, and gives conditional
successful-step preservation rather than unconditional Unify or progress.

`SequentialFigure7OlderEventFutureWorkTouchAvailability.lean` is the capstone
for the queued-head preservation family. It inducts over the proof-carrying
canonical history, using exact empty/initialization and all six successful-rule
theorems, and therefore derives `OlderEventFutureWorkTouchSeparated` from
structural well-formedness alone for any supplied canonical history. It does
not construct such a history, enlarge reachability, derive mate-region or
raw-mark separation, supply unconditional stored-left equal-boundary
avoidance, or prove
enabledness, progress, totality, completeness, fallback removal, scheduling,
or complexity.

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

`SequentialFigure7RawMarkReservationAnchor.lean` connects a concrete raw mark
to that realized reservation without identifying the mark with a historical
search touch. `SchedulerInvariant` first accounts for the marked occurrence in
its current representative component; the chronological ledger supplies the
authentic event at the same immutable raw age; reservation realization accounts
for both submitted-axiom endpoints there. Component and owned-list uniqueness
then align all three occurrences, and component reference geometry gives paths
from the mark to each endpoint that stay inside the common owned list. This is
local geometry within one current component. It does not cross adjacent
commitment-spine components, prove avoidance of a future tensor conclusion,
recover queue origin, discharge any raw seam, or imply progress.

`SequentialFigure7CommitmentEdgeReferencePath.lean` composes the exact local
anchors for one adjacent pair retained in final `sigma`. The commitment-spine
witness identifies the historical `NewStep`; raw-mark history keeps its selected
head marked at the parent age; the parent anchor, the step's tensor/source-left
path, and the child reservation anchor then loop-erase to a canonical simple
path from the parent event's stored left endpoint to the child event's stored
left endpoint. The result retains both final owned carriers and each segment's
exact endpoints. It is a single-edge path theorem, not a future-target avoidance
theorem: arbitrary chain composition, queue origin, created-candidate raw seams,
enabledness, progress, completeness, fallback removal, and complexity remain
outside this layer.

`SequentialFigure7CommitmentEdgeTargetAvoidance.lean` refines that one-edge
path under one explicit semantic law. For a supplied `FutureNewCandidateAt`,
or for the conclusion of a supplied ready-head par consumer, the exact child
ledger event must leave the target conclusion untouched. Ownership accounting
keeps either conclusion outside both endpoint carriers; producer uniqueness
and final mark equations exclude collision with the historical tensor
conclusion. The proof reconstructs an avoiding middle segment and composes the
three avoiding paths by verified loop erasure. This does not derive the
child-event untouched law or its global availability, compose a whole spine,
recover queue origin, discharge a raw seam, or imply progress.

`SequentialFigure7CommitmentIntervalTargetAvoidance.lean` supplies the
composition combinator for any positive-length retained-`sigma` interval. A
callback provides one target-avoiding witness for every adjacent edge in the
interval. Exact ledger lookups identify each shared middle event, and verified
loop erasure joins the paths while preserving their common avoidance target.
This closes explicit-callback interval composition only. It does not derive or
globalize the callback or child-event untouched laws, cover the zero-edge case,
recover queue origin, discharge a raw seam, imply progress, preserve segment or
parallel-edge identity, or establish a complexity bound.

`SequentialFigure7StrictCommitmentTargetAvoidance.lean` discharges those
callbacks for the strictly older slice. The complete scheduler invariant makes
every retained sigma boundary a current union-find root; strict sigma ordering
then transports strict oldness of an interval's final boundary to every child
inside it. `OlderEventTouchSeparated` and
`OlderEventFutureWorkTouchSeparated` exclude the corresponding child event
from the future tensor conclusion, so the one-edge theorem and positive
interval compositor yield canonical avoiding paths without a separate
`childUntouched` argument. The theorem still requires both supplied separation
invariants and exact sigma lookups. It does not cover an equal final boundary,
derive global availability, recover queue origin, discharge a raw seam, or
imply progress or complexity.

`SequentialFigure7StrictOlderSigmaSplit.lean` locates the retained interval
needed by that compositor. Starting from an authentic ledger event and a
future-New candidate with strict current-representative order, chronological
ledger bounds and `RealizesSigma` locate the event representative, while the
future-work witness locates the candidate root. Strict `sigma` ordering places
the former before the latter. The theorem then returns the candidate's exact
immediate predecessor and a possibly empty prefix from the event
representative. A positive prefix can use the strict interval theorem; a zero
prefix needs no edge composition. The final predecessor-to-candidate edge is
not discharged, and no global invariant, queue-origin, raw-seam, progress, or
complexity claim is added.

`SequentialFigure7EqualBoundaryCommitmentTargetAvoidance.lean` classifies the
remaining final edge. Stored-right orientation yields the canonical path
avoiding the active tensor conclusion. The general theorem is an inclusive
dichotomy: either such a path exists, or an authentic child event has the
active raw age, stored-left orientation, and an exact adjacent
conclusion-to-head trace fragment. The second branch records failure of the
generic child-untouched callback; it neither excludes every avoiding path nor
makes the two branches disjoint. For a current ready-head par conclusion, a
parallel inclusive dichotomy returns an avoiding path or an authentic same-age
event whose trace contains the exact conclusion-to-selected or
conclusion-to-mate step. It does not eliminate either par orientation. No
mate-region/raw-mark invariant, queue origin, reachability, progress, or
complexity result is added.

`SequentialFigure7CommitmentIntervalParConclusionDichotomy.lean` lifts that
classification across a complete positive retained interval. If every local
edge has a par-conclusion-avoiding path, the interval compositor returns one
endpoint path. Otherwise the theorem identifies an exact parent/child edge
without such a local path and an authentic event at the child age whose trace
contains the conclusion-to-selected or conclusion-to-mate step. Strict sigma
ordering places the child strictly before or at the final boundary. The outer
alternatives are inclusive; the theorem neither discharges the failed edge nor
derives a payer, tail law, reachability, progress, or complexity result.

`SequentialFigure7CommitmentIntervalParTraceLocalization.lean` sharpens that
failed branch relative to the active occurrence carrier. Live-carrier
disjointness rules out a strictly older trace to the selected head or to an
active-owned mate. Consequently every strictly older obstruction is
stored-right and traces to a mate outside the active owned carrier. At the
equal final boundary, both exact selected/mate trace orientations remain. The
outer alternatives are still inclusive; the theorem does not localize the
external mate further, eliminate the equal-final cases, derive a distinct
payer or tail law, or prove progress.

`SequentialFigure7CommitmentIntervalParGuardOutcome.lean` specializes the
localized interval to actual Nop and Wait steps. Its four-case carrier retains
the avoiding path, equal-final selected trace, equal-final mate trace, and the
strictly older stored-right mate. In the Nop theorem that mate is outside the
active carrier and raw-unmarked. In the Wait theorem it is outside, concretely
marked at the exact mate age, and has a representative strictly below the
active boundary. These are exact branch statuses, not a distinct payer or
history-tail result; the equal-final and inclusive alternatives remain.

`SequentialFigure7CommitmentIntervalParGuardReentry.lean` adds supplied
reference-switching connectedness to those typed outcomes. In the strictly
older branch, the exact raw Nop mate or older-representative marked Wait mate
now carries an outside-to-inside active-carrier path, one exact submitted
parent re-entry edge, and a target classification. The target is the selected
raw head, a non-global raw ready-tail occurrence, or a prior concrete mark.
The theorem does not eliminate the selected/marked cases, change the
equal-final or inclusive alternatives, derive the history-tail law, or prove
progress.

`SequentialFigure7CommitmentIntervalParGuardReentryFailure.lean` specializes
that older branch to exact failure of the non-global ready-tail obligation.
Because the selected par is stored-right while the switching graph retains the
stored-left parent edge, parent uniqueness and strict formula complexity rule
out the selected head as the inbound target. The remaining target is distinct,
concretely marked, authenticated by canonical raw-mark history, and represented
at the active boundary. The theorem does not eliminate that marked target or
the avoiding and equal-final branches, derive the history-tail law, or prove
progress.

`SequentialFigure7CommitmentIntervalParGuardReentryMateSeparation.lean`
strengthens that marked-target branch without changing its inclusive outer
shape. A retained simple path cannot revisit its external starting mate. If a
connective view at the exact marked target had the current selected head as its
mate, structural parent uniqueness would swap the two exact views and identify
the target with that path start. The new carrier records both separations. It
does not eliminate the marked target, choose its submitted source kind, recover
a ready-tail witness, derive the history-tail law, or close an avoiding or
equal-final branch.

`SequentialFigure7CommitmentIntervalParGuardReentryMarkedTargetTemporal.lean`
binds that same marked target to its unique submitted parent and exact inbound
source. Canonical continuation credit then yields three target-indexed cases:
the raw mate is unmarked and outside the active carrier, the parent conclusion
is queued at a strictly older boundary, or that conclusion is concretely
marked at a strictly older representative. The target's source kind remains
available through its exact consumer, but no case is eliminated and no
ready-tail witness, history-tail law, or progress theorem follows.

`SequentialFigure7CommitmentIntervalParGuardReentryMarkedTargetContinuationExit.lean`
follows a marked non-global parent through the existing finite continuation
normalizer. The terminal receipt is raw outside the active carrier, an exact
raw return to the current selected/mate pair, future work at a strictly older
boundary, or a marked global conclusion at a strictly older representative.
The return binds the terminal consumer to the current conclusion and records
strict formula-complexity growth from target to mate. It is a residual, not a
contradiction, payer, tail law, or progress theorem.

`SequentialFigure7MarkedTargetRawReturnCyclicReduction.lean`
splices the exact raw return into a closed walk in the full occurrence graph.
The prefix is lifted occurrence-for-occurrence from the reference switching;
the continuation tail is forward with no repeated target, and both segments
are individually nonbacktracking. Complete normalization is either the empty
splice or cancellation at one of their two oriented endpoint junctions. In a
nonempty cancellation, each segment has unique occurrence indices, every
prefix occurrence is backward and paired with its exact reverse in the tail,
and the tail ledger marks every reached prefix vertex as a nonconclusion.
Because the retained prefix comes from a simple path, unique outgoing sources
order the continuation tail as its exact reverse traversal.
Otherwise correctness exposes both exact premises of a par, with its kept
occurrence in the switching prefix and its omitted occurrence in the
continuation tail. The latter starts at a concretely marked nonconclusion in
the finite chain. Complete cancellation and the par-pair case remain residuals
rather than contradictions or ready-tail payers.

`SequentialFigure7MarkedTargetNopRawReturnElimination.lean`
removes the exact-return branch specifically for a successful typed Nop. A
nontrivial marked-conclusion chain has a concrete terminal mark, while the Nop
step keeps its current opposite premise raw-unmarked. The two facts contradict
an exact return to that premise. The refined Nop target still permits raw work
outside the active carrier, older future work, and an older marked global
conclusion. It neither changes the generic cyclic reduction nor eliminates the
corresponding Wait branch, and it supplies no tail law or progress result.

`SequentialFigure7MarkedTargetRawReturnFirstDescent.lean`
refines the exact-return branch that remains in the generic and Wait targets.
The re-entry premise is marked at the active representative, while its exact
submitted parent conclusion lies outside the active occurrence carrier. If the
marked-conclusion chain returns to the current mate, its first step therefore
lands at a strictly older representative. Canonical tag history authenticates
that first conclusion as a `RawMarked` event. The refined target retains raw
work outside the carrier, this first-step descent, older future work, and an
older marked global conclusion. The descent is not eliminated and supplies no
ready-tail, history-tail, completion, or progress theorem.

`SequentialFigure7RawMarkCausalOrder.lean` makes the chronological relation
between authentic prepared-selection raw-mark events explicit. A prior event
survives each later constructor, and any prior event precedes the current
event. The relation projects both endpoint events and makes their selected
occurrences distinct. For an authentically marked submitted connective
conclusion, both its queried premise and opposite mate have strictly earlier
authentic raw-mark events.

`SequentialFigure7MarkedTargetRawReturnCausalDescent.lean` combines that order
with the first representative descent. Both the re-entry origin and its
sibling mate precede the older marked parent conclusion; the sibling also
retains its finite continuation exit. The generic first-descent target and the
typed Wait outcome expose this refinement.
`SequentialFigure7MarkedTargetRawReturnTerminalCausalOrder.lean` proves the
strict event relation transitive and asymmetric. A finite marked-conclusion
chain is reflexive or places its origin before an authenticated terminal. The
target adapter and typed Wait theorem authenticate the outer mate as that
terminal. In the retained causal-descent alternative, the re-entry origin and
the first connective's sibling therefore precede the complete chain terminal.
No theorem eliminates the descent or sibling exit, makes the event order
total, derives a ready-tail/history-tail law, or proves completion or progress.
`SequentialFigure7MarkedTargetRawReturnSiblingExitCausalOrder.lean` makes the
authentic event order total on distinct vertices and provides the corresponding
equality-or-two-orders comparison. It keeps raw and future sibling exits
unchanged. A marked-global sibling endpoint is distinct from the non-global
outer mate and is therefore strictly earlier or strictly later. The generic
terminal target and typed Wait outcome preserve the first descent while adding
that endpoint classification. Neither ordered alternative is eliminated, and
the theorem derives no payer, tail law, completion, or progress result.
`SequentialFigure7MarkedTargetRawReturnSiblingExitCausalJunction.lean` applies
the existing exact cyclic-junction reduction to the complete marked-conclusion
chain retained by that same first descent. Its strengthened target stores the
cyclic-junction outcome beside the sibling causal classification on the same
switching path and target connective; the typed Wait theorem transports the
combined witness. It eliminates no junction, exit, descent, or ordered branch
and proves no payer, history-tail law, completion, or progress result.
`SequentialFigure7MarkedTargetRawReturnCyclicEndpointCausalOrder.lean`
strengthens only that aligned branch. Exact reverse traversal makes both
nonempty complete-cancellation endpoint junctions hold simultaneously, with
their four walk endpoints. The same chain places the cyclic source either at
the authenticated outer terminal or strictly before it. The generic target and
typed Wait theorem retain this classification without eliminating a junction,
par-pair residual, sibling exit, marked-global order, or descent.
`SequentialFigure7MarkedTargetRawReturnCompleteCancellationCausalEndpoints.lean`
eliminates only the equality case in that final classification. The complete
cancellation pairing makes retained-prefix edge indices duplicate-free, so its
internally nonbacktracking prefix is cyclically nonbacktracking as well. If the
cyclic source equaled the base, exact mask retention would embed a nonempty
closed cyclically nonbacktracking walk in the correct reference switching,
contradicting its tree contract. The combined theorem therefore keeps both
endpoint junctions and places the source strictly before the authenticated
base. Complete cancellation and every other residual remain open.
`SequentialFigure7MarkedTargetRawReturnSiblingExitForwardCausalOrder.lean`
then re-roots the sibling continuation after the first descent's shared marked
non-global conclusion. Submitted-parent uniqueness makes two finite marked-
conclusion chains from the same origin terminal-comparable. Against the chain
to the authenticated outer mate, any marked-global sibling endpoint must
therefore occur strictly later; the earlier order is impossible. The generic
target and typed Wait theorem retain raw-mate and future-conclusion exits,
complete cancellation, both endpoint junctions, the par residual, the descent,
and tail failure. No payer, history-tail law, completion, or progress follows.
`SequentialFigure7MarkedTargetRawReturnSiblingExitOpen.lean` then eliminates
the surviving marked-global sibling endpoint. The selected ready head is
queued and therefore raw-unmarked. If the compared sibling chain reaches a
marked global conclusion, either terminal uniqueness gives an immediate
non-global contradiction or the current connective conclusion becomes
concretely marked. Canonical raw-mark history would then mark both submitted
premises, contradicting the selected head's raw-unmarked lookup. The resulting
open-exit carrier has only raw-mate and future-work constructors. The target's
separate raw, future, and older marked-global branches, complete cancellation,
both endpoint junctions, the par residual, the descent, and tail failure remain;
no payer, history-tail law, completion, or progress theorem follows.
`SequentialFigure7MarkedTargetRawReturnSiblingExitTemporal.lean` next
normalizes the two open sibling constructors against the exact active
occurrence carrier when the non-global ready-tail search has failed. A raw mate
is outside the carrier or is exactly the selected head, in which case consumer
uniqueness identifies its chain terminal with the current mate and its
conclusion with the current connective conclusion. A future endpoint retains
an outside conclusion at a boundary strictly older than the active ready head.
All three constructors retain an outside chain terminal. The target's separate
raw, future, and older marked-global branches are unchanged, and the exact raw
return remains an open residual; no payer, tail law, completion, or progress
follows.

`SequentialFigure7FutureWorkExactLocation.lean` then unfolds the scheduler
semantics hidden by `FutureWorkAt`. Ready work retains its exact sigma slot,
ready bucket, live component frontier, and raw-unmarked conclusion. Waiting
work retains its exact cell, submitted par producer, oriented marked premises,
and strict younger-boundary comparison. In either location, a connective
conclusion stored as future work has both premises concretely marked.
`SequentialFigure7MarkedTargetRawReturnSiblingExitScheduled.lean` transports
that information into the older future sibling branch and the typed Wait
target. Raw-outside and exact selected/mate-return branches are unchanged.
This is a scheduler classification, not endpoint elimination, a ready-tail
witness, a history-tail law, completion, or progress.

`SequentialFigure7MarkedTargetRawReturnSiblingExitCausalOwnership.lean`
authenticates both endpoint-premise marks in the supplied canonical history and
orders their events. Exact component ownership makes the outside terminal's
representative strictly older than the active boundary. The mate is either
outside with a strictly older representative or active-owned at the active
representative. If that active mate belongs to waiting work, exact span
orientation forces the terminal to be the older premise and the mate to be the
younger premise whose boundary is active; the reverse orientation contradicts
strict span order. Ready work remains an explicit alternative. This is a
causal/ownership normalization, not elimination of the endpoint or construction
of a non-global payer.

`SequentialFigure7MarkedTargetRawReturnSiblingExitReadyMateElimination.lean`
removes the active-owned ready alternative. A ready conclusion's exact live
component occurrence owns both submitted premises at the endpoint's strictly
older boundary. If the mate were also active-owned, exact live-carrier
disjointness would identify one vertex with two different live boundaries.
Therefore the active-owned branch is precisely the already oriented waiting
return from the older terminal to the active mate. An older-outside mate keeps
its ready or waiting scheduler status. This is one scheduler-case elimination,
not elimination of the future endpoint or exact raw return, construction of a
payer, derivation of the history-tail law, completion, or progress.

`SequentialFigure7MarkedTargetRawReturnSiblingExitWaitingMateParentRecursion.lean`
then turns the surviving active-owned waiting return into an authenticated
parent escape. Its mate is a concretely marked, non-global active-frontier
premise distinct from the selected head, while its submitted conclusion lies
outside the active occurrence carrier. Under ready-tail failure, the existing
parent-escape normalization therefore supplies a recursive temporal outcome.
That refinement is lifted through the sibling target and typed Wait trace.
Older-outside mates retain their strictly older ready or waiting status. The
result does not eliminate waiting or the recursive temporal residual, produce
a payer, prove repeated normalization well-founded, derive the history-tail
law, or prove completion or progress.

`SequentialFigure7MarkedTargetWaitingMateExternalTemporal.lean` closes the raw
credit subcase inside that active-owned waiting return in its public contract.
The two-constructor `ActiveMateWaitingParentExternalTemporalOutcome` is fixed
to `consumer.conclusion` and contains only `olderFuture` and `olderMarked`; the
explicit `propext`-only `.activeCarrierOutcome` map forgets it into the broader
parent temporal carrier. The waiting span marks both the older terminal and
the active mate. Canonical continuation credit for the marked non-global mate cannot
return raw: connective-opposite identity
would make the already marked older terminal raw-unmarked. The narrowed result
therefore reaches the submitted conclusion outside the active carrier, either
as future work at a strictly older boundary or as a concrete mark at a
strictly older representative. The direct theorem and active scheduler status
return or store that narrowed carrier. The direct bridge needs only
`CanonicalTagHistory`, `SchedulerInvariant`, active component lookup and
occurrence, the outside-conclusion premise, and the waiting witness. It needs
neither `DeclarativelyCorrect`, `noTail`, nor an explicit `mateActive` premise.
The refinement is lifted through the scheduler status, sibling-exit target,
and typed Wait trace. It leaves older-outside mates ready or waiting and does
not discharge the broader exact selected/mate raw returns, external temporal
endpoints, history-tail law, progress, completion, or totality.

`SequentialFigure7MarkedTargetWaitingMateExternalCommitmentReentry.lean`
refines both constructors of the exact waiting-mate external temporal carrier.
At either strictly older future or marked endpoint, canonical history supplies
the exact `StrictOlderCommitmentSplit`; reference-switching connectedness
supplies an owned-to-external `ActiveCarrierExternalEndpointCrossing`; and
`.reentry` reverses its edge-simple path and boundary edge. Under exact
ready-tail failure, that re-entry yields
`ActiveCarrierExternalReentryFailureHistoricalStatus`. The resulting
two-constructor
`ActiveMateWaitingParentExternalCommitmentReentryFailureOutcome` remains fixed
to `consumer.conclusion` and retains the temporal, commitment, crossing,
re-entry, and failure evidence. The direct theorem constructs re-entry by
reversing its crossing, but the carrier fields assert existence separately and
do not equate arbitrary stored witnesses. Its remaining inbound target is the
selected raw-unmarked head or a distinct canonical-history-authenticated mark
represented at the active boundary. No avoiding re-entry, target elimination,
payer, history-tail law, completion, progress, termination, or totality follows.

`SequentialFigure7MarkedTargetWaitingMateExternalCommitmentReentryMarked.lean`
uses the outer stored-right par orientation to remove that selected-head target.
The generic
`ActiveCarrierExternalReentryFailureHistoricalStatus.markedHistoricalTarget_of_storedRight`
theorem applies structural inbound-parent-edge separation: beyond the supplied
failure status, it needs only structural well-formedness, the selected
connective's `par` kind, and its `.storedRight` side. No avoiding path premise
is required. The exact future/marked waiting endpoint retains its temporal,
strict commitment, crossing, and reverse re-entry fields and replaces only the
failure status with `ActiveCarrierExternalReentryMarkedHistoricalTarget`. That
refinement is transported through the active future-work mate status,
continuation exit, sibling target, and typed Wait older-mate trace. The
older-outside, raw-outside, selected-return, future/marked sibling exits, and
avoiding/equal trace branches remain unchanged; so do the causal-descent and
cyclic-junction receipts. The surviving target is still a distinct
canonical-history-authenticated mark at the active representative. No avoiding
witness or path alignment, payer, history-tail law, progress, completion,
termination, or totality is derived.

`SequentialFigure7MarkedTargetWaitingMateExternalCommitmentReentryTemporal.lean`
normalizes that surviving mark from the exact endpoint where its nested path
actually starts. For a waiting case this endpoint may be
`consumer.conclusion`, not the enclosing `current.mate`. The inbound target is
in the active frontier and therefore in the active owned carrier; the supplied
`current.mate ∉ owned` receipt separates the two vertices. Structural
parent uniqueness identifies the target's unique submitted consumer, aligns
the inbound edge source with that consumer's conclusion, and keeps its mate
different from the selected head. Under the retained exact ready-tail-failure
premise, continuation credit then has three exact forms: an unmarked raw parent
mate outside the carrier, future work for the parent conclusion at a boundary
strictly below the active age, or a marked parent conclusion whose
representative is strictly below the active age. The
existing strict commitment split, crossing, reverse re-entry, active scheduler,
continuation sibling, causal-descent, cyclic-junction, and typed Wait wrappers
transport this endpoint-parametric status without changing unrelated branches.
The marked target is not eliminated, and no payer, arbitrary witness alignment,
history-tail law, progress, completion, termination, or totality follows.

`SequentialFigure7MarkedTargetWaitingMateExternalCommitmentReentryContinuationExit.lean`
retains exact ready-tail failure, preserves `path.start = endpoint` for the
temporal target's arbitrary endpoint, and follows its finite
`MarkedConclusionChain`. A raw-unmarked terminal consumer mate is either
outside the active carrier or exactly the selected head, in which latter case
the chain terminal is `current.mate`, its submitted conclusion is
`current.conclusion`, and target-to-terminal formula complexity grows strictly.
The other exits place the terminal consumer's conclusion outside the carrier
as future work at a strictly older boundary or as a marked-global conclusion
at a strictly older representative. One proposition carrier and one
standard-three theorem expose this normalization. No exit is eliminated, and
the result recovers no payer, supplies no avoiding witness or aligned re-entry
path, and derives no history-tail law, progress, completion, termination, or
totality.

`SequentialFigure7MarkedTargetWaitingMateExternalCommitmentReentryContinuationWaiting.lean`
then combines carrier-forest marked ownership with live-carrier disjointness.
A nontrivial chain first marks the known-outside parent conclusion. Its owner
cannot be the active carrier, because that contradicts the outside premise. If
the owner is a distinct live carrier, connective ownership closure also places
the active-frontier origin there, contradicting its ownership by the active
carrier and disjointness. Thus every retained `MarkedConclusionChain` is
reflexive, and its terminal consumer is the target consumer. The exact
selected/current-mate return contradicts the retained mate separation, and a
marked-global conclusion contradicts the same ownership argument. Decomposing
strictly older `FutureWorkAt` into its exact scheduler location also rules out
the ready case: it would place the chain origin in both the older and active
live carriers. The waiting case retains the initialized payload, submitted par
lookup and source-index entry, oriented marked premises, and both `sigma`
boundary equations. The resulting target has exactly two forms: a
raw-unmarked target-consumer mate outside active ownership, or its conclusion
as strictly older future work at that exact initialized waiting location. The
module exposes one exact-location definition, one two-case target definition,
and one standard-three theorem. It does not eliminate the target, identify a
payer, align witnesses or paths, derive a history-tail law, or establish
progress, completion, termination, or totality.

`SequentialFigure7WaitingReentryContinuationProducerOrientation.lean` then
orients the exact producer inside the older waiting branch without importing
the surrounding carrier or history geometry. If the consumed target is marked
at an age represented by the active boundary while the exact waiting location
is strictly older, producer uniqueness and the waiting premise orientation
rule out the target as the older premise. The theorem returns every exact
location field together with `target = youngerPremise`,
`consumer.mate = olderPremise`, `targetAge = youngerAge`, and
`youngerBoundary = active`; the older and younger mark representatives are the
older and active boundaries respectively. Its inputs are only the scheduler
invariant, exact location, target mark, active-representative equation, and
strict boundary order. It requires no component lookup, carrier occurrence,
canonical history, `noTail`, or declarative correctness. That orientation
theorem alone leaves the raw survivor intact and supplies no path, payer,
history-tail law, progress, completion, termination, or totality.

`SequentialFigure7WaitingReentryContinuationMateAvoiding.lean` supplies the
next geometric bridge. From `DeclarativelyCorrect` and an exact waiting
location, `mateToTargetAvoidingPath` returns an exact path from the consumer
mate to the target while avoiding the inner waiting conclusion. With the
complete scheduler invariant and an explicit active-component lookup and
occurrence witness, `activeTargetMateAlignedAvoidingReentry` aligns the target
inside the active owned carrier and its older mate outside, and retains an
outside-to-inside directed occurrence on that same path.
`activeTargetMateAvoidingReentry` packages exactly those witnesses in the
existing avoiding-re-entry carrier. This derives the previously missing inner
waiting-branch avoidance/re-entry premise. It does not show that the path
avoids the outer selected parent conclusion, eliminate the raw or waiting
survivor, recover a payer, or close the history-tail or progress gates.

`SequentialFigure7CommitmentBlockerAdvance.lean` joins the global queued-head
law, the strict `sigma` split, the strict-edge avoiding adapter, and the final
equal-boundary classification. Under declarative correctness and the complete
scheduler invariant, for a supplied canonical history, active `NewGuard`, and
authentic ledger event whose current representative is strictly below the
active head, it returns an exact avoiding path, a mate-touching event at a
strictly higher representative still below the head, or the exact equal-
boundary stored-left callback-failure trace. The three branches are inclusive.
Representative advance is neither raw-age nor ledger chronology; the theorem
does not maximalize or eliminate that branch, and the equal callback failure
does not prove path nonexistence. It derives no mate-region invariant, closes no
created-candidate raw seam, and adds no enabledness, progress, reachability,
totality, completeness, or complexity theorem.

`SequentialFigure7CommitmentBlockerMaximality.lean` removes the intermediate
current-representative advance under the same explicit correctness, complete
scheduler-invariant, canonical-history, active-guard, membership, and strict-
order inputs. It takes the maximum current representative among the finite
authentic mate-touch blockers above the original event. At that blocker, an
avoiding commitment path would splice with the historical and current
component routes to form the tensor bypass forbidden by reference-switching
acyclicity, while another advance contradicts maximality. The inclusive result
is therefore an exact avoiding path or the exact equal-boundary stored-left
callback failure. That callback witness does not deny path existence. Queue
origin, the independent mate-region and global raw-mark invariants, created-
candidate raw seams, enabledness, progress, totality, completeness, and
complexity remain outside the theorem.

`SequentialFigure7ActiveRegionTouchSeparation.lean` consumes that inclusive
result through a reusable local path carrier rather than adding a global
history field. `ActiveMateEventAnchor guard event` stores an exact reference
path from the active tensor mate to the event's stored-left axiom endpoint while
omitting the active conclusion. The commitment-path branch extends that anchor
through the representative event and final commitment edge, producing the
forbidden tensor bypass. The stored-left callback branch instead follows the
retained prefix, final New edge, and exact callback trace to produce an
alternate mate-to-conclusion walk that omits the active tensor edge. Exact
stored-edge identity in the reference tree excludes both walks. Because any
touch inside the complete active mate source-left region constructs this anchor,
every authentic ledger event is locally touch-separated from that region. The
module does not claim callback impossibility without an anchor, create a global
separation invariant, construct reachability, or execute a scheduler rule.

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

The root executable `ProofNetIRNewProgressAudit.lean` is a bounded,
fail-closed replay layer over that boundary. It never inserts arbitrary states:
each path begins with `initializeReservation?` and recursively applies the
canonical `dispatch?`, carrying `ReachableByImplementedDispatcher` and deriving
`SchedulerInvariant` from the actual history. At every post-initialization
state it classifies concrete marking completeness, reconstructs exact typed
`ReadyHeadInput` availability, and calls the real dispatcher. An incomplete
state without a head or with `dispatch? = none` is a hard failure retaining the
accepted certificate, full state, event ledger, and replayed rule trace. The
same traversal retains the earlier guarded-New and marked-tensor-predecessor
subaudits. The default CI corpus is finite at seed 0, depths 0 through 4, every
formula start, and six labelled order variants; `--extended` adds depth 5, and
`--cross-representative-search` widens the labelled variants. Candidate
acceptance uses `unificationCheck` and the kernel equality
`unificationCheck_eq_check`; a direct all-switchings sentinel remains at depths
0 through 2. This architecture supplies regression evidence and diagnostics,
not semantic completion, dispatcher progress, or totality.

The same replay now independently classifies every selected marked-tensor ready
head against the active sigma top. The default depth-0-through-4 run observed
6,198 such states, and the extended depth-0-through-5 run observed 26,658; every
mate resolved to the immediate predecessor, so both runs recorded zero missing-
predecessor gaps. The detector retains a complete replayable counterexample and
partitions any failure into a missing previous top or a boundary mismatch. These
finite observations remain independent falsification evidence, not the source
of the kernel theorem. The full-history invariant now eliminates the residual
at an explicitly supplied correct canonical-history ready head, and the
active-top classifier identifies the exact structural shape when that head is
absent. The marked-nonconclusion debt theorem now turns that shape into
`core.allMarked = true` when its additional state predicate holds. The
full-history continuation-credit invariant also has a finite three-way
normalization. A separate endpoint-bound open-exit law conditionally implies
active-top debt and hence closes a drained branch when supplied. Successful
Wait, however, refutes that unrestricted same-component law at its output; the
replay and canonical-history theorems therefore cannot preserve it unchanged.
They derive neither direct debt nor a Wait-compatible drained, temporal, or
cross-component weakening, and the obstruction proves no post-Wait drained or
reachable-Wait existence fact. Unconditional progress, completion, terminality,
and totality therefore remain open.

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
  `SequentialFigure7RawMarkHistory.lean` reuses the same typed branch evidence
  to expose each branch's common prepared prefix. Its one-step theorem says
  that an output raw mark is old or is exactly the current selected
  occurrence/raw-age pair; induction then characterizes every final raw mark
  by an authentic dispatcher event. This relation is separate from search
  touch provenance because stable rules raw-mark connective conclusions. It
  does not by itself provide queue-origin or vertex-level commitment paths and
  therefore does not discharge any created-candidate raw seam. The separate
  commitment-spine layer now records exact retained `sigma` ancestry, and the
  raw-mark reservation-anchor layer supplies the same-component path from a
  mark to its event endpoints. The adjacent-edge layer now composes one exact
  retained parent-child edge, and the target-avoidance layer conditionally
  omits a future tensor conclusion under the explicit child-event untouched
  law. Explicit adjacent callbacks compose across every supplied nonempty
  retained-`sigma` interval. When both separation invariants and the complete
  scheduler invariant are supplied, the child-event law and callback now
  follow automatically for any strictly older adjacent edge or positive
  interval ending at a strictly older boundary. New preservation of the
  queued-head invariant is kernel checked as one branch of the global result.
  Wait, Forward, and UnifyPayload now derive their created-head residuals
  structurally, and a complete canonical-history induction now establishes the
  queued-head invariant globally over every supplied structurally well-formed
  history.
  An event whose current representative is strictly below the candidate now
  splits at the candidate's immediate predecessor, so every positive prefix is
  composable. Under the additional public theorem inputs, finite maximality
  reduces the complete interval to an avoiding path or the exact equal callback
  failure. Global availability of the independent mate-region and raw-mark
  invariants, the remaining stored-left callback failure, and queue-to-created-
  candidate geometry remain required by the seams.
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
