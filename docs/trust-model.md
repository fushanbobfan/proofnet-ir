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
linearity claim is made. The current event-driven worklist must first be proved
complete and the recursive fallback removed; a later Guerrini-style claim also
requires the complete Figures 7--8 `NEXTAXIOM`, token-age,
ready/waiting-stack, and special union-find invariants together with a
whole-program cost theorem.

The separate `SequentialUnification.lean` checkpoint narrows, but does not
close, that requirement. Lean proves exact submitted-link origin for every
entry in its reusable source-incidence index. `SourceIndex.Sound` is only a
provenance property: it does not establish lookup existence or uniqueness, and
both endpoints of a malformed self-axiom are intentionally inserted into one
bucket. Structural well-formedness now proves singleton lookup for every
in-bounds occurrence. Given an exact submitted par lookup, the stronger
positional theorem identifies that singleton with the same submitted link
index and link value; repeated labels or equal-valued links in another slot
cannot replace it. A successful bounded/tagged `NEXTAXIOM` result carries
the exact submitted axiom index/endpoints, final tags, and trace; its proof
fields establish tag-array size preservation, monotonicity of old true tags,
trace `Nodup`, input-false/output-true tagging of every trace occurrence and
both endpoints, input-unmarked endpoints, and `trace.length ≤ fuel`. Its
`Touched` carrier is the trace plus endpoints, and successive successful calls
have disjoint touched carriers when the second uses exactly `first.tags`. This
is the scope of the global no-revisit discipline; no result is claimed after
tags are reset or replaced. A separate oriented-route theorem proves that the
trace is an exact submitted source-left chain to the axiom endpoint actually
reached and relates that endpoint to either stored axiom orientation.
`SearchClearThrough` supports a local totality theorem: structural
well-formedness, state abstraction, freshness through the starting complexity
rank, and fuel greater than that rank imply success on the production index.
Full initial-carrier freshness yields the exact `rank + 1` budget. This does
not prove the carrier-size wrapper total or establish freshness in a later
Figure-7 scheduler state. Because success tags complexity-zero axiom
endpoints, the global low-rank predicate cannot itself be threaded to a second
call; later scheduling requires a route-local freshness invariant.

Its dynamic update immediately allocates and assigns a token and refines one
eager Figure-5 start step under `Abstractable` and `OrderedParents`; it is not
the delayed Figures 7–8 `init`/`new` transition. Missing,
ambiguous, tagged, marked, or malformed sources fail closed, with dedicated
regressions for zero fuel, out-of-bounds, tagged and marked starts, missing and
duplicate sources, stored-right orientation, initial rank-budget coverage, and
repeat rejection after threading the first result's tags. The executable and
its proof fields are trusted only after compilation like any other Lean
declaration; the regression observations remain untrusted evidence.

`SequentialSchedulerState.lean` adds a separate compiled delayed-state
checkpoint. Its `RawTokenAge` is not a representative. Kernel-checked
`SigmaAgePartition` fields enforce an empty-zero/positive-zero-head, strictly
increasing boundary list below the raw-age horizon. Waiting cells retain three
distinct observations: out of bounds, in-bounds undefined, and initialized
empty. Strict empty `init` leaves `W(0)` undefined. The literal
`newEnqueue?` source-audit helper writes the fresh waiting cell exactly as the
printed Figure-7 display does, preserves only the weak shape invariant, and is
not used by the production bridge. `operationalNewEnqueue?` instead
initializes the old active `σ` boundary and leaves the freshly pushed active
top undefined. The compiled `OperationalWaitingDomain` states that, among
allocated ages, initialized waiting cells are exactly `sigma.dropLast`; both
`init` and the operational later reservation preserve it.

This old-boundary update is the project's interpretation of the paper's prose
that defines `W` on nonactive boundaries and of the later `wait`/`unify`
behavior. It is not an author-confirmed erratum or a theorem that this is the
unique reconstruction of the display. `SequentialSchedulerBridge.lean` now defines
`ReservationState`, `initializeReservation?`, and `reserveNewAxiom?` to keep
the delayed stack, production core, and complete search tags synchronized
through initial and later reservation-only calls. The typed
`InitialReservationStep` / `NewReservationStep` records and their executable
`some_iff` theorems expose every successful subcall rather than trusting an
opaque wrapper result.

`ReservationInvariant` is the compiled preservation bundle for
wrapper-generated histories: delayed `WellShaped` and
`OperationalWaitingDomain`; `RealizesSigma`; production `OrderedParents`,
`Abstractable`, and `ComponentsFormulaConsistent`; component/parent carrier
alignment; started-axiom/counter alignment; and tag-domain alignment. It is
proved for the empty state, established by a successful initialization, and
preserved by every successful operational later reservation. The record is
not itself a reachability or tag-history characterization: `tags_size` proves
only carrier size, so reset tags may still satisfy it. Its waiting-domain field
specifies which cells are initialized, not semantic ownership or correctness
of their payloads and not `wait`/`unify` transfer behavior. Later
`RealizesSigma` preservation uses
the sigma-append old/fresh lemmas together with the corresponding production
old/fresh representative lemmas. A deliberately arbitrary ordered parent
forest `#[0, 1, 0]` with `sigma = [0, 1]` sends age `2` to boundary `1` but
representative `0`. It is not proved reachable through actual `unify`/union;
it only refutes automatic derivation of `RealizesSigma` from `WellShaped`,
marks/horizon alignment, and `OrderedParents`.

Complete tag threading proves that each adjacent composable wrapper-step pair
reserves distinct submitted axiom-link indices. It does not equate duplicate
axiom values at different indices without an extra structural premise. The
scope is exact: reset/replaced tags can replay low-level search, while the
operational stack guard independently rejects endpoints already stored in
ready or waiting payloads; direct low-level reservations remain replayable.
The canonical
two-call regression locks submitted/ready orientations
`[0,1]`/`[1,0]`, then `[2,3]`/`[3,2]`. The next trusted layer implements the
project's operational local Figure-7 `new` transition under a supplied
`ReservationInvariant`: synchronized pop/raw-mark, fixed canonical
sound-and-complete consumer lookup, orientation-aware tensor mate, post-mark
`NEXTAXIOM`, and an operational later reservation that initializes the old
active waiting boundary while leaving the fresh top undefined. Its proof
argument blocks independently forged stack/core horizons and raw ages, and
callers cannot inject a partial consumer table. A separate proof-relevant
`InitNewHistory` now characterizes exact empty/init/new executions and proves
tag iff recorded touch, global submitted-slot non-reuse, and
reservation-count alignment. It is still not a full reachable Figure-7
scheduler. Exact local `concl`/`nop`/`wait` and successful `forward` now require
a proof-carrying canonical consumer/conclusion view and preserve the
reservation invariant.
The common prepared pop/raw-mark prefix is also proved to preserve every
current state-only field of `SchedulerInvariant`; exact and executable
`concl`/`nop` inherit that theorem because they return `prepared.after`.
The independent proof-only `SequentialComponentProvenance` layer now recovers
exact internal component/link occurrence identity: it records submitted link
positions, exact first-occurrence focuses, complete owned vertices, local
`Nodup`, and cross-live-slot disjointness. Its bidirectional accounting binds
marked owned vertices to the exact representative slot, leaves unmarked owned
vertices on that component frontier, and assigns every concrete raw mark to
an owner at its representative. It soundly refines the older
formula-consistency predicate and rejects a concrete same-label alias. The
layer also has closed rejection fixtures for cross-representative ownership
and forest-external raw marks. These propositions are not runtime trusted
state. The whole-forest predicate is now a `SchedulerInvariant` field:
empty/init establish it, and the prepared raw-mark prefix preserves it from
the representative-indexed live owner, so `concl`/`nop` inherit it. Successful
deterministic `NewStep` and executable `new?` results now preserve the complete
current occurrence-exact state-only invariant as well. The proof establishes
fresh submitted-axiom occurrence ownership against the old forest and
transports every current queue, causal, waiting, pending, and counter field.
The theorem assumes an existing invariant and a successful step/equation; it
does not establish later-state `new?` success, totality, or dispatcher
reachability. `wait` requires the separate theorem below.
Successful deterministic/executable `wait` now preserves that same complete
state-only invariant. It uses the mate's raw mark and exact `sigmaBoundary?`
destination, identifies the submitted par by its source-index position, proves
the new conclusion fresh and raw-unmarked in the combined queue, and extends
`WaitingSpanExact` while leaving the occurrence forest and logical counter
unchanged. It still performs only one initialized-cell cons and no global queue
scan; the global facts are proofs from the input invariant, not runtime scans.
This is conditional successful-step preservation, not applicability or
reachability. Successful typed `ForwardStep` and executable `forward?` now
compose the exact submitted par occurrence with the paper's non-strict raw-age
guard `selectedRawAge ≤ mateRawAge`; a separate theorem regression covers the
distinct-age boundary case `sigmaBoundary? [0] 1 = some 0`. They queue that
exact par, prepend its
conclusion to the active ready bucket, and preserve the complete
occurrence-exact `SchedulerInvariant`: component forest, live frontier,
ready/waiting queue, waiting spans, pending coverage, and fired counter. The
extra active-ready `Nodup` guard is only fail-closed shape validation, not a
paper premise. A typed `init → nop → forward → concl` regression locks the
successful composition. This still does not prove applicability, totality,
or unconditional reachability. The later canonical dispatcher/history layer
records successful branches but supplies no enabledness theorem. Bounded
`UnifyEmpty` now has
direct/executable correspondence for `W(j) = []` under its documented
premises. Its successful typed/executable steps preserve the complete current
occurrence-exact `SchedulerInvariant`, including `RealizesSigma`, the
survivor/retired component-forest update, queue/waiting/pending facts, and the
fired counter after the active-level pop and parent union. Strict-singleton
`UnifyOne` now additionally accepts exactly `W(j) = [c]`, resolves `c` to its
unique exact submitted par producer slot, and performs one atomic prepare →
tensor union → par activation → scheduler drain. Its independent
Boolean-free direct relations, typed/executable correspondence, unique output,
exact `+2` counter equation, and preservation of both `ReservationInvariant`
and the full occurrence-exact `SchedulerInvariant` are kernel checked. Empty
and length-at-least-two payloads fail closed in that specialized executor. A
separate local production-core fold activates any finite stored payload head
to tail with independent direct/typed/executable correspondence, output
uniqueness, and exact `+ payload.length` accounting.
`SequentialFigure7UnifyPayload.lean` now composes one tensor, that fold, and the
two-level drain atomically. Its high-level-executable-independent direct
`UnifyPayloadRule`, typed witness, and executable have exact correspondence
under the stated structural,
`ReservationInvariant`, and final-ready `Nodup` premises; success preserves
`ReservationInvariant` and satisfies exact `1 + payload.length` accounting.
`SequentialFigure7UnifyPayloadInvariant.lean` additionally proves complete
occurrence-forest/`SchedulerInvariant` preservation from a supplied full input
invariant. The proof keeps a fixed final scheduler stack and a transient
unactivated-suffix gap: the input forest proves each gap occurrence fresh and
non-produced, exact producer/boundary facts identify its activation, and each
activation establishes its new exact owner before the empty gap closes. No
history/reachability assumption is trusted, and no ordinary invariant is
assigned to physical intermediate tensor/fold states. The six new public
theorem boundaries audited here are `SchedulerInvariant.withoutReady`,
`UnifyPayloadGapInvariant.close`, `UnifyPayloadGapInvariant.activateHead`,
`UnifyPayloadGapInvariant.WaitingParActivationFoldStep.closeGap`,
`UnifyPayloadStep.schedulerInvariant`, and
`unifyPayload?_schedulerInvariant`; each has only the existing
`propext`/`Classical.choice`/`Quot.sound` dependency boundary. This does not
by itself derive applicability. The separate audited boundaries
`unifyPayload?_exists_of_enabled` and
`unifyPayload?_exists_schedulerInvariant_of_enabled` prove conditional
applicability from pure input-only `UnifyPayloadEnabled` plus the full
invariant. They do not claim the invariant alone implies enabledness or select
the correct dispatcher branch. The separate
`SequentialFigure7StableEnabled.lean` boundary applies the same discipline to
`concl`, `nop`, `wait`, and `forward`. Its audited public inputs contain only
the ready-head equations, exact submitted-par slot/orientation where relevant,
and the paper-side age/mark guards; they contain no result, executor equation,
wait destination/payload, component pick, or representation `Nodup` witness.
The full invariant derives those hidden facts. Each `*_exists_of_enabled`
theorem proves execution, and each companion theorem proves the complete output
invariant. `submittedParInput_enabled_cases` is only a trichotomy for an already
supplied ready head and exact submitted par; it is not priority-aware or
globally exhaustive. The additional audited boundaries
`ConnectiveBelow.mate_bound`,
`structural_conclusion_or_submittedConsumer_of_structural`,
`readyHead_structural_cases`, and
`readyHead_enabled_or_tensor_mark_cases` provide exhaustive occurrence-level
coverage for a supplied ready head. Their evidence is read-only: no executor
result, success equation, post-state, history, or reachability witness is
stored. The nested alternatives are not trusted as pairwise disjoint, and the
bare unmarked tensor case does not establish `NewEnabled`; the source-region
bridge additionally checks exact route reconstruction, endpoint queue
separation, and fresh-cell capacity. A marked tensor yields
`UnifyPayloadEnabled` only with the separately checked input-only sigma
predecessor/boundary witness; the bare marked alternative does not supply it.
A checker-rejected one-axiom/one-tensor fixture proves this remains true even
with the complete state-only `SchedulerInvariant`: after exact initialization
and the common prepare prefix, singleton sigma, a ready tensor premise, and a
marked mate coexist with failed `UnifyPayloadEnabled`. This fixture is not
evidence about correct certificates or canonical dispatcher reachability.
Correct-state progress,
pure-worklist completeness, fallback removal, faithful
`NEXTAXIOM`/token-age sequencing, and whole-program linearity remain
unimplemented. Independent Boolean-free direct relations now exist for the
common prefix, `concl`, `nop`, `wait`, and `forward`. `ForwardRule` excludes
Figure-7 executables and mutation wrappers and retains the exact non-strict
raw-age guard. Its separate `ForwardExecutableReadyNodup` premise is a
fail-closed list representation condition, not a paper guard. Executable
soundness and structurally valid completeness/iff/output uniqueness are
kernel checked; the complete `SchedulerInvariant` derives the shape premise
and supplies its own completeness/iff. These theorems do not imply
applicability, reachability, or progress.
`SequentialFigure7Dispatcher.lean` adds no new logical oracle. It evaluates
the six existing executors in a documented order and returns a tagged state
only when one already succeeds. Its exact dependent witness includes every
earlier branch's failure equation; invariant preservation factors through the
existing typed-step theorems. The associated history is explicitly
proof-carrying: constructing a later edge requires the full input invariant.
Accordingly, `ReachableByImplementedDispatcher` means certified executable
trace reachability, not that the invariant creates an enabled branch. The
empty full-invariant regression returning `none` prevents that interpretation.
The compatibility `unifyEmpty?` and `unifyOne?` functions remain outside the
canonical branch type and contribute no duplicate trust path.
`SequentialFigure7PriorityEnabled.lean` adds no new oracle either. For all six
branches it reconstructs the already audited input-only witnesses from exact
typed-step fields and uses the existing invariant-backed applicability
theorems in the reverse direction. Its `new` field stores `NewEnabled`; the
historical `NewExecutableEnabled` remains definitionally operational
existential `new?` success only as an exact compatibility API, not a hidden
paper-level assumption. `PriorityEnabled` adds only earlier-branch input
negations and is exactly interconvertible with the existing `DispatchStep`. Its
selected-kind iff, `none` iff no kind, and kind-uniqueness theorems therefore
classify current executable behavior without asserting that an intended state
must be executable. The real completed `[[]]` regression remains an explicit
full-invariant no-branch case.
`SequentialFigure7NewInputCore.lean` likewise adds no oracle or applicability
axiom; `SequentialFigure7NewInputNecessary.lean` is its historical compatibility
facade. The core erases executor equations, results, and post-states from
a successful `NewStep`, retaining only a shallow ready/tensor/mate guard and a
bounded exact source-left route with input tag freshness, whole-trace
production readiness, and ready axiom endpoints. The checked direction is
success to `NewInputNecessary`. At this lower layer no unconditional reverse
direction exists because the record itself omits recursive per-step tag-update
equations and the later operational enqueue guard. The structural source-region layer now reconstructs the exact
run and derives terminal-partner exclusion, but does not manufacture the
enqueue region. Forged
all-true and
terminal-partner-pretagged inputs demonstrate that `NewGuard` alone is not an
oracle for success. `PriorityEnabled` therefore stores the stronger input-only
`NewEnabled`, never the shallow necessary projection.
`SequentialFreshSourceLeftRun.lean` and
`SequentialFigure7NewEnabledCore.lean` adds no oracle or unchecked existence
principle. The proof-relevant run is constructed directly from a named
`nextAxiomWithFuel?` equation and replays directly to that equation; its four
constructors retain exact source-bucket and link-slot equalities, evolving tag
facts, fixed raw-mark readiness, and terminal orientation. The reservation
bridge explicitly requires structural well-formedness and carrier alignment.
`NewEnabled` adds the shallow guard and exact operational enqueue predicate but
stores no executor equation/result, output, history, or reachability witness.
Under `SchedulerInvariant`, Lean proves it equivalent to existential `new?`
success and derives an invariant-preserving result. Negative fixtures cover a
raw-marked intermediate occurrence, a pretagged terminal partner, and a queued
terminal partner; the last keeps a valid guard and run but invalidates enqueue.
The older `NewInputNecessary` remains strictly weaker. A dedicated lower-layer
split permits the priority field to store `NewEnabled`; the compatibility iff
and constructor do not change the dispatcher definition or order. The
historical `SequentialFigure7NewEnabled.lean` file is only an import facade;
the two direct-import sentinels change neither the trusted declarations nor
their axioms.
`SequentialFigure7NewRegion.lean` uses no new oracle: structural source-bucket
singletonhood reconstructs the exact formula-bounded run from the declarative
route, and `NewSourceRegionInput` explicitly carries the two endpoint
queue-absence facts and strict fresh capacity that are not derivable from the
current state invariant. With `SchedulerInvariant` and
`FutureWaitingUndefined`, it derives the existing audited enqueue guard and
`NewEnabled`. It assumes neither executor success nor reachability,
correctness, progress, or totality.
`SequentialFigure7FreshCapacity.lean` adds no unchecked counting premise. It
derives the strict capacity field from one exact current-tag run, structural
link/formula capacity, exact canonical reservation counting, and submitted-slot
`Nodup`. `SequentialFigure7QueueHistory.lean` likewise reasons only over exact
typed dispatcher evidence. It classifies queued endpoints of one exact axiom,
not arbitrary queued occurrences: stable rules can enqueue an untagged
connective conclusion. Canonical tag provenance turns endpoint queue membership
into a true current tag, contradicting the run's false-tag freshness. Hence
canonical history plus the complete invariant proves the history-indexed
`NewEnabled ↔ NewInputNecessary`, and certified reachability packages the same
result. The exact route remains part of `NewInputNecessary`; no oracle supplies
it from `NewGuard`.
`SequentialFreshSourceBlocker.lean` adds no oracle or history assumption. Its
structural dichotomy starts only from `StructurallyWellFormed` and an in-bounds
source occurrence. The positive branch is a formula-budget
`FreshSourceLeftRun`; the negative branch is an inhabited
`FreshSourceBlocker` whose occurrence lies on the stored-left visited region or
is the terminal axiom partner. The blocker records only a tag lookup different
from `some false` or a raw-mark lookup different from `some none`. Source-link
shape, source-index singletonhood, and fuel exhaustion are kernel-discharged
structural obligations, not trusted failure constructors. The dichotomy does
not use declarative correctness, scheduler history, or reachability, does not
exclude either dynamic blocker, and does not manufacture the downstream queue
absence or capacity evidence required by `NewEnabled`. Consequently it adds no
progress, totality, pure-worklist completeness, fallback-removal, or complexity
claim.
`SequentialFigure7BlockerHistory.lean` also adds no oracle. It consumes an
existing proof-carrying `CanonicalTagHistory`, the complete
`SchedulerInvariant`, and a shallow `NewGuard`. Exact tag provenance maps a tag
failure to a recorded prior touch. The raw-mark classifier uses only the
definitional selected-head update and the invariant's occurrence-exact
component forest: a raw failure is the selected head itself or an old marked
occurrence with a proof-relevant live owner. Its
`CanonicalSourceLeftObstruction` is a possibly-overlapping disjunction of those
three forms, not a trusted exclusive case split. The module assumes neither an
exact run nor executor success, `NewEnabled`, declarative correctness, or
reachability when it performs the classification.
The selected-head visited-case refinement also adds no oracle. Its source-left
rank and last-step lemmas are structural consequences of link typing, and the
head-separation proof compares the exact last consumer with the selected
tensor's unique consumer. It removes the selected-head alternative only for a
recursive `visited` witness.
`SequentialFigure7TerminalPartnerGeometry.lean` supplies the deliberately
separate proof for the terminal axiom partner. Its private helpers are ordinary
kernel-checked constructions of exact directed occurrences, simple paths, and
an `EdgeSimpleCycle`; its public theorem takes
`referenceSwitchingGraph.Acyclic` explicitly. The declarative-correctness
wrapper obtains that fact from `DeclarativelyCorrect.referenceSwitchingTree`,
not from scheduler history or an executable test. The structurally valid but
switching-cyclic triangle therefore remains a meaningful negative boundary.
Under this explicit acyclicity assumption, the complete-region blocker
classifier contains only prior canonical touch or old exact live-component
ownership; neither of those is trusted away. They are not assumed mutually
exclusive: a private native-computed canonical fixture records their overlap
as executable regression evidence, not as a public three-axiom theorem.
`SequentialFigure7TouchOrigin.lean` adds no oracle to the prior-touch branch.
It inducts only over the already proof-carrying `CanonicalTagHistory` and its
stored initialization/dispatcher evidence. The recovered route and submitted
slot are fields of those exact typed steps, while source-region membership is
derived structurally from the stored route. No executable replay, unchecked
choice of event, current-owner inference, or raw-age assumption is introduced.
`SequentialFigure7ReservationLedger.lean` adds no event oracle. Its only event
constructors store an exact `InitialReservationStep` or `NewStep`; its
oldest-first chronology is an inductive fold over `CanonicalTagHistory`, and
its raw-age, length, lookup, and submitted-slot equations are derived from the
stored step equations. The `new` event uses the fresh pre-step `nextAge`, not
the popped active age, and a separate theorem proves the latter strictly
smaller. The touch bridge retains an event-membership and event-local `Touched`
witness. It does not infer that raw age is a representative, that every vertex
touched by the event belongs to the reserved axiom component, or that
historical provenance classes are disjoint.
`SequentialFigure7CommitmentSpine.lean` adds no commitment or scheduling
oracle. Its public theorem is an induction over the existing
`CanonicalTagHistory`; stable branches preserve `sigma` and the reservation
ledger, `new` appends its exact fresh child and authentic reservation event,
and `unifyPayload` removes only the final active boundary. It therefore proves
allocation ancestry for adjacent pairs in the final retained `sigma`, with
the child raw age indexing the exact ledger event. It does not retain popped
boundaries, construct a vertex-level reference path, prove target avoidance or
queue origin, discharge any raw created-candidate seam, or establish
enabledness, progress, completeness, fallback removal, or complexity.
`SequentialFigure7TouchCompleteness.lean` adds no search oracle. Its run-level
theorem follows the supplied `FreshSourceLeftRun` by structural induction,
using source-producer and submitted-axiom uniqueness from
`StructurallyWellFormed`. Its event-level theorem reconstructs exactly the run
whose successful equation is already stored by the authentic initialization
or `new` event. The resulting touch/region equivalence needs no declarative
correctness, scheduler invariant, additional current executor success, or
executable audit. It does not manufacture an execution for a bare
`ReservationSearchEvent` or infer
current ownership, representative order, created-region separation, or
progress.
`SequentialFigure7CrossRepresentativeInvariant.lean` adds no scheduling or
region-separation oracle. `FutureWorkAt` stores exact ready/sigma lookups or an
exact initialized waiting lookup; its live-boundary and representative-root
theorems are derived from `SchedulerInvariant`, `WaitingSpanExact`,
`SigmaAgePartition`, and `RealizesSigma`. `FutureNewCandidateAt` stores an
exact `TensorBelow.Valid` witness and a concrete raw-unmarked lookup. The
history-indexed `OlderSourceRegionSeparated` is an explicit proposition to be
preserved, not an assumed field of `SchedulerInvariant`: its only order premise
uses the current ordered union-find representative. The exact empty proof is
vacuous and the initialization proof reduces strict order to `r < r`; no
search result, runtime test, raw-age chronology, or unproved disjointness is
inserted. At that foundation checkpoint, no later-rule preservation was
proved; the stable module below now covers the prepared, `concl`, and `nop`
cases, while the candidate-creating branches remain theorem work.
`SequentialFigure7OlderEventTouchSeparation.lean` adds no geometric oracle.
The forward conversion merely maps an event touch through the existing
touch-to-region theorem before applying region disjointness. The reverse
conversion uses the structurally proved authentic-event touch completeness.
Its history wrapper copies the ledger, future-candidate, and strict current-
representative quantifiers without adding a reachable-state or executor
witness. Therefore the iff normalizes `OlderSourceRegionSeparated`; it does
not prove that separation or any created-candidate premise.
`SequentialFigure7SameRepresentativeEventTouch.lean` imports no historical
touch or region oracle. The reservation event is an exact member of the
proof-carrying ledger, its touched witness comes from the event's stored search
result, and its final axiom endpoint ownership is derived from reservation
realization under structural correctness. The contradiction uses the
reference-switching acyclicity field of `DeclarativelyCorrect`; it does not use
an executable audit, a reconstructed `FreshSourceLeftRun`, or the desired
created-region invariant. Its conclusion is limited to representative
equality and cannot be reused as a strictly-older or old-owner theorem.
`SequentialFigure7ActiveRegionTouchOrder.lean` adds no geometric or execution
oracle. Ledger chronology, sigma realization, and the active-root facts first
give a non-strict representative bound; the preceding correctness theorem
excludes equality only when an authentic event touch meets the active region.
The resulting strict order is then consumed by the explicitly supplied
`OlderEventTouchSeparated`. Tag freshness follows by mapping a failed tag
lookup through canonical touch provenance to a concrete ledger event. No
runtime audit, route/run existence, raw readiness, queue/capacity witness,
created-region premise, or progress result enters these theorems.
`SequentialFigure7ActiveConclusionTouch.lean` adds no touch or path oracle.
Structural touch completeness extends an authentic event's source-left route
through the supplied future tensor's stored-left premise and then uses the
stored orientation to classify the reached premise as mate or head. In the
active theorem, existing tag provenance and conditional mate-region freshness
refute only the mate branch. The surviving head touch remains explicit, so no
conclusion-untouched fact, raw-mark exclusion, target-avoiding path, created
seam, enabledness, or progress theorem is hidden in this layer.
`SequentialFigure7ActiveRegionAvailability.lean` adds no search or ownership
oracle. It case-splits the already kernel-checked structural
`freshSourceLeftRun_or_blocker`. The run branch is packaged by existing
canonical queue/capacity theorems; declarative blocker classification reduces
the other branch to a canonical touch or an exact marked owner, and the prior
tag-freshness theorem refutes only the touch. `NewEnabled` then uses the
already-proved history-level `FutureWaitingUndefined`. The old-owner branch and
its pointwise exclusion remain explicit hypotheses, so no progress or global
availability fact is hidden in this layer.
`SequentialFigure7CrossRepresentativeStablePreservation.lean` adds no
reachability, ordering, or region-disjointness oracle. Its prepared-prefix
helpers are derived from the exact `popReadyMark?` and `markReadyRaw?`
equations. The only candidate-specific argument excludes equality between the
post-state unmarked tensor mate and the uniquely newly marked ready head; the
input lookup then follows from the concrete array update equation. The generic
history transport requires full ledger equality, while the canonical `concl`
and `nop` corollaries derive that equality from their empty reservation-event
lists. No claim is made for any branch that creates or moves future work.
`SequentialFigure7OlderEventFutureWorkTouchSeparation.lean` adds no touch,
queue-origin, or reachability oracle. Its proposition states the queued-head
non-touch law explicitly. The strict conclusion theorem combines that supplied
law with the independently supplied mate-region law and the prior structural
mate-or-head decomposition. Empty and structurally well-formed init eliminate
the strict order directly; Prepared/concl/nop transport exact ledger
membership, future work, and current
representatives. Candidate-creating rules, same-boundary touches, and global
availability remain explicit rather than hidden in this base proof. The
successful New case is handled by a separate downstream theorem; Wait,
Forward, and UnifyPayload are handled conditionally by downstream theorems
under their exact created-head residuals.
`SequentialFigure7StrictCommitmentTargetAvoidance.lean` adds no ownership,
touch, path, or reachability oracle. It instantiates the already audited
one-edge target-avoidance theorem with the already audited strict conclusion
law. Its private boundary-root lemma follows from exact sigma membership,
`RealizesSigma`, and the strict partition invariant; the interval corollary
uses only list-index ordering and the existing verified path compositor. Both
public theorems keep the scheduler invariant and both separation predicates as
explicit inputs. Equal-boundary edges, global availability, queue origin, raw
seams, progress, and complexity remain outside the claim.
`SequentialFigure7StrictOlderSigmaSplit.lean` adds no path, touch, ownership,
queue, or reachability oracle. It recovers the authentic event's raw-age bound
from the chronological ledger, locates its current representative through
`RealizesSigma`, locates the candidate root through the existing future-work
witness, and uses strict `sigma` ordering to return the candidate's immediate
predecessor. The possibly empty prefix can feed the previously audited positive
interval theorem, but this module does not discharge the final edge or derive
either separation invariant, queue origin, a raw seam, progress, or complexity.
`SequentialFigure7OlderRawMarkedRegionSeparation.lean` introduces no history,
executor, or reachability oracle. Its primitive is a proposition over concrete
raw marks, current representatives, and one structural source-left region.
Empty/initial proofs eliminate marks directly; Prepared preservation uses the
exact mark update, unchanged parents, exact future-work transport, and the
sigma-top greatest-boundary laws. Active-region exclusion separately combines
the invariant with the already proved same-representative correctness geometry
and occurrence-exact component provenance. The resulting owner-clear theorem
is conditional on the raw-mark invariant. No theorem in this layer manufactures
that invariant after New/Wait/Forward/Unify, creates a future run, or proves
progress.
`SequentialFigure7CrossRepresentativeWaitPreservation.lean` adds no hidden
source-region oracle. Its output-work classification follows only from the
typed destination's exact waiting prepend and unchanged ready/sigma fields;
its representative helper follows from exact core equality. The standalone
`WaitCreatedCandidate` contains only the inserted conclusion's tensor-below
data and middle-state unmarked-mate lookup. The final theorem is explicitly
conditional on `WaitCreatedRegionSeparated`, which states precisely the
remaining source-region obligation for prior ledger events. The finite
cross-representative executable may falsify that premise on generated
reachable cases, but no runtime result is imported into the theorem and zero
observed intersections is not used as proof.
`SequentialFigure7OlderEventFutureWorkTouchWaitPreservation.lean` adds no
touch, queue, geometry, history, or reachability oracle. It is indexed by an
already-successful typed `WaitStep`, a prior canonical history, its supplied
queued-head invariant, and the candidate-indexed
`WaitCreatedHeadTouchSeparated` premise. Exact destination and prepared-prefix
equations transport retained candidates. An actual inserted candidate is sent
directly to that residual; Wait contributes no new reservation event. Relative
to the prior invariant this is the exact transition-local obligation, but the
proof does not derive it from the scheduler invariant, history, or
reachability. It establishes no unconditional/global Wait,
Forward/UnifyPayload, same-boundary, raw/source-region seam, enabledness, or
progress result.
`SequentialFigure7CrossRepresentativeNewPreservation.lean` adds no hidden
source-region oracle. Its exact stack equations classify output work as
retained marked-middle work or a reached/partner endpoint at the fresh
boundary. Reservation appending preserves old representatives and makes the
new event a fresh self-root; output work bounds then prove that event cannot
be strictly older than any candidate. `NewCreatedCandidate` contains only an
actual endpoint's tensor-below data and marked-middle unmarked-mate lookup.
The final theorem is explicitly conditional on `NewCreatedRegionSeparated`
for prior events against those created candidates. No executable result is
imported into the proof.
`SequentialFigure7OlderEventFutureWorkTouchNewPreservation.lean` introduces no
new touch, queue, geometry, or reachability oracle. It is indexed by an
already-successful typed `NewStep`, a prior canonical history, and the supplied
prior queued-head invariant. Retained candidates use exact prepared/New state
transport. For a created endpoint, the proof converts an old ledger-event touch
to a prior history touch and the reached/partner identity to a current search
touch, then applies the existing cross-event disjointness theorem. Fresh-event
strict order is impossible by the existing maximality theorem. The result does
not derive the prior invariant, global availability, same-boundary exclusion,
another candidate-creating rule, a raw seam, enabledness, or progress.
`SequentialFigure7OlderRawMarkedRegionNewPreservation.lean` uses that exact
New candidate decomposition without adding a history or reachability oracle.
It is indexed by an already successful typed `NewStep`; the only additional
geometric premise is `NewRetainedRawMarksSeparated`. Exact step equations
transport marks and representatives, while structural correctness and
reference-switching acyclicity independently exclude the selected head from
every created region. The proof does not infer the retained-mark premise from
executable audits, canonical history, or scheduler reachability, and it does
not widen this theorem beyond New. Separate modules handle conditional Wait,
Forward, and Unify preservation; seam availability, unconditional preservation,
and progress remain open.
`SequentialFigure7OlderRawMarkedRegionWaitPreservation.lean` adds no history,
reachability, or correctness oracle. A typed `WaitStep` alone proves that the
destination representative is strictly below the selected raw-age
representative. Exact destination equations preserve the core, so retained
candidates and marks transport through Prepared; the selected mark is excluded
from created destination candidates by age. The final theorem is explicitly
conditional on `WaitRetainedRawMarksSeparated` for input-retained marks. That
premise is separate from `WaitCreatedRegionSeparated`, is not inferred from a
finite audit or history, and yields neither unconditional Wait nor progress.
`SequentialFigure7CrossRepresentativeForwardPreservation.lean` likewise adds
no hidden source-region oracle. Its output-work classification follows from
the exact active-ready prepend plus unchanged sigma and waiting fields.
Production-side par queuing preserves marks and parents, so its representative
and inherited-candidate transports are derived from concrete step equations.
`ForwardCreatedCandidate` contains only the inserted conclusion's tensor-below
data and prepared-middle mate-unmarked lookup. The final theorem is explicitly
conditional on `ForwardCreatedRegionSeparated`, the remaining source-region
obligation for strictly older prior ledger events. The preferred
`--cross-representative-search` mode and its `--wait-search` compatibility
alias use exact New/Forward/Unify transition replay, exact Wait payload
decoding, and independent nonzero coverage gates, including both New endpoints
and the Unify retired-class and moved-candidate paths. No
finite audit result is imported into any theorem, and no unconditional New,
Wait, Forward, or Unify preservation follows.
`SequentialFigure7OlderEventFutureWorkTouchForwardPreservation.lean` adds no
touch, queue, geometry, history, or reachability oracle. It is indexed by an
already-successful typed `ForwardStep`, a prior canonical history, its supplied
queued-head invariant, and the candidate-indexed
`ForwardCreatedHeadTouchSeparated` premise. Prepared and exact Forward
representative equations transport retained candidates. An actual inserted
candidate is sent directly to that residual; Forward contributes no new
reservation event. Relative to the prior invariant this is the exact
transition-local obligation, but the proof does not derive it from scheduler
invariants, history, or reachability. It establishes no unconditional/global
Forward, UnifyPayload, same-boundary, raw/source-region seam, enabledness, or
progress result.
`SequentialFigure7OlderRawMarkedRegionForwardPreservation.lean` adds no
history, reachability, correctness, or source-region oracle. It is indexed by
an already successful typed `ForwardStep`; exact prepare and queue equations
show that the selected mark and inserted candidate have the same active raw
age, while retained candidates and marks transport through Prepared. The final
theorem is explicitly conditional on `ForwardRetainedRawMarksSeparated` for
input-retained marks. That premise is separate from
`ForwardCreatedRegionSeparated`, is not inferred from a finite audit or
history, and yields neither unconditional Forward nor progress.
`SequentialFigure7CrossRepresentativeUnifyPayloadPreservation.lean` adds no
representative-stability or region oracle. Its exact if-map is derived from the
typed tensor union, with the active class redirected to the previous root and
all other prepared representatives retained. Exact output stack equations
bound every candidate at or below that previous boundary, which excludes a
retired-class event from the strict-older antecedent. The standalone
`UnifyPayloadCreatedCandidate` contains only the inserted conclusion's
tensor-below data and prepared-state mate-unmarked lookup. The final theorem is
explicitly conditional on `UnifyPayloadCreatedRegionSeparated`. The executable
audit replays the full union, payload activation, and drain and checks the
representative map, but no finite result is imported into the theorem and no
unconditional Unify preservation follows.
`SequentialFigure7OlderEventFutureWorkTouchUnifyPayloadPreservation.lean` adds
no touch, queue, geometry, history, reachability, or representative-stability
oracle. It is indexed by an already-successful typed `UnifyPayloadStep`, a prior
canonical history, its supplied queued-head invariant, and the
candidate-indexed `UnifyPayloadCreatedHeadTouchSeparated` premise. The proof
derives its representative transport from the exact typed union: strict output
order excludes the retired active class, while survivors and moved candidates
return to the prior invariant. An actual inserted candidate is sent directly
to the residual; UnifyPayload contributes no new reservation event. Relative
to the prior invariant this is the exact transition-local obligation, but the
proof does not derive it from scheduler invariants, history, or reachability.
It establishes no unconditional/global UnifyPayload, same-boundary,
raw/source-region seam, enabledness, or progress result.
`SequentialFigure7OlderRawMarkedRegionUnifyPayloadPreservation.lean` adds no
event-history, reachability, correctness, or representative-stability oracle.
It uses the typed output candidate bound to exclude every strictly older raw
mark from the retired active class; only then does it transport survivor and
moved candidates through the prepared invariant. Inserted tensor candidates
remain explicitly conditional on
`UnifyPayloadCreatedRawMarksSeparated`, measured before the union. This raw
premise is separate from `UnifyPayloadCreatedRegionSeparated`, is not inferred
from the finite audit or history, and yields neither unconditional Unify nor
progress.
`SequentialFigure7ReservationRealization.lean` introduces no component oracle.
Under the public theorems' explicit certificate structural-well-formedness
premise, it inducts over the same proof-carrying canonical history and
transports an event's exact submitted axiom membership through the typed
production updates.
For tensor union it obtains the other side from the already supplied
`ComponentForestProvenance`; structural `OccurrenceDerivation.owned_unique`
aligns the event-specific owned list with that final forest. The resulting
endpoint-accounting theorem does not classify every historical trace vertex as
owned and does not assume distinct events remain distinct components.
`SequentialFigure7RawMarkReservationAnchor.lean` adds no ownership or path
oracle. A concrete mark is transported through `RealizesSigma`; its assigned
age bound selects the authentic same-age ledger event. Existing exact marked
ownership and reservation endpoint accounting meet at the same representative
component, structural owned-list uniqueness aligns their carriers, and the
existing component reference geometry constructs both contained paths. The
theorem needs no declarative correctness or switching acyclicity, but it also
adds no cross-component composition, target avoidance, queue origin, raw-seam
discharge, enabledness, or progress result.
`SequentialFigure7CommitmentEdgeReferencePath.lean` adds one exact adjacent-edge
composition without adding a path oracle. `CommitmentSpine` recovers the typed
historical `NewStep`; raw-mark history retains its selected parent mark; the
existing parent and child component witnesses construct the owned anchors; and
the structural tensor/source-left path supplies the middle segment. Ordinary
walk composition plus verified loop erasure yields the canonical parent-left to
child-left simple path. No declarative correctness or acyclicity premise is
needed, and the theorem does not claim target avoidance, arbitrary multi-edge
composition, queue origin, a raw seam, enabledness, progress, completeness,
fallback removal, or complexity.
`SequentialFigure7CommitmentEdgeTargetAvoidance.lean` adds no avoidance oracle.
It consumes an explicit law saying that the exact child ledger event does not
touch a supplied future candidate's tensor conclusion. Existing ownership
accounting excludes that conclusion from the endpoint anchors; structural
producer uniqueness and the final mark equations exclude the historical tensor
collision; the explicit untouched law keeps it out of the historical source
trace.
Verified loop erasure then yields the avoiding canonical edge path. The law's
global availability, arbitrary multi-edge composition, queue origin, raw-seam
discharge, enabledness, progress, completeness, and complexity remain open.
`SequentialFigure7CommitmentIntervalTargetAvoidance.lean` adds no path or
avoidance oracle. It accepts an explicit avoiding witness for every adjacent
edge in a supplied positive-length retained-`sigma` interval, identifies shared
middle events through exact ledger lookups, and uses the already verified
`connectEraseAvoiding` operation. The theorem does not derive or globalize that
callback or the child-event untouched laws, cover a zero-edge interval, recover
queue origin, discharge a raw seam, imply progress, retain segment or
parallel-edge identity, or prove a complexity bound.
An explicit universally quantified proof that the structural region contains
neither remaining obstruction is sufficient to recover `FreshSourceLeftRun`,
then `NewInputNecessary`, and then `NewEnabled` through already-audited
bridges. Once a run is supplied, its input tag/raw-mark equations do separate
its carrier from prior touches and old marked owners;
`SequentialFigure7RegionBoundaries.lean` proves exactly those two facts over
the run's trace plus terminal partner. That conditional fact does not
manufacture the run or derive the clear premise from correctness.
Thus it adds no `NewGuard` sufficiency, reachable-state
exhaustiveness, progress, totality, pure-worklist completeness, fallback
removal, or linearity claim.
None of these local proofs establishes later-call totality, reachable-state
exhaustiveness, progress, pure-worklist completeness, fallback removal, or
linearity.
The separate `ProofNetIRNewProgressAudit.lean` executable introduces no new
axiom and does not manufacture invariant-shaped states. Each inspected state
comes with `ReachableByImplementedDispatcher`, built from an exact successful
initialization and exact dispatcher equations. A counterexample must retain
the accepted certificate, complete state, start, replayed rule kinds,
proof-relevant `NewGuard`, and the actual `new? = none` equation. Generated
certificate acceptance is obtained from `unificationCheck = true` and
transported to `check = true` by the kernel theorem
`unificationCheck_eq_check`; the 18 depth-0-through-2 cases additionally run
the direct all-switchings checker. The default and extended finite receipts
found no witness, but absence in 30 or 36 labelled cases is not an oracle,
universal `NewGuard`-sufficiency theorem, reachability characterization, or
progress result.
`SequentialFigure7TagHistory.lean` also adds no oracle. It pattern-matches only
the exact typed branch recovered from an existing `DispatchStep` and augments
the already-certified `ExecutedHistory`. The five stable branches prove array
equality; `new` retains the exact `NEXTAXIOM` result. The resulting theorems
characterize true tags by recorded touches, separate new touches from the
entire prior history, make submitted axiom-link positions globally
duplicate-free, show touched history-independence for a fixed state, and prove
recorded reservation-slot length equals final `nextAge`.
`ReachableByImplementedDispatcher` supplies such an augmented history, but
`SchedulerInvariant` alone does not: its tag field remains only a size check.
The all-true regression demonstrates that distinction without claiming a
separate nonreachability proof for that forged state.
`SequentialFigure7RawMarkHistory.lean` likewise adds no execution oracle. It
projects the already-successful typed witness retained by each
`DispatchTagEvidence`, exposes the common prepared selection, and proves exact
one-step and whole-history raw-mark provenance. Stable branches show why this
relation cannot be identified with `Touched`: they raw-mark a connective
conclusion without another `NEXTAXIOM` execution. The theorem adds neither
queue origin nor vertex-level commitment paths or target avoidance and does
not derive the four raw created-candidate seams, progress, or completeness.
The separate commitment-spine theorem establishes only final retained `sigma`
allocation ancestry and does not strengthen this raw-mark provenance claim.
`SequentialFigure7ProgressInvariant.lean` adds the public
`FutureWaitingUndefined` preservation family; those theorems remain within the
same audited standard boundary. The fixed tensor-adjacency, forged-future, and
route-orientation counterexamples live only in test executables and use
`native_decide` for closed certificate facts. They are explicitly executable regression
evidence, not public three-axiom theorems. The exact trust audit now covers 868
declarations: 586 use exactly `[propext, Classical.choice, Quot.sound]`, 25 are
axiom-free, 122 use exactly `[propext]`, and 135 use exactly
`[propext, Quot.sound]`.
`ConclusionBelow`'s
`NodeWellFormed` field is only a local ownership check; it does not replace a
whole-certificate `StructurallyWellFormed`/checked gate at a future untrusted
dispatcher entry point. Future guards must use raw
assigned ages—not representatives.

Four lower-level mutations are now in the kernel-checked API. `queuePar?` and
`queueTensor?` construct
the production components and increment the local connective count while
leaving the conclusion raw-unmarked; their theorems preserve component
formula consistency only from a prior consistency invariant plus explicit
`LinkWellFormed`; separate local theorems preserve abstraction, ordered
parents, carrier size, and started-axiom alignment. `prependReadyTop?` and
`mergeTopReadyWaiting?` perform the corresponding local stack changes. The
two-level stack merge deterministically chooses
`conclusion :: (payload ++ previousReady ++ activeReady)` although the source
algorithm uses sets, and its shape theorem requires explicit `Nodup` and
payload-bound evidence rather than deriving ownership from a queue scan.
The successful local `forward?` now composes the par and active-ready
primitives, but those primitives do not state a rule by themselves. These facts
now support a bounded `UnifyEmpty` executable/direct correspondence when
`W(j) = []`. Under `ReservationInvariant`, the successful executable identifies
the generic tensor roots with exact scheduler `j/i`, orients
`parent[i] := j`, and drains the empty previous cell. Soundness needs that
invariant; completeness/iff additionally require structural validity and the
separate ready-list `Nodup` premise. A successful executable preserves the
complete `ReservationInvariant`; under the stronger supplied
`SchedulerInvariant`, the typed and executable preservation theorems retain
the entire occurrence-exact state-only bundle.
These scheduler-level facts plus `UnifyOne` authorize the singleton branch with
the full state-only invariant. The arbitrary `UnifyPayload` executor now
combines the tensor, all stored waiting-par activations, and the drain, proving
the total `1 + |W(j)|` counter change and complete occurrence-exact invariant
preservation for every successful step from a full input invariant. Pure
input-only `UnifyPayloadEnabled` plus that invariant now proves executable
success and an invariant-preserving output; proving the predicate for every
intended dispatcher-selected reachable state remains open. The old
empty/singleton successes embed one way with the same output; no function
equality or reverse equivalence is trusted. Guerrini's rule specifies moving a
waiting set into ready; the project's stored head-to-tail order and explicit
derivation/provenance construction are representation refinements, not paper
claims, and imply neither commutativity nor paper temporal order. A canonical
successful-step dispatcher now exists, but no exhaustive branch-enabledness,
progress, scheduler/pure-worklist
completeness, O(1), or whole-program linearity claim follows.

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

That receipt does not imply a Figure-7 stack discipline. A stable small
accepted certificate with three axiom links and two tensors reconstructs in
two attempts, zero waiting requeues, and two firings. From its exact link order,
eager axiom initialization assigns ages 0, 1, and 2, and reverse connective
queuing first merges the age-0 and age-2 premises. Public statistics do not
expose token-class membership; the noncontiguous merge is derived from the
fixed certificate and implementation definitions. Consequently callers and
proofs must not assume contiguous age intervals, adjacent stack union, or LIFO
behavior for the flat worklist. `tagSchedulerFamily.step` is a selected
dependency-segment index, not firing time or token age.

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
 exact reverse.

The chord recursion now has a coordinate-exact implementation.
`SchedulerOccurrence` tags each scheduler visit by segment step and
in-segment offset, and the complete tagged family is proved duplicate-free
before its tags are erased. Erasure recovers the existing flattened edge
traversal. Exact cyclic cuts and descent traces map from tags to edge values;
a proof-relevant edge cut can also be lifted existentially from its retained
append decompositions. This general theorem does not recover a canonical visit
from an edge value, and the terminal-complement path no longer uses it. Every
surviving tag is inverted to its original segment/offset lookup, and each
recursive state recomputes its positioned par obstruction on those coordinates.
Each backward cut is bound to that exact obstruction. Lean reaches the terminal
forward cusp with a tagged state-and-interval descent from the original family,
then binds the terminal generator, arc, complement, derived strict cut, closed
walk, source-fixed reverse-shell normalization, and nesting trace in one
indexed witness. Coordinate-exact reverse-shell normalization erases to the
graph-level relation and retains the positional lift from each shell's stored
list decomposition. The terminal complement and all later nested cores compose
exact tagged cuts and shell descents back to the original scheduler family.
For an empty core, Lean additionally proves
that every exact visit has a distinct reverse-valued partner from another
scheduler step; same-step pairing is ruled out by simple-path edge-index
uniqueness. The strengthened terminal witness retains the complement's exact
closed walk and internal cusp-freedom. Every edge of an empty-core complement
is then proved reference-kept, the complement is transported to a nonempty
closed reference-switching-tree walk, and no complement tag can be the omitted
head of a flipped segment. One exact reverse pair is now oriented by strict
scheduler-step order with the complete segment-family decomposition retained.
Each positive offset is proved to lie in the concrete reference-retained
suffix after the unique omitted head, and that suffix retains its exact walk
to the classified target. Exact mask transport now preserves the two selected
suffix occurrences as one compacted reverse pair. The empty reverse-shell
trace is separately transported as two nonempty reference walks through one
midpoint, with the complete compacted closing traversal proved equal to the
reverse of the compacted opening traversal. A closed tree walk, including
this exact nested out-and-back form, is not itself contradictory. Instead Lean
uses the stronger inherited `CuspFreeTraversal`: the shell midpoint contains
an exact occurrence immediately followed by its reverse, hence a forbidden
cusp. The empty base is therefore excluded. The nontrivial closing-par base
remains; its exact first/last scheduler tags, segment/offset classifications,
and reference-kept forward last incidence are now retained. The same dependent
witness binds those tags to the par link, normalized closed core, and exact
`first :: middle ++ [last]` order. Its artificial closing seam is proved not
to be a same-segment or segment-boundary scheduler coordinate adjacency.
A private structural replay now threads that closing seam through the same
terminal reverse shells and omitted arc, then through every exact nesting and
backward-search frame, to the package's initial tagged family. In addition to
the older candidate cursor, it carries an occurrence-position endpoint zipper
whose gap is definitionally the complete complementary arc between the fixed
tagged endpoints. Every indexed flipped segment is nonempty, so an empty final
exact gap would force the scheduler-coordinate adjacency already excluded by
the endpoint witness. The exact initial-family gap is therefore nonempty.

The canonical replay of the fixed terminal step always first-opens before
ancestry begins. If `closing ++ opening` is nonempty, the reverse-shell frame
opens the gap first; otherwise the generator's nonempty omitted arc opens it in
the second frame. Lean retains the exact reverse equation, the omitted-right
zero-offset backward anchor, the forward retained-left last occurrence of the
outer terminal arc, and the canonical base gap
`closing ++ taggedArc ++ opening`. The erased outer arc is a closed `EdgeWalk`
at the complement base and a `CuspFreeTraversal`. Its exact cyclic closing pair
from the outer last occurrence to the anchor is a cusp, with non-reverse
directed endpoints; this is a wraparound closure rather than an internal cusp.
The first-opening proof uses the shell case split internally, but its returned
proposition does not expose the selected frame together with the anchor origin.
Endpoint-gap sublist preservation carries the whole `taggedArc` in its original
linear order through ancestry into the initial-family gap, retaining the same
named head and last occurrences. A generic theorem decomposes the containing
gap from those exact head/getLast lookups as
`g0 ++ anchor :: g1 ++ outerLast :: g2`; the endpoint zipper then yields
`CyclicFourPointDisplayAt firstTag lastTag anchor outerLast` for the initial
family. The relation permits empty intervening lists and repeated values
generically. It is not a strict scheduler-rank theorem: the ordered sublist is
not necessarily contiguous, and the display proves no fixed linear rank,
crossing, cyclic betweenness, or scheduler-order/proper-nesting contradiction.
It is therefore not yet closing-par exclusion or a progress theorem.
For the complete initial `tagSchedulerFamily`, Lean now derives
`[firstTag, lastTag, anchor, outerLast].Nodup` from duplicate-freedom of the
exact scheduler coordinates. Erasure is not injective here: the four erased
directed edges, their endpoints, and their vertices are not proved distinct.
The endpoint replay retains the same outer positioned par choice which named
`anchor` and `outerLast`; ancestry membership lifts that outer witness and the
inner normalized closing witness to the full initial family. The specialized
theorem returns both positioned witnesses with the display and four-tag
`Nodup`.
The displayed occurrence order
`firstTag → lastTag → anchor → outerLast` separates the inner and outer pairs;
it is not a crossing. No interval is proved nonempty, so contiguity, fixed or
modular rank, closing-par exclusion, progress, and pure-worklist completeness
remain open. Ordinary laminarity permits the separated pairs as siblings, and
the executable regression refutes generic flat token-age/LIFO containment.
The remaining flat-completeness option is a residual-witness preservation or
a theorem at the marked-domain/occurrence-thread quotient; exact-state and
structural-only confluence are too fine. Guerrini-style linearity instead
requires extending the bounded/tagged `NEXTAXIOM` checkpoint with later-state
selection and complete `R`/`W` token-age sequencing. Its exact oriented routes,
initial/local totality, per-call invariants, and strictly threaded touched-set
disjointness are already proved. The reservation wrapper now adds typed
initial/later calls, axiom-link-index replay exclusion for composable calls
under exact output tag threading, later `RealizesSigma` preservation, and a
bundled invariant preserved across both stages. The invariant-bound local
`new` layer now adds pop-before-mark, binary-mate lookup, raw-age marking,
post-mark search, and the operational old-boundary/fresh-top reservation. The
dedicated init/new history adds exact reachability and tag provenance for that
 fragment. Local `concl`/`nop`/`wait`/`forward`/`UnifyEmpty`/`UnifyOne` exist outside it; successful
 Forward has complete state-only invariant preservation and an independent
 direct rule with executable correspondence. Bounded `UnifyEmpty` and
 strict-singleton `UnifyOne` have direct correspondence, and successful
 typed/executable steps preserve the complete occurrence-exact state-only
 invariant. The local arbitrary-payload fold and atomic `UnifyPayload`
 composition exist outside the dedicated init/new history layer. Successful
 atomic steps preserve the complete occurrence-exact state-only invariant. The
 input-only `UnifyPayloadEnabled` theorem adds conditional applicability and an
 invariant-preserving result. The stable input-only predicates provide the same
 conditional result for `concl`, `nop`, `wait`, and `forward`, with only a
 submitted-par-local `nop`/`wait`/`forward` trichotomy. Neither layer proves
 exhaustive later branch enabledness,
 totality, or unconditional full-rule reachability. A separate canonical
 priority dispatcher and proof-carrying
 certified history now integrates all implemented successful branches, and its
 tag augmentation proves exact touch provenance, global submitted-slot
 non-reuse, and exact reservation-event counting against final `nextAge`. A
 public whole-history oriented-route theorem remains separate. No
planarity principle is assumed.

Lean now also constructs the exact simultaneous complementary
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
  retained-left occurrence on the orientation-correct side. Lean also orders
  the two conflict segments by an exact before/middle/after decomposition and
  cuts the cyclic family at the conclusion into two closed arcs. The first is
  nonempty and contains the omitted-right occurrence; retained-left lies in
  one of the arcs, and their concatenation covers the flipped occurrences up
  to the cyclic-rotation permutation. The exact rotation witness now transports
  internal cusp-freedom to the concatenation and to both arcs. A forward
  retained-left occurrence is the incoming chord path's exact last edge and,
  together with the omitted-right first-arc head, forms a kernel-proved par
  cusp at the new first-arc closing turn. A backward retained-left occurrence
  is the outgoing chord path's exact first edge and the nonempty second arc's
  head. The backward closing turn is now classified exactly: the cyclic
  rotation's closing boundary is cusp-free, and both reversed chord incidences
  carry the same par color. Hence the second arc closes cusp-free, is
  cyclically nonbacktracking, and is strictly shorter than the original
  flipped walk because the first arc is nonempty. This is a descent witness,
  not yet a `CuspFreeCycle`, because the second arc may repeat vertices. The
  descent now preserves pointwise indexed scheduler provenance and reference
  retention. Correctness exposes another backward-right par in the shorter
  arc, and Lean locates it at two distinct classified scheduler segments: the
  omitted right is one segment's head, while the retained left reaches the
  same conclusion internally from the other segment. Lean now packages these
  facts into a generic cyclic scheduler-subarc state. Rotating at omitted-right
  and cutting at retained-left either yields the forward closing par cusp or a
  strictly shorter backward state with all invariants and scheduler location
  preserved. Each step also retains the exact rotation/contiguous-subinterval
  witness in a proof-relevant cyclic-interval trace. Recursion on traversal
  length proves that a terminal forward par-cusp interval exists together with
  its state-and-interval trace back to the original flipped family. Every
  backward step in that trace now ties its exact scheduler tags, positioned
  obstruction, cyclic decompositions, retained suffix, and strict cut in one
  generator-exact witness. The
  terminal object now retains an exact nonempty, closed, internally cusp-free,
  strictly shorter
  complementary cyclic interval. A closing cusp on that complement is
  kernel-proved to be only the exact last/first reverse, not another nontrivial
  par cusp. Ordinary loop erasure is not used because it can create a new
  closing cusp at the erased vertex. Proof-relevant normalization now strips
  the exact reverse shells, retains their positional context and exact length
  equation, and transports scheduler provenance to the residual core.
  Cusp-free nonempty cores recursively produce strictly nested terminal
  forward cusps, so finite descent first leaves an empty shell core or a
  scheduler-located nontrivial closing-par core. The empty shell is now
  excluded by its forced midpoint cusp. The terminal cusp and its
  scheduler location are now carried by one position-aware witness, preventing
  later proofs from combining unrelated existential par occurrences; terminal
  bases likewise contain no independent duplicate location witness. The
  closing normalization and exact endpoint split now also share one explicit
  normalized list. The terminal-complement frame is now generator-exact and
  removes the first generic cut lift. The terminal base, data-indexed global
  ancestry, closing outcome, and normalized endpoint split are now assembled
  into one exact package: the first three share
  `(base, complementBase, taggedComplement, taggedNormalized)`, and the split
  shares that `taggedNormalized`. This does not yet expose the complete
  terminal `StepAt` frame as global indices; those data remain existential
  inside the step wrapper. The structural replay consumes each wrapper once
  and folds the terminal frame, exact backward cuts, reverse-shell arms,
  nesting, and global ancestry into an exact endpoint zipper replay. Its gap
  is the complete complementary endpoint arc, not the older cursor candidate.
  Nonemptiness of every indexed flipped segment makes the initial-family exact
  gap nonempty: emptiness would imply the coordinate adjacency already
  excluded by the endpoint witness.

  The canonical terminal replay now proves a first opening by an internal case
  split. Its first reverse-shell frame opens when its context is nonempty; the
  second, nonempty omitted-arc frame opens otherwise. The exact reverse equation,
  omitted-right anchor, outer retained-left last occurrence, and base-gap
  formula `closing ++ taggedArc ++ opening` are retained. Its erased outer arc
  is a closed, internally cusp-free walk with an exact nontrivial closing cusp
  from the outer last occurrence to the anchor. The internal shell case split
  constructs first opening, but the returned proposition does not bind its
  chosen frame to the separately retained anchor origin. Sublist monotonicity
  carries the complete outer `taggedArc` in its original linear order through
  ancestry to the initial-family gap. It retains the same head and last
  occurrences. Their exact lookups yield
  `g0 ++ anchor :: g1 ++ outerLast :: g2` and
  `CyclicFourPointDisplayAt firstTag lastTag anchor outerLast`. The generic
  display allows empty intervals and repeated values, and proves no
  contiguity, fixed linear rank, crossing, cyclic betweenness, or required
  scheduler-order/proper-nesting contradiction. In the complete initial
  `tagSchedulerFamily`, the four exact `SchedulerOccurrence` tags are now
  proved `Nodup`; both the inner positioned witness and the same outer
  positioned choice are retained after ancestry. This says nothing about
  distinct erased edges or
  vertices. The order is `firstTag → lastTag → anchor → outerLast`, which
  separates rather than crosses the two endpoint pairs; intervening intervals
  may still be empty. Ordinary laminarity permits this sibling placement, and
  the small accepted worklist regression rules out a generic flat
  age-interval/LIFO contradiction. Exact concrete-state confluence is also
  refuted on a derivation-generated correct certificate, and structural-only
  confluence is refuted on a structurally well-formed certificate. The
  remaining candidate quotient records the marked occurrence domain and
  occurrence-thread partition. No committed reproducible audit or theorem
  establishes confluence at that quotient.
  Residual-witness preservation or a theorem at this quotient remains a
  possible route to flat completeness. The bounded primitive already has
  per-call trace/tag invariants, exact oriented routes, initial/local
  rank-scoped totality, and strictly threaded touched-set disjointness;
  the operational waiting-cell domain and exact init/new history are also
  proved. Exact local `concl`/`nop`/`wait`/`forward`/`UnifyEmpty`/`UnifyOne` are also proved, and
  successful deterministic/executable `new`, `wait`, `forward`, and bounded
  `UnifyEmpty` and strict-singleton `UnifyOne` preserve the complete current
  occurrence-exact state-only invariant. A local arbitrary-payload fold and
  atomic tensor/fold/drain executor are proved separately, with complete
  successful-step occurrence-exact invariant preservation from a full input
  invariant. Conditional input-only applicability under `UnifyPayloadEnabled`
  is also kernel checked. A canonical successful-step dispatcher and certified
  history are also kernel checked. Final retained-`sigma` allocation ancestry
  is kernel checked as well, concrete raw marks have local contained paths to
  both endpoints of their same-age reservation event, and one adjacent
  cross-component path has an explicit-premise target-avoidance refinement.
  Explicit adjacent callbacks compose across any supplied positive-length
  retained interval. When the two strict separation invariants and the
  scheduler invariant are supplied, the child-event callback follows for each
  strictly older adjacent edge and for a positive interval whose last boundary
  is strictly older. The queued-head half has empty/init, stable,
  successful New, and conditional Wait/Forward/UnifyPayload preservation.
  Strict older events now split at the candidate's immediate predecessor and
  expose a composable positive prefix. Exhaustive later-state branch
  enabledness and totality, global invariant and all three residuals'
  availability, the final same-boundary callback,
  queue origin, the raw created-candidate seams, unconditional full-rule
  reachability, and the remaining `NEXTAXIOM`/token-age scheduler remain
  required for linearity.
  Closing-par scheduler-order exclusion, correct-state progress,
  pure-worklist completeness, recursive fallback removal, and whole-program
  linearity remain open.
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
