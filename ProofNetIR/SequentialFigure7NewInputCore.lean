import ProofNetIR.SequentialFigure7StableEnabled
import ProofNetIR.SequentialFreshSourceLeftRun

namespace ProofNetIR

/-!
# Lower-layer input-state conditions for Figure-7 `new`

This module contains the declarative input views shared by the input-only
`NewEnabled` predicate and the public compatibility facade.  It deliberately
does not import the priority layer.

`NewGuard` is intentionally shallow: it records the ready head, its exact
well-formed tensor consumer, and the opposite premise's pre-state unmarked
condition.  It is necessary for executable `new`, but not sufficient.

`FreshSourceLeftRoute` records an exact bounded source-left chain to an exact
submitted axiom, together with input tag freshness and production readiness
for the whole trace and both terminal endpoints.  `NewInputNecessary` combines
that route with `NewGuard`; it remains strictly weaker than `NewEnabled`.
-/

namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge

/-- Shallow, input-only necessary guard for Figure-7 `new`.

The opposite premise is checked in the original production marking.  No tag
freshness, source route, executor equation, or output state is stored here, so
this type must not be read as sufficient executable applicability. -/
structure NewGuard (certificate : Certificate)
    (before : ReservationState) : Type where
  head : ReadyHeadInput before
  tensor : TensorBelow
  tensor_valid :
    tensor.Valid certificate certificate.consumerIndex head.vertex
  mate_unmarked : before.core.marks[tensor.mate]? = some none

namespace NewGuard

/-- A shallow guard determines the exact canonical tensor lookup. -/
theorem tensor_eq
    {certificate : Certificate} {before : ReservationState}
    (guard : NewGuard certificate before) :
    certificate.tensorBelow? guard.head.vertex = some guard.tensor :=
  Certificate.tensorBelow?_eq_some_iff.mpr guard.tensor_valid

/-- The selected ready occurrence and its tensor mate are distinct. -/
theorem mate_ne
    {certificate : Certificate} {before : ReservationState}
    (guard : NewGuard certificate before) :
    guard.tensor.mate ≠ guard.head.vertex :=
  Certificate.tensorBelow?_mate_ne guard.tensor_eq

end NewGuard

/-- Declarative input-state content of one fresh bounded source-left route.

The witness records only certificate structure, the input production marking,
the input tag carrier, and a finite list of visited vertices. `traceFresh`
means input tag freshness; `traceReady` records production readiness for every
visited occurrence, while endpoint readiness is recorded explicitly. This is
a necessary semantic projection of successful `NEXTAXIOM`, not by itself a
complete executable success criterion: it does not store recursive per-step
tag-update equations or the later operational enqueue guard. Under structural
well-formedness, `SequentialFigure7NewRegion` reconstructs the exact recursive
run and derives terminal-partner exclusion from this route; the enqueue guard
remains separate. -/
structure FreshSourceLeftRoute (certificate : Certificate)
    (state : UnificationState) (tags : Array Bool)
    (start : Vertex) : Type where
  trace : List Vertex
  reached : Vertex
  partner : Vertex
  linkIndex : Nat
  traceNonempty : trace ≠ []
  traceHead : trace.head? = some start
  traceLast : trace.getLast? = some reached
  chain : SequentialUnification.SourceLeftChain certificate trace
  reachable :
    SequentialUnification.SourceLeftReachable certificate start reached
  exactAxiom :
    certificate.links[linkIndex]? = some (.axiom reached partner) ∨
      certificate.links[linkIndex]? = some (.axiom partner reached)
  traceLength : trace.length ≤ certificate.formulas.size
  traceNodup : trace.Nodup
  traceFresh :
    ∀ {vertex : Vertex}, vertex ∈ trace → tags[vertex]? = some false
  traceReady :
    ∀ {vertex : Vertex}, vertex ∈ trace →
      state.marks[vertex]? = some none
  reachedReady : state.marks[reached]? = some none
  partnerReady : state.marks[partner]? = some none
  partnerFresh : tags[partner]? = some false

namespace FreshSourceLeftRoute

/-- The named start belongs to every nonempty exact route. -/
theorem start_mem
    {certificate : Certificate} {state : UnificationState}
    {tags : Array Bool} {start : Vertex}
    (route : FreshSourceLeftRoute certificate state tags start) :
    start ∈ route.trace := by
  cases traceEquation : route.trace with
  | nil => exact False.elim (route.traceNonempty traceEquation)
  | cons head tail =>
      have headEquation : head = start := by
        simpa [traceEquation] using route.traceHead
      subst head
      simp

/-- The route start is false in the exact input tag carrier. -/
theorem startFresh
    {certificate : Certificate} {state : UnificationState}
    {tags : Array Bool} {start : Vertex}
    (route : FreshSourceLeftRoute certificate state tags start) :
    tags[start]? = some false :=
  route.traceFresh route.start_mem

end FreshSourceLeftRoute

end SequentialFigure7

namespace SequentialUnification.FreshSourceLeftRun

/-- An exact run projects directly to the older result-free input route
whenever its fuel fits within the certificate carrier budget. -/
def toFreshSourceLeftRoute
    {certificate : Certificate}
    {state : UnificationState} {fuel : Nat} {tags : Array Bool}
    {start reached partner : Vertex} {trace : List Vertex}
    {linkIndex : Nat}
    (run : FreshSourceLeftRun certificate state fuel tags start
      trace reached partner linkIndex)
    (fuelBound : fuel ≤ certificate.formulas.size) :
    SequentialFigure7.FreshSourceLeftRoute certificate state tags start where
    trace := trace
    reached := reached
    partner := partner
    linkIndex := linkIndex
    traceNonempty := run.traceNonempty
    traceHead := run.traceHead
    traceLast := run.traceLast
    chain := run.sourceLeftChain
    reachable := run.sourceLeftReachable
    exactAxiom := run.exactAxiom
    traceLength := Nat.le_trans run.traceLength fuelBound
    traceNodup := run.traceNodup
    traceFresh := run.traceFresh
    traceReady := run.traceReady
    reachedReady := run.reachedReady
    partnerReady := run.partnerReady
    partnerFresh := run.partnerFresh

/-- Proposition-level compatibility wrapper for callers that only need
existence of the older route. -/
theorem toFreshSourceLeftRoute_nonempty
    {certificate : Certificate}
    {state : UnificationState} {fuel : Nat} {tags : Array Bool}
    {start reached partner : Vertex} {trace : List Vertex}
    {linkIndex : Nat}
    (run : FreshSourceLeftRun certificate state fuel tags start
      trace reached partner linkIndex)
    (fuelBound : fuel ≤ certificate.formulas.size) :
    Nonempty
      (SequentialFigure7.FreshSourceLeftRoute certificate state tags start) :=
  ⟨run.toFreshSourceLeftRoute fuelBound⟩

end SequentialUnification.FreshSourceLeftRun

namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge

/-- Read-only data for the input-only necessary Figure-7 `new` predicate.

`guard.head.markedCore` is a pure expression over the input state; it is not an
executor result.  The structure contains no `new?`/`nextAxiom?` equation and no
post-state.  No converse from this predicate to executable success is claimed.
-/
structure NewInput (certificate : Certificate)
    (before : ReservationState) : Type where
  guard : NewGuard certificate before
  route :
    FreshSourceLeftRoute certificate guard.head.markedCore before.tags
      guard.tensor.mate

/-- Input-only necessary witness proposition for Figure-7 `new`.

The name deliberately avoids `Enabled`: unlike the established Figure-7
`*Enabled` predicates, this proposition does not imply executor success. -/
def NewInputNecessary (certificate : Certificate)
    (before : ReservationState) : Prop :=
  Nonempty (NewInput certificate before)

namespace NewStep

/-- Recover the shallow ready-head view from the exact input queries of a typed
`new` success. -/
def readyHeadInput
    {certificate : Certificate} {before after : ReservationState}
    (step : NewStep certificate before after) : ReadyHeadInput before where
  vertex := step.stackResult.vertex
  readyTail := step.stackResult.remainingTop
  rawAge := step.stackResult.rawAge
  top_ready :=
    (SequentialStackState.popReadyMark?_exact step.stack_eq).1
  sigma_top :=
    (SequentialStackState.popReadyMark?_exact step.stack_eq).2.1

/-- The production state obtained by the typed raw-mark query is definitionally
the pure marked-core expression attached to its input-only ready head. -/
theorem coreMarked_eq_readyHeadInput
    {certificate : Certificate} {before after : ReservationState}
    (step : NewStep certificate before after) :
    step.coreMarked = step.readyHeadInput.markedCore := by
  rcases UnificationState.markReadyRaw?_ok_iff.mp step.core_mark_eq with
    ⟨marked⟩
  simpa [readyHeadInput, ReadyHeadInput.markedCore] using marked.after_eq

/-- The stack output of the typed pop prefix is exactly the pure marked-stack
expression attached to its recovered read-only head. -/
theorem stackAfter_eq_readyHeadInput
    {certificate : Certificate} {before after : ReservationState}
    (step : NewStep certificate before after) :
    step.stackResult.after = step.readyHeadInput.markedStack := by
  rcases SequentialStackState.popReadyMark?_ok_iff.mp step.stack_eq with
    ⟨marked⟩
  simpa [readyHeadInput, ReadyHeadInput.markedStack] using marked.after_eq

/-- The opposite tensor premise was already unmarked in the original input
state, before the selected ready occurrence was raw-marked. -/
theorem mate_unmarked_before
    {certificate : Certificate} {before after : ReservationState}
    (step : NewStep certificate before after) :
    before.core.marks[step.tensor.mate]? = some none := by
  have markExact :=
    UnificationState.markReadyRaw?_exact step.core_mark_eq
  have selectedNeMate :
      step.stackResult.vertex ≠ step.tensor.mate :=
    (Certificate.tensorBelow?_mate_ne step.tensor_eq).symm
  have unchanged :
      step.coreMarked.marks[step.tensor.mate]? =
        before.core.marks[step.tensor.mate]? := by
    rw [markExact.2.1]
    simp [selectedNeMate]
  exact unchanged.symm.trans step.mate_unmarked

/-- Every typed `new` success reconstructs the shallow input-only guard. -/
def guard
    {certificate : Certificate} {before after : ReservationState}
    (step : NewStep certificate before after) :
    NewGuard certificate before where
  head := step.readyHeadInput
  tensor := step.tensor
  tensor_valid := step.tensorValid
  mate_unmarked := step.mate_unmarked_before

/-- A typed `new` success projects to a result-free, equation-free fresh route
over its exact input marking and tags. -/
def freshSourceLeftRoute
    {certificate : Certificate} {before after : ReservationState}
    (step : NewStep certificate before after) :
    FreshSourceLeftRoute certificate step.coreMarked before.tags
      step.tensor.mate := by
  let route := step.route
  refine {
    trace := step.search.trace
    reached := step.reached
    partner := step.partner
    linkIndex := step.search.linkIndex
    traceNonempty := route.traceNonempty
    traceHead := route.traceHead
    traceLast := route.traceLast
    chain := route.chain
    reachable := route.reachable
    exactAxiom := route.exactAxiom
    traceLength := step.search.traceLength
    traceNodup := step.search.traceNodup
    traceFresh := fun membership ↦ (step.search.traceTagged membership).1
    traceReady :=
      SequentialUnification.nextAxiom?_traceReady step.search_eq
    reachedReady := ?_
    partnerReady := ?_
    partnerFresh := ?_ }
  · rcases route.storedEndpoints with
      ⟨reachedEq, partnerEq⟩ | ⟨reachedEq, partnerEq⟩
    · simpa [reachedEq] using step.search.leftReady
    · simpa [reachedEq] using step.search.rightReady
  · rcases route.storedEndpoints with
      ⟨reachedEq, partnerEq⟩ | ⟨reachedEq, partnerEq⟩
    · simpa [partnerEq] using step.search.rightReady
    · simpa [partnerEq] using step.search.leftReady
  · rcases route.storedEndpoints with
      ⟨reachedEq, partnerEq⟩ | ⟨reachedEq, partnerEq⟩
    · simpa [partnerEq] using step.search.rightTagged.1
    · simpa [partnerEq] using step.search.leftTagged.1

/-- A typed executable `new` success reconstructs the combined input-only
necessary predicate. -/
theorem inputNecessary
    {certificate : Certificate} {before after : ReservationState}
    (step : NewStep certificate before after) :
    NewInputNecessary certificate before := by
  refine ⟨{
    guard := step.guard
    route := ?_ }⟩
  change FreshSourceLeftRoute certificate step.readyHeadInput.markedCore
    before.tags step.tensor.mate
  rw [← step.coreMarked_eq_readyHeadInput]
  exact step.freshSourceLeftRoute

end NewStep

/-- Executable `new?` success implies the input-only necessary predicate.

There is deliberately no reverse theorem in this checkpoint. -/
theorem new?_success_implies_inputNecessary
    {certificate : Certificate} {before after : ReservationState}
    (invariant : ReservationInvariant certificate before)
    (equation : new? certificate before invariant = some after) :
    NewInputNecessary certificate before := by
  rcases (new?_some_iff invariant).mp equation with ⟨step⟩
  exact step.inputNecessary

end SequentialFigure7

end ProofNetIR
