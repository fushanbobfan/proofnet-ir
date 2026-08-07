import ProofNetIR.SequentialFigure7TouchOrigin

namespace ProofNetIR

/-!
# Canonical Figure-7 reservation ledger

This module records every successful initialization or canonical `new`
reservation in chronological raw-age order.  Each ledger entry retains the
exact dependent `NEXTAXIOM` result and its oriented source-left route.

Raw ages are immutable allocation-time identifiers.  This ledger does not
identify them with later union-find representatives, identify historical
touched vertices with final live-component owners, or prove scheduler
progress, totality, worklist completeness, fallback removal, or complexity.
-/

namespace SequentialFigure7

open SequentialSchedulerBridge
open SequentialSchedulerState
open SequentialUnification

/-- Uniform proof-relevant view of one successful reservation search. -/
structure ReservationSearchEvent (certificate : Certificate) : Type where
  state : UnificationState
  fuel : Nat
  inputTags : Array Bool
  start : Vertex
  result : NextAxiomResult certificate state fuel inputTags
  reached : Vertex
  partner : Vertex
  route : NextAxiomRoute start result reached partner

namespace ReservationSearchEvent

/-- The submitted axiom-link position of this exact search. -/
def linkIndex {certificate : Certificate}
    (event : ReservationSearchEvent certificate) : Nat :=
  event.result.linkIndex

/-- Vertices touched by this exact search. -/
def Touched {certificate : Certificate}
    (event : ReservationSearchEvent certificate) (vertex : Vertex) : Prop :=
  event.result.Touched vertex

/-- The exact initial reservation witness as a uniform search event. -/
def ofInitial {certificate : Certificate} {after : ReservationState}
    {start : Vertex}
    (step : InitialReservationStep certificate after start) :
    ReservationSearchEvent certificate where
  state := (ReservationState.empty certificate).core
  fuel := certificate.formulas.size
  inputTags := (ReservationState.empty certificate).tags
  start := start
  result := step.result
  reached := step.reached
  partner := step.partner
  route := step.route

/-- The exact search inside a successful operational `new` event. -/
def ofNew {certificate : Certificate} {before after : ReservationState}
    (step : NewStep certificate before after) :
    ReservationSearchEvent certificate where
  state := step.coreMarked
  fuel := certificate.formulas.size
  inputTags := before.tags
  start := step.tensor.mate
  result := step.search
  reached := step.reached
  partner := step.partner
  route := step.route

/-- Every touched vertex lies in this event's complete historical source-left
region, including the returned terminal partner. -/
theorem touched_sourceLeftRegion
    {certificate : Certificate} (event : ReservationSearchEvent certificate)
    {vertex : Vertex} (touched : event.Touched vertex) :
    SourceLeftRegionVertex certificate event.start vertex :=
  event.route.touched_sourceLeftRegion touched

end ReservationSearchEvent

/-- One exact successful raw-age allocation event.

The constructors retain the complete operational witness, preventing the
raw age, source, route, or submitted slot from being detached from the event
that actually allocated it. -/
inductive ReservationEvent (certificate : Certificate) : Type where
  | initial {after : ReservationState} {start : Vertex}
      (step : InitialReservationStep certificate after start)
  | new {before after : ReservationState}
      (step : NewStep certificate before after)

namespace ReservationEvent

/-- Immutable raw age assigned when this event reserved its token. -/
def rawAge {certificate : Certificate} :
    ReservationEvent certificate → RawTokenAge
  | .initial _ => 0
  | @new _ before _ _ => before.stack.nextAge

end ReservationEvent

namespace NewStep

/-- The ready occurrence consumed by a successful `new` carries a strictly
older active raw age than the fresh reservation event allocated by that
step.  This compares immutable allocation ages, not union-find
representatives. -/
theorem activeRawAge_lt_reservationRawAge
    {certificate : Certificate} {before after : ReservationState}
    (step : NewStep certificate before after) :
    step.stackResult.rawAge < (ReservationEvent.new step).rawAge := by
  change step.stackResult.rawAge < before.stack.nextAge
  rcases SequentialStackState.popReadyMark?_exact step.stack_eq with
    ⟨_top, sigmaTop, _unmarked, _marks, _nextAge, _sigma, _ready,
      _waiting, _marked⟩
  rcases List.getLast?_eq_some_iff.mp sigmaTop with
    ⟨sigmaPrefix, sigmaEquation⟩
  have membership :
      step.stackResult.rawAge ∈ before.stack.sigma := by
    rw [sigmaEquation]
    simp
  exact
    step.before_invariant.stack_wellShaped.sigma_partition.boundary_lt
      step.stackResult.rawAge membership

end NewStep

namespace ReservationEvent

/-- Exact dependent search retained by this reservation event. -/
def search {certificate : Certificate} :
    ReservationEvent certificate → ReservationSearchEvent certificate
  | .initial step => .ofInitial step
  | .new step => .ofNew step

/-- Source occurrence from which this event ran `NEXTAXIOM`. -/
def start {certificate : Certificate}
    (event : ReservationEvent certificate) : Vertex :=
  event.search.start

/-- Submitted axiom-link position reserved by this event. -/
def linkIndex {certificate : Certificate}
    (event : ReservationEvent certificate) : Nat :=
  event.search.linkIndex

/-- Vertices touched by this exact historical event. -/
def Touched {certificate : Certificate}
    (event : ReservationEvent certificate) (vertex : Vertex) : Prop :=
  event.search.Touched vertex

/-- An event touch retains its exact historical source-left region. -/
theorem touched_sourceLeftRegion
    {certificate : Certificate} (event : ReservationEvent certificate)
    {vertex : Vertex} (touched : event.Touched vertex) :
    SourceLeftRegionVertex certificate event.start vertex :=
  event.search.touched_sourceLeftRegion touched

end ReservationEvent

namespace DispatchTagEvidence

/-- The chronological reservation events contributed by one dispatcher
step.  Only the `new` branch contributes an event. -/
def reservationEvents
    {certificate : Certificate} {before : ReservationState}
    {result : Figure7DispatchResult} :
    DispatchTagEvidence certificate before result →
      List (ReservationEvent certificate)
  | .new step => [.new step]
  | _ => []

/-- Appending one dispatch event's allocations to the prior raw-age prefix
produces exactly the result state's allocation prefix. -/
theorem range_append_reservationEvents
    {certificate : Certificate} {before : ReservationState}
    {result : Figure7DispatchResult}
    (evidence : DispatchTagEvidence certificate before result) :
    List.range before.stack.nextAge ++
        (evidence.reservationEvents.map ReservationEvent.rawAge) =
      List.range result.after.stack.nextAge := by
  have count := evidence.linkIndices_length_add_nextAge
  cases evidence with
  | concl step =>
      simp only [DispatchTagEvidence.linkIndices, List.length_nil,
        Nat.zero_add] at count
      simpa [reservationEvents] using congrArg List.range count
  | nop step =>
      simp only [DispatchTagEvidence.linkIndices, List.length_nil,
        Nat.zero_add] at count
      simpa [reservationEvents] using congrArg List.range count
  | new step =>
      simp only [DispatchTagEvidence.linkIndices, List.length_cons,
        List.length_nil] at count
      rw [← count]
      simpa [reservationEvents, ReservationEvent.rawAge, Nat.add_comm] using
        (List.range_succ (n := before.stack.nextAge)).symm
  | wait step =>
      simp only [DispatchTagEvidence.linkIndices, List.length_nil,
        Nat.zero_add] at count
      simpa [reservationEvents] using congrArg List.range count
  | forward step =>
      simp only [DispatchTagEvidence.linkIndices, List.length_nil,
        Nat.zero_add] at count
      simpa [reservationEvents] using congrArg List.range count
  | unifyPayload step =>
      simp only [DispatchTagEvidence.linkIndices, List.length_nil,
        Nat.zero_add] at count
      simpa [reservationEvents] using congrArg List.range count

end DispatchTagEvidence

namespace CanonicalTagHistory

/-- All initialization and `new` reservation events, oldest first. -/
def reservationLedger
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state} :
    CanonicalTagHistory certificate history →
      List (ReservationEvent certificate)
  | .empty => []
  | .init step => [.initial step]
  | .later prior evidence =>
      prior.reservationLedger ++ evidence.reservationEvents

/-- The ledger's raw ages are exactly `0, ..., nextAge - 1` in chronological
order.  This is an allocation-history fact, not a representative invariant. -/
theorem reservationLedger_rawAges
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history) :
    tagHistory.reservationLedger.map ReservationEvent.rawAge =
      List.range state.stack.nextAge := by
  induction tagHistory with
  | empty =>
      simp [reservationLedger, ReservationState.empty,
        SequentialStackState.empty]
  | init step =>
      rcases SequentialStackState.initEnqueue?_exact step.stack_eq with
        ⟨_marks, nextAge, _sigma, _ready, _waiting, _activeUndefined⟩
      have outputNextAge :=
        congrArg (fun current : ReservationState ↦ current.stack.nextAge)
          step.output_eq
      have finalNextAge : step.stackAfter.nextAge = 1 := nextAge
      have stateNextAge : _ = 1 := outputNextAge.trans finalNextAge
      rw [stateNextAge]
      rfl
  | later prior evidence induction =>
      rw [reservationLedger, List.map_append, induction]
      exact evidence.range_append_reservationEvents

/-- Ledger length agrees exactly with the final raw-age horizon. -/
theorem reservationLedger_length
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history) :
    tagHistory.reservationLedger.length = state.stack.nextAge := by
  have lengths := congrArg List.length tagHistory.reservationLedger_rawAges
  simpa using lengths

/-- Looking up an allocated raw age returns an event carrying exactly that
allocation-time age. -/
theorem reservationLedger_getElem?_rawAge
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (rawAge : RawTokenAge) (bound : rawAge < state.stack.nextAge) :
    Option.map ReservationEvent.rawAge
        tagHistory.reservationLedger[rawAge]? = some rawAge := by
  rw [← List.getElem?_map, tagHistory.reservationLedger_rawAges]
  exact List.getElem?_range bound

/-- Every allocated raw age selects a concrete event at that chronological
ledger position. -/
theorem reservationLedger_eventAtRawAge
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (rawAge : RawTokenAge) (bound : rawAge < state.stack.nextAge) :
    ∃ event : ReservationEvent certificate,
      tagHistory.reservationLedger[rawAge]? = some event ∧
        event.rawAge = rawAge := by
  exact Option.map_eq_some_iff.mp
    (tagHistory.reservationLedger_getElem?_rawAge rawAge bound)

/-- Chronological ledger slots are the reverse of the legacy newest-first
submitted-slot history. -/
theorem reservationLedger_linkIndices
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history) :
    tagHistory.reservationLedger.map ReservationEvent.linkIndex =
      tagHistory.linkIndices.reverse := by
  induction tagHistory with
  | empty => rfl
  | init step => rfl
  | later prior evidence induction =>
      rw [reservationLedger, List.map_append, induction, linkIndices,
        List.reverse_append]
      cases evidence <;>
        simp [DispatchTagEvidence.reservationEvents,
          DispatchTagEvidence.linkIndices, ReservationEvent.linkIndex,
          ReservationEvent.search, ReservationSearchEvent.linkIndex,
          ReservationSearchEvent.ofNew]

end CanonicalTagHistory

namespace CanonicalTouchOrigin

/-- An exact touch origin selects a concrete chronological ledger event whose
own search touched the vertex. -/
theorem reservationLedger_event
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {vertex : Vertex}
    (origin : CanonicalTouchOrigin certificate tagHistory vertex) :
    ∃ event : ReservationEvent certificate,
      event ∈ tagHistory.reservationLedger ∧ event.Touched vertex := by
  induction origin with
  | init step touched =>
      exact ⟨.initial step, by simp [CanonicalTagHistory.reservationLedger],
        touched⟩
  | @earlier before result history invariant dispatch prior evidence
      vertex origin induction =>
      rcases induction with ⟨event, membership, touched⟩
      exact ⟨event, by
        simp only [CanonicalTagHistory.reservationLedger, List.mem_append]
        exact Or.inl membership,
        touched⟩
  | @current before after history invariant dispatch prior step vertex
      touched =>
      exact ⟨.new step, by
        simp [CanonicalTagHistory.reservationLedger,
          DispatchTagEvidence.reservationEvents],
        touched⟩

end CanonicalTouchOrigin

namespace CanonicalTagHistory

/-- Every global canonical touch is carried by a concrete event in the
chronological reservation ledger. -/
theorem touched_reservationLedger_event
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    {vertex : Vertex} (touched : tagHistory.Touched vertex) :
    ∃ event : ReservationEvent certificate,
      event ∈ tagHistory.reservationLedger ∧ event.Touched vertex := by
  rcases tagHistory.touched_nonempty_origin touched with ⟨origin⟩
  exact origin.reservationLedger_event

end CanonicalTagHistory

end SequentialFigure7

end ProofNetIR
