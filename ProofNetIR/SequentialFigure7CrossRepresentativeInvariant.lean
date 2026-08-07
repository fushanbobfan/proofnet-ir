import ProofNetIR.SequentialFigure7SameRepresentativeGeometry

namespace ProofNetIR

/-!
# Figure-7 cross-representative source-region invariant

This module introduces the proof-relevant future-work domain needed by the
next progress layer.  Ready work retains its exact `sigma`/`ready` position;
waiting work retains its exact initialized cell.  A future `new` candidate is
therefore tied to one current scheduler boundary, one exact tensor consumer,
and the opposite premise's current raw-unmarked state.

`OlderSourceRegionSeparated` compares reservation events and future
candidates only when their *current union-find representatives* are strictly
ordered.  It deliberately does not compare immutable allocation ages and it
does not require separation for the reverse representative order.  This is a
history-indexed invariant foundation, not yet a preservation theorem for all
six Figure-7 rules and not a progress or completeness theorem.
-/

namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge
open SequentialUnification

/-- One occurrence currently stored as future scheduler work at an exact
raw-age boundary.

The ready constructor keeps the common positional index into `sigma` and
`ready`; the waiting constructor keeps the exact initialized waiting cell.
This avoids recovering a boundary from flattened queue membership. -/
inductive FutureWorkAt (state : ReservationState) :
    RawTokenAge → Vertex → Prop where
  | ready {position : Nat} {rawAge : RawTokenAge}
      {bucket : List Vertex} {vertex : Vertex}
      (sigmaAt : state.stack.sigma[position]? = some rawAge)
      (readyAt : state.stack.ready[position]? = some bucket)
      (member : vertex ∈ bucket) :
      FutureWorkAt state rawAge vertex
  | waiting {rawAge : RawTokenAge} {payload : List Vertex}
      {vertex : Vertex}
      (waitingAt : state.stack.waiting[rawAge]? =
        some (.initialized payload))
      (member : vertex ∈ payload) :
      FutureWorkAt state rawAge vertex

namespace FutureWorkAt

/-- Every precisely indexed future-work occurrence belongs to the flattened
executable queue. -/
theorem mem_queued
    {state : ReservationState} {rawAge : RawTokenAge} {vertex : Vertex}
    (work : FutureWorkAt state rawAge vertex) :
    vertex ∈ state.stack.queuedVertices := by
  induction work with
  | ready sigmaAt readyAt member =>
      unfold SequentialStackState.queuedVertices
      apply List.mem_append_left
      apply List.mem_flatten.mpr
      exact ⟨_, List.mem_of_getElem? readyAt, member⟩
  | @waiting rawAge payload vertex waitingAt member =>
      unfold SequentialStackState.queuedVertices
      apply List.mem_append_right
      unfold SequentialStackState.waitingVertices
      apply List.mem_flatMap.mpr
      refine ⟨.initialized payload, ?_, ?_⟩
      · exact List.mem_of_getElem? (by simpa using waitingAt)
      · simpa [WaitingCell.vertices] using member

/-- Under the complete scheduler invariant, every future-work boundary is a
current `sigma` boundary.  Waiting work uses its exact semantic span rather
than treating an arbitrary initialized storage cell as live work. -/
theorem rawAge_mem_sigma
    {certificate : Certificate} {state : ReservationState}
    {rawAge : RawTokenAge} {vertex : Vertex}
    (work : FutureWorkAt state rawAge vertex)
    (invariant : SchedulerInvariant certificate state) :
    rawAge ∈ state.stack.sigma := by
  cases work with
  | ready sigmaAt _readyAt _member =>
      exact List.mem_of_getElem? sigmaAt
  | waiting waitingAt member =>
      rcases invariant.waiting_span_exact waitingAt member with
        ⟨_linkIndex, _left, _right, _olderPremise, _youngerPremise,
          _olderAge, _youngerAge, _youngerBoundary,
          _linkLookup, _sourceLookup, _conclusionUnmarked,
          _premiseOrientation, _olderMarked, _youngerMarked,
          olderBoundary, _youngerBoundaryLookup, _boundaryLt⟩
      exact sigmaBoundary?_mem olderBoundary

/-- Every future-work boundary lies below the allocated raw-age horizon. -/
theorem rawAge_lt_nextAge
    {certificate : Certificate} {state : ReservationState}
    {rawAge : RawTokenAge} {vertex : Vertex}
    (work : FutureWorkAt state rawAge vertex)
    (invariant : SchedulerInvariant certificate state) :
    rawAge < state.stack.nextAge :=
  invariant.stack_wellShaped.sigma_partition.boundary_lt rawAge
    (work.rawAge_mem_sigma invariant)

/-- A live scheduler boundary is a root of the current ordered union-find.

This is a current-state representative fact.  It does not identify the
boundary with every immutable raw age in its interval. -/
theorem representative_eq_rawAge
    {certificate : Certificate} {state : ReservationState}
    {rawAge : RawTokenAge} {vertex : Vertex}
    (work : FutureWorkAt state rawAge vertex)
    (invariant : SchedulerInvariant certificate state) :
    state.core.representative rawAge = rawAge := by
  have rawAgeMembership : rawAge ∈ state.stack.sigma :=
    work.rawAge_mem_sigma invariant
  have rawAgeBound : rawAge < state.stack.nextAge :=
    work.rawAge_lt_nextAge invariant
  rcases
      invariant.stack_wellShaped.sigma_partition.boundary_exists rawAgeBound
    with ⟨boundary, boundaryLookup⟩
  have boundaryLeRawAge : boundary ≤ rawAge :=
    sigmaBoundary?_le boundaryLookup
  have rawAgeLeBoundary : rawAge ≤ boundary :=
    sigmaBoundary?_greatest
      invariant.stack_wellShaped.sigma_partition.strictIncreasing
      boundaryLookup rawAge rawAgeMembership (Nat.le_refl _)
  have boundaryEq : boundary = rawAge :=
    Nat.le_antisymm boundaryLeRawAge rawAgeLeBoundary
  subst boundary
  have representativeLookup :=
    invariant.realizesSigma.representative_eq_boundary rawAgeBound
  exact Option.some.inj (representativeLookup.symm.trans boundaryLookup)

end FutureWorkAt

namespace ReadyHeadInput

/-- The currently selected ready head is one precisely indexed future-work
occurrence at the active boundary. -/
theorem futureWorkAt
    {certificate : Certificate} {before : ReservationState}
    (input : ReadyHeadInput before)
    (invariant : SchedulerInvariant certificate before) :
    FutureWorkAt before input.rawAge input.vertex := by
  rcases List.getLast?_eq_some_iff.mp input.top_ready with
    ⟨readyPrefix, readyDecomposition⟩
  rcases List.getLast?_eq_some_iff.mp input.sigma_top with
    ⟨sigmaPrefix, sigmaDecomposition⟩
  have prefixLengths : readyPrefix.length = sigmaPrefix.length := by
    have aligned := invariant.stack_wellShaped.ready_aligned
    rw [readyDecomposition, sigmaDecomposition] at aligned
    simp at aligned
    omega
  apply FutureWorkAt.ready
      (position := readyPrefix.length)
      (bucket := input.vertex :: input.readyTail)
  · rw [sigmaDecomposition, prefixLengths]
    simp
  · rw [readyDecomposition]
    simp
  · simp

end ReadyHeadInput

/-- A currently queued occurrence whose exact tensor consumer could select a
future Figure-7 `new` once that occurrence becomes the active ready head.

This record stores no executor result, exact source-left run, output state,
history, or reachability witness. -/
structure FutureNewCandidateAt (certificate : Certificate)
    (state : ReservationState) : Type where
  rawAge : RawTokenAge
  head : Vertex
  work : FutureWorkAt state rawAge head
  tensor : TensorBelow
  tensor_valid :
    tensor.Valid certificate certificate.consumerIndex head
  mate_unmarked : state.core.marks[tensor.mate]? = some none

namespace NewGuard

/-- A shallow `NewGuard` is the active instance of the broader future-new
candidate view. -/
def futureNewCandidateAt
    {certificate : Certificate} {before : ReservationState}
    (guard : NewGuard certificate before)
    (invariant : SchedulerInvariant certificate before) :
    FutureNewCandidateAt certificate before where
  rawAge := guard.head.rawAge
  head := guard.head.vertex
  work := guard.head.futureWorkAt invariant
  tensor := guard.tensor
  tensor_valid := guard.tensor_valid
  mate_unmarked := guard.mate_unmarked

end NewGuard

/-- The complete structural source-left regions rooted at two starts share no
occurrence, including either region's terminal axiom partner. -/
def SourceLeftRegionsDisjoint (certificate : Certificate)
    (firstStart secondStart : Vertex) : Prop :=
  ∀ ⦃vertex : Vertex⦄,
    SourceLeftRegionVertex certificate firstStart vertex →
    SourceLeftRegionVertex certificate secondStart vertex → False

namespace SourceLeftRegionsDisjoint

/-- Structural source-region disjointness is symmetric. -/
theorem symm
    {certificate : Certificate} {firstStart secondStart : Vertex}
    (disjoint :
      SourceLeftRegionsDisjoint certificate firstStart secondStart) :
    SourceLeftRegionsDisjoint certificate secondStart firstStart := by
  intro vertex secondRegion firstRegion
  exact disjoint firstRegion secondRegion

end SourceLeftRegionsDisjoint

/-- Every historical reservation region whose current representative is
strictly older than a future candidate's current representative is disjoint
from that candidate's complete source-left region.

The strict order is exclusively a current union-find order.  No immutable
raw-age comparison is part of this invariant. -/
structure OlderSourceRegionSeparated
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history) : Prop where
  event_candidate :
    ∀ {event : ReservationEvent certificate},
      event ∈ tagHistory.reservationLedger →
      ∀ candidate : FutureNewCandidateAt certificate state,
        state.core.representative event.rawAge <
            state.core.representative candidate.rawAge →
          SourceLeftRegionsDisjoint certificate event.start
            candidate.tensor.mate

namespace OlderSourceRegionSeparated

/-- A touch of a strictly older reservation event cannot occur in the
candidate's source-left region.  This is the direct tag-only use of the
history-indexed separation invariant. -/
theorem not_event_touch_of_lt
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    (separated : OlderSourceRegionSeparated tagHistory)
    {event : ReservationEvent certificate}
    (eventMembership : event ∈ tagHistory.reservationLedger)
    (candidate : FutureNewCandidateAt certificate state)
    (older :
      state.core.representative event.rawAge <
        state.core.representative candidate.rawAge)
    {vertex : Vertex}
    (touched : event.Touched vertex)
    (candidateRegion :
      SourceLeftRegionVertex certificate candidate.tensor.mate vertex) :
    False :=
  separated.event_candidate eventMembership candidate older
    (event.touched_sourceLeftRegion touched) candidateRegion

end OlderSourceRegionSeparated

/-- The exact empty canonical history has no reservation event and therefore
satisfies cross-representative separation vacuously. -/
theorem empty_olderSourceRegionSeparated (certificate : Certificate) :
    OlderSourceRegionSeparated
      (CanonicalTagHistory.empty :
        CanonicalTagHistory certificate
          (ExecutedHistory.empty : ExecutedHistory certificate
            (ReservationState.empty certificate))) := by
  refine { event_candidate := ?_ }
  intro event membership
  simp [CanonicalTagHistory.reservationLedger] at membership

namespace InitialReservationStep

/-- One exact initialization has a singleton reservation ledger and a single
live boundary, so the strict current-representative premise is impossible. -/
theorem olderSourceRegionSeparated
    {certificate : Certificate} {after : ReservationState} {start : Vertex}
    (step : InitialReservationStep certificate after start)
    (structural : certificate.StructurallyWellFormed) :
    OlderSourceRegionSeparated (CanonicalTagHistory.init step) := by
  have invariant : SchedulerInvariant certificate after :=
    step.schedulerInvariant structural
  have outputStack :=
    congrArg (fun state : ReservationState => state.stack) step.output_eq
  have stackSigma :=
    (SequentialStackState.initEnqueue?_exact step.stack_eq).2.2.1
  have afterSigma : after.stack.sigma = [0] := by
    exact (congrArg SequentialStackState.sigma outputStack).trans stackSigma
  refine { event_candidate := ?_ }
  intro event membership candidate older
  simp only [CanonicalTagHistory.reservationLedger,
    List.mem_singleton] at membership
  subst event
  have candidateMembership : candidate.rawAge ∈ after.stack.sigma :=
    candidate.work.rawAge_mem_sigma invariant
  rw [afterSigma] at candidateMembership
  have candidateAge : candidate.rawAge = 0 := by
    simpa using candidateMembership
  rw [candidateAge] at older
  exact (Nat.lt_irrefl _ older).elim

end InitialReservationStep

end SequentialFigure7

end ProofNetIR
