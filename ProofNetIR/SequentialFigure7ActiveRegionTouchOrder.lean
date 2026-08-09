import ProofNetIR.SequentialFigure7OlderEventTouchSeparation
import ProofNetIR.SequentialFigure7SameRepresentativeEventTouch

namespace ProofNetIR

/-!
# Figure-7 active-region historical-touch order

This module classifies a historical reservation-event touch of the active
`NewGuard` source-left region.  The current scheduler invariant first bounds
the event representative by the active representative; declarative
correctness then excludes equality through the existing same-representative
geometry.  Any overlap is therefore strictly older in both current
representative order and immutable raw-age order.

When `OlderEventTouchSeparated` is supplied, the strict-order result closes
the remaining overlap case and yields input tag freshness throughout the
active source-left region.  The existing structural invariant is accepted
through a compatibility theorem.

Nothing here constructs a route or run, proves raw-mark readiness or queue
capacity, establishes `OperationalNewReadyAt` or `NewEnabled`, or proves
scheduler progress, totality, or worklist completeness.
-/

namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge
open SequentialUnification

/-- Every reservation event in the chronological ledger was allocated before
the current raw-age horizon. -/
private theorem CanonicalTagHistory.event_rawAge_lt_nextAge
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    {event : ReservationEvent certificate}
    (membership : event ∈ tagHistory.reservationLedger) :
    event.rawAge < state.stack.nextAge := by
  have mapped :
      event.rawAge ∈
        tagHistory.reservationLedger.map ReservationEvent.rawAge :=
    List.mem_map.mpr ⟨event, membership, rfl⟩
  rw [tagHistory.reservationLedger_rawAges] at mapped
  simpa using mapped

/-- If a historical reservation event touches the active `NewGuard` source-left
region, its current representative is strictly older than the active ready
head's representative.

This is a conflict-order theorem.  It neither excludes the conflict nor proves
that the guarded `new` execution succeeds. -/
theorem CanonicalTagHistory.event_touch_active_region_implies_representative_lt
    {certificate : Certificate} {before : ReservationState}
    {history : ExecutedHistory certificate before}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate before)
    (guard : NewGuard certificate before)
    {event : ReservationEvent certificate}
    (eventMembership : event ∈ tagHistory.reservationLedger)
    {vertex : Vertex}
    (eventTouched : event.Touched vertex)
    (candidateRegion :
      SourceLeftRegionVertex certificate guard.tensor.mate vertex) :
    before.core.representative event.rawAge <
      before.core.representative guard.head.rawAge := by
  have eventAgeBound :=
    tagHistory.event_rawAge_lt_nextAge eventMembership
  have eventBoundary :=
    invariant.realizesSigma.representative_eq_boundary eventAgeBound
  have eventRepresentativeLeActive :
      before.core.representative event.rawAge ≤ guard.head.rawAge := by
    by_cases eventLtActive : event.rawAge < guard.head.rawAge
    · exact Nat.le_trans
        (UnificationState.OrderedParents.representative_le
          invariant.core_orderedParents event.rawAge)
        (Nat.le_of_lt eventLtActive)
    · have activeLeEvent : guard.head.rawAge ≤ event.rawAge :=
        Nat.le_of_not_gt eventLtActive
      have topLookup :=
        invariant.stack_wellShaped.sigma_partition.sigmaBoundary?_eq_top_of_le
          guard.head.sigma_top activeLeEvent eventAgeBound
      exact Nat.le_of_eq
        (Option.some.inj (eventBoundary.symm.trans topLookup))
  have activeRoot :
      before.core.representative guard.head.rawAge = guard.head.rawAge :=
    (guard.head.futureWorkAt invariant).representative_eq_rawAge invariant
  have eventRepresentativeLeActiveRepresentative :
      before.core.representative event.rawAge ≤
        before.core.representative guard.head.rawAge := by
    rw [activeRoot]
    exact eventRepresentativeLeActive
  have representativesNe :
      before.core.representative event.rawAge ≠
        before.core.representative guard.head.rawAge := by
    intro sameRepresentative
    exact tagHistory.not_event_touch_of_sameRepresentative
      correct invariant guard eventMembership sameRepresentative
      eventTouched candidateRegion
  exact Nat.lt_of_le_of_ne eventRepresentativeLeActiveRepresentative
    representativesNe

/-- An active-region historical-touch conflict is also strictly ordered by the
events' immutable raw ages. -/
theorem CanonicalTagHistory.event_touch_active_region_implies_rawAge_lt
    {certificate : Certificate} {before : ReservationState}
    {history : ExecutedHistory certificate before}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate before)
    (guard : NewGuard certificate before)
    {event : ReservationEvent certificate}
    (eventMembership : event ∈ tagHistory.reservationLedger)
    {vertex : Vertex}
    (eventTouched : event.Touched vertex)
    (candidateRegion :
      SourceLeftRegionVertex certificate guard.tensor.mate vertex) :
    event.rawAge < guard.head.rawAge := by
  have representativeLt :=
    tagHistory.event_touch_active_region_implies_representative_lt
      correct invariant guard eventMembership eventTouched candidateRegion
  have eventAgeBound :=
    tagHistory.event_rawAge_lt_nextAge eventMembership
  have eventBoundary :=
    invariant.realizesSigma.representative_eq_boundary eventAgeBound
  let candidate := guard.futureNewCandidateAt invariant
  have candidateMembership : candidate.rawAge ∈ before.stack.sigma :=
    candidate.work.rawAge_mem_sigma invariant
  have activeRoot :
      before.core.representative guard.head.rawAge = guard.head.rawAge :=
    (guard.head.futureWorkAt invariant).representative_eq_rawAge invariant
  refine Nat.lt_of_not_ge ?_
  intro candidateLeEvent
  have candidateLeEventRepresentative :
      candidate.rawAge ≤ before.core.representative event.rawAge :=
    sigmaBoundary?_greatest
      invariant.stack_wellShaped.sigma_partition.strictIncreasing
      eventBoundary candidate.rawAge candidateMembership candidateLeEvent
  have eventRepresentativeLtCandidate :
      before.core.representative event.rawAge < candidate.rawAge := by
    change before.core.representative event.rawAge < guard.head.rawAge
    simpa [activeRoot] using representativeLt
  exact (Nat.not_le_of_lt eventRepresentativeLtCandidate)
    candidateLeEventRepresentative

/-- Under older-event touch separation, every ledger event is touch-separated
from the active `NewGuard` source-left region. -/
theorem
    CanonicalTagHistory.event_touchSeparatedFrom_active_sourceLeftRegion_of_olderEventTouchSeparated
    {certificate : Certificate} {before : ReservationState}
    {history : ExecutedHistory certificate before}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate before)
    (guard : NewGuard certificate before)
    (separated : OlderEventTouchSeparated tagHistory)
    {event : ReservationEvent certificate}
    (eventMembership : event ∈ tagHistory.reservationLedger) :
    event.TouchSeparatedFrom guard.tensor.mate := by
  intro vertex eventTouched candidateRegion
  have older :=
    tagHistory.event_touch_active_region_implies_representative_lt
      correct invariant guard eventMembership eventTouched candidateRegion
  exact separated.event_candidate eventMembership
    (guard.futureNewCandidateAt invariant) older eventTouched candidateRegion

/-- Older-event touch separation makes every occurrence in the active
`NewGuard` source-left region false in the current input tag carrier. -/
theorem CanonicalTagHistory.active_sourceLeftRegion_tagFresh_of_olderEventTouchSeparated
    {certificate : Certificate} {before : ReservationState}
    {history : ExecutedHistory certificate before}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate before)
    (guard : NewGuard certificate before)
    (separated : OlderEventTouchSeparated tagHistory)
    {vertex : Vertex}
    (region :
      SourceLeftRegionVertex certificate guard.tensor.mate vertex) :
    before.tags[vertex]? = some false := by
  by_cases fresh : before.tags[vertex]? = some false
  · exact fresh
  · have touched :=
      tagHistory.classifyFreshTagBlocker invariant guard region fresh
    rcases tagHistory.touched_reservationLedger_event touched with
      ⟨event, eventMembership, eventTouched⟩
    have touchSeparated :=
      tagHistory.event_touchSeparatedFrom_active_sourceLeftRegion_of_olderEventTouchSeparated
        correct invariant guard separated eventMembership
    exact (touchSeparated eventTouched region).elim

/-- Compatibility form of active-region tag freshness for the existing
structural older-source-region invariant. -/
theorem CanonicalTagHistory.active_sourceLeftRegion_tagFresh_of_olderSourceRegionSeparated
    {certificate : Certificate} {before : ReservationState}
    {history : ExecutedHistory certificate before}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate before)
    (guard : NewGuard certificate before)
    (separated : OlderSourceRegionSeparated tagHistory)
    {vertex : Vertex}
    (region :
      SourceLeftRegionVertex certificate guard.tensor.mate vertex) :
    before.tags[vertex]? = some false :=
  tagHistory.active_sourceLeftRegion_tagFresh_of_olderEventTouchSeparated
    correct invariant guard separated.olderEventTouchSeparated region

end SequentialFigure7

end ProofNetIR
