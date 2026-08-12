/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7CrossRepresentativeInvariant

/-!
# Figure-7 strict older sigma split

Locates a historical reservation event's current representative strictly
before a supplied future-New candidate in the scheduler's `sigma` stack. The
result splits the retained interval into a possibly empty prefix ending at the
candidate's immediate predecessor and the final predecessor-to-candidate edge.

The prefix edge count may be zero when the historical representative is
already the candidate's predecessor. This module does not prove that the
final edge avoids the candidate conclusion, establish either older-event
separation invariant, or prove scheduler progress or completeness.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerBridge

/-- A retained `sigma` interval from `first` reaches the immediate predecessor
of `candidate` after `edgeCount` edges, followed by the final adjacent edge
into `candidate`. The prefix count may be zero. -/
def StrictOlderSigmaSplit
    (state : ReservationState)
    (first candidate : RawTokenAge) : Prop :=
  ∃ position edgeCount predecessor,
    state.stack.sigma[position]? = some first ∧
      state.stack.sigma[position + edgeCount]? = some predecessor ∧
      state.stack.sigma[position + edgeCount + 1]? = some candidate ∧
      state.core.representative predecessor <
        state.core.representative candidate

namespace CanonicalTagHistory

private theorem representative_eq_of_sigmaAt
    {certificate : Certificate} {state : ReservationState}
    (invariant : SchedulerInvariant certificate state)
    {position : Nat} {rawAge : RawTokenAge}
    (sigmaAt : state.stack.sigma[position]? = some rawAge) :
    state.core.representative rawAge = rawAge := by
  have rawAgeMembership : rawAge ∈ state.stack.sigma :=
    List.mem_of_getElem? sigmaAt
  have rawAgeBound : rawAge < state.stack.nextAge :=
    invariant.stack_wellShaped.sigma_partition.boundary_lt rawAge
      rawAgeMembership
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

private theorem event_rawAge_lt_nextAge
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

/-- A ledger event whose current representative is strictly older than a
future-New candidate determines an exact `sigma` split at the candidate's
immediate predecessor.

The returned prefix may have zero edges. The theorem locates the final edge
but makes no target-avoidance claim about it. -/
theorem strictOlderSigmaSplit
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (invariant : SchedulerInvariant certificate state)
    {event : ReservationEvent certificate}
    (eventMembership : event ∈ tagHistory.reservationLedger)
    (candidate : FutureNewCandidateAt certificate state)
    (older :
      state.core.representative event.rawAge <
        state.core.representative candidate.rawAge) :
    StrictOlderSigmaSplit state
      (state.core.representative event.rawAge) candidate.rawAge := by
  have eventBound :=
    tagHistory.event_rawAge_lt_nextAge eventMembership
  have eventLookup :=
    invariant.realizesSigma.representative_eq_boundary eventBound
  have eventMembershipSigma :
      state.core.representative event.rawAge ∈ state.stack.sigma :=
    sigmaBoundary?_mem eventLookup
  rcases List.getElem_of_mem eventMembershipSigma with
    ⟨eventPosition, eventPositionBound, eventAtValue⟩
  have eventAt :
      state.stack.sigma[eventPosition]? =
        some (state.core.representative event.rawAge) := by
    rw [List.getElem?_eq_getElem eventPositionBound, eventAtValue]
  have candidateMembership :
      candidate.rawAge ∈ state.stack.sigma :=
    candidate.work.rawAge_mem_sigma invariant
  rcases List.getElem_of_mem candidateMembership with
    ⟨candidatePosition, candidatePositionBound, candidateAtValue⟩
  have candidateAtPosition :
      state.stack.sigma[candidatePosition]? = some candidate.rawAge := by
    rw [List.getElem?_eq_getElem candidatePositionBound, candidateAtValue]
  have candidateRoot :
      state.core.representative candidate.rawAge = candidate.rawAge :=
    candidate.work.representative_eq_rawAge invariant
  have eventBeforeCandidate : eventPosition < candidatePosition := by
    by_cases candidateLeEvent : candidatePosition ≤ eventPosition
    · rcases Nat.eq_or_lt_of_le candidateLeEvent with same | before
      · have sameLookup :
            state.stack.sigma[eventPosition]? = some candidate.rawAge := by
          simpa [same] using candidateAtPosition
        have agesEq :
            state.core.representative event.rawAge = candidate.rawAge :=
          Option.some.inj (eventAt.symm.trans sameLookup)
        rw [candidateRoot, agesEq] at older
        exact (Nat.lt_irrefl _ older).elim
      · have ordered :=
          (List.pairwise_iff_getElem.mp
            invariant.stack_wellShaped.sigma_partition.strictIncreasing)
            candidatePosition eventPosition candidatePositionBound
            eventPositionBound before
        rw [candidateAtValue, eventAtValue] at ordered
        rw [candidateRoot] at older
        exact ((Nat.not_lt_of_ge (Nat.le_of_lt ordered)) older).elim
    · exact Nat.lt_of_not_ge candidateLeEvent
  let edgeCount := candidatePosition - eventPosition - 1
  have predecessorPositionBound :
      eventPosition + edgeCount < state.stack.sigma.length := by
    dsimp [edgeCount]
    omega
  let predecessor := state.stack.sigma[eventPosition + edgeCount]
  have predecessorAt :
      state.stack.sigma[eventPosition + edgeCount]? = some predecessor := by
    rw [List.getElem?_eq_getElem predecessorPositionBound]
  have candidateAt :
      state.stack.sigma[eventPosition + edgeCount + 1]? =
        some candidate.rawAge := by
    have indexEq :
        eventPosition + edgeCount + 1 = candidatePosition := by
      dsimp [edgeCount]
      omega
    simpa [indexEq] using candidateAtPosition
  have predecessorRawOlder : predecessor < candidate.rawAge := by
    rcases List.getElem?_eq_some_iff.mp predecessorAt with
      ⟨predecessorPositionBoundAgain, predecessorAtValue⟩
    have indexEq :
        eventPosition + edgeCount + 1 = candidatePosition := by
      dsimp [edgeCount]
      omega
    have ordered :=
      (List.pairwise_iff_getElem.mp
        invariant.stack_wellShaped.sigma_partition.strictIncreasing)
        (eventPosition + edgeCount) candidatePosition
        predecessorPositionBoundAgain candidatePositionBound (by omega)
    rw [predecessorAtValue, candidateAtValue] at ordered
    exact ordered
  have predecessorRoot :=
    representative_eq_of_sigmaAt invariant predecessorAt
  have predecessorOlder :
      state.core.representative predecessor <
        state.core.representative candidate.rawAge := by
    rw [predecessorRoot, candidateRoot]
    exact predecessorRawOlder
  exact ⟨eventPosition, edgeCount, predecessor, eventAt, predecessorAt,
    candidateAt, predecessorOlder⟩

end CanonicalTagHistory
end SequentialFigure7
end ProofNetIR
