/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7OlderEventFutureWorkTouchSeparation
import ProofNetIR.SequentialFigure7CrossRepresentativeUnifyPayloadPreservation

namespace ProofNetIR

/-!
# Figure-7 UnifyPayload preservation of older-event future-work head separation

A successful `unifyPayload` keeps the chronological reservation ledger fixed.
Every output future-work occurrence is inherited from the prepared state,
moved from the retired active boundary to the previous boundary, or inserted
as the selected tensor conclusion. The inherited and moved branches transport
the prior separation invariant. The inserted conclusion requires the explicit
transition-local premise below.

This module does not derive that premise from scheduler or history invariants,
and it proves no unconditional `unifyPayload` preservation, global
availability, target-path construction, raw separation, enabledness, progress,
totality, or completeness result.
-/

namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge

private theorem futureTouch_event_rawAge_lt_nextAge
    {certificate : Certificate} {before : ReservationState}
    {history : ExecutedHistory certificate before}
    (prior : CanonicalTagHistory certificate history)
    {event : ReservationEvent certificate}
    (membership : event ∈ prior.reservationLedger) :
    event.rawAge < before.stack.nextAge := by
  have mapped :
      event.rawAge ∈
        prior.reservationLedger.map ReservationEvent.rawAge :=
    List.mem_map_of_mem
      (f := fun e : ReservationEvent certificate ↦ e.rawAge) membership
  rw [prior.reservationLedger_rawAges] at mapped
  exact List.mem_range.mp mapped

namespace UnifyPayloadStep

private theorem futureTouch_previous_lt_active
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after) :
    step.previousBoundary < step.prepared.stackResult.rawAge :=
  Nat.lt_of_le_of_lt step.lower step.upper

private theorem futureTouch_middle_previous_root
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after) :
    step.prepared.after.core.representative step.previousBoundary =
      step.previousBoundary := by
  have middleInvariant :
      ReservationInvariant certificate step.prepared.after :=
    step.prepared.reservationInvariant step.before_invariant
  have mergeTop :
      step.prepared.stackResult.after.sigma.getLast? =
        some step.mergeStep.activeBoundary := by
    rw [step.mergeStep.sigma_eq]
    simp
  have preparedTop :
      step.prepared.stackResult.after.sigma.getLast? =
        some step.prepared.stackResult.rawAge := by
    rcases SequentialStackState.popReadyMark?_exact step.prepared.stack_eq with
      ⟨_, sigmaTop, _, _, _, sigmaAfter, _, _, _⟩
    rw [sigmaAfter]
    exact sigmaTop
  have activeEq :
      step.mergeStep.activeBoundary =
        step.prepared.stackResult.rawAge :=
    Option.some.inj (mergeTop.symm.trans preparedTop)
  have sigmaEquation :
      step.prepared.after.stack.sigma =
        step.mergeStep.sigmaPrefix ++
          [step.previousBoundary, step.prepared.stackResult.rawAge] := by
    simpa [PreparedStep.after, activeEq] using step.mergeStep.sigma_eq
  have previousMembership :
      step.previousBoundary ∈ step.prepared.after.stack.sigma := by
    rw [sigmaEquation]
    simp
  have previousBound :
      step.previousBoundary < step.prepared.after.stack.nextAge :=
    middleInvariant.stack_wellShaped.sigma_partition.boundary_lt _
      previousMembership
  have lookup :
      sigmaBoundary? step.prepared.after.stack.sigma
          step.previousBoundary =
        some step.previousBoundary :=
    middleInvariant.stack_wellShaped.sigma_partition
      |>.sigmaBoundary?_eq_previous_of_between
        sigmaEquation (Nat.le_refl _) step.futureTouch_previous_lt_active
  have realized :=
    middleInvariant.realizesSigma.representative_eq_boundary previousBound
  exact Option.some.inj (realized.symm.trans lookup)

private theorem futureTouch_event_representative_eq_prepared_of_older
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    (step : UnifyPayloadStep certificate before after)
    (invariant : SchedulerInvariant certificate before)
    (prior : CanonicalTagHistory certificate history)
    {event : ReservationEvent certificate}
    (eventMembership : event ∈ prior.reservationLedger)
    (candidate : FutureNewCandidateAt certificate after)
    (older :
      after.core.representative event.rawAge <
        after.core.representative candidate.rawAge) :
    after.core.representative event.rawAge =
      step.prepared.after.core.representative event.rawAge := by
  have middleInvariant := step.prepared.schedulerInvariant invariant
  have eventBeforeBound :=
    futureTouch_event_rawAge_lt_nextAge prior eventMembership
  have middleNextAge :
      step.prepared.after.stack.nextAge = before.stack.nextAge := by
    rcases SequentialStackState.popReadyMark?_exact step.prepared.stack_eq with
      ⟨_, _, _, _, nextAge, _, _, _, _⟩
    exact nextAge
  have eventMiddleBound :
      event.rawAge < step.prepared.after.core.parents.size := by
    rw [middleInvariant.realizesSigma.horizon_eq, middleNextAge]
    exact eventBeforeBound
  have mapped :=
    step.after_representative_eq_prepared_if eventMiddleBound
  by_cases retired :
      step.prepared.after.core.representative event.rawAge =
        step.prepared.stackResult.rawAge
  · have afterEvent :
        after.core.representative event.rawAge =
          step.previousBoundary := by
      simpa [retired] using mapped
    have afterCandidate :=
      candidate.work.representative_eq_rawAge
        (step.schedulerInvariant invariant)
    have candidateLe :=
      candidate.rawAge_le_previousBoundary_of_unifyPayload step invariant
    have impossible : step.previousBoundary < candidate.rawAge := by
      rw [afterEvent, afterCandidate] at older
      exact older
    exact (Nat.not_lt_of_ge candidateLe impossible).elim
  · simpa [retired] using mapped

end UnifyPayloadStep

/-- Every strictly older prior ledger event leaves the exact conclusion
inserted by a successful `unifyPayload` untouched.

This is only the residual old-event/inserted-head obligation. It does not
repeat the inherited- or moved-candidate cases covered by the prior invariant.
-/
def UnifyPayloadCreatedHeadTouchSeparated
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    (prior : CanonicalTagHistory certificate history)
    (step : UnifyPayloadStep certificate before after) : Prop :=
  ∀ {event : ReservationEvent certificate},
    event ∈ prior.reservationLedger →
    ∀ _created : UnifyPayloadCreatedCandidate certificate step,
      step.prepared.after.core.representative event.rawAge <
          step.prepared.after.core.representative step.previousBoundary →
        ¬ event.Touched step.consumer.conclusion

namespace UnifyPayloadStep

/-- A canonical `unifyPayload` extension preserves older-event future-work
head-touch separation when its newly inserted conclusion satisfies the
explicit residual touch premise.

The theorem applies to an already-successful typed `UnifyPayloadStep`. It does
not derive `UnifyPayloadCreatedHeadTouchSeparated`, handle another
candidate-creating rule, discharge a raw or source-region seam, or establish
scheduler progress.
-/
theorem olderEventFutureWorkTouchSeparated
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    {invariant : SchedulerInvariant certificate before}
    {dispatch :
      DispatchStep certificate before invariant ⟨.unifyPayload, after⟩}
    (step : UnifyPayloadStep certificate before after)
    (prior : CanonicalTagHistory certificate history)
    (separated : OlderEventFutureWorkTouchSeparated prior)
    (createdSeparated :
      UnifyPayloadCreatedHeadTouchSeparated prior step) :
    OlderEventFutureWorkTouchSeparated
      (CanonicalTagHistory.later (dispatch := dispatch) prior
        (DispatchTagEvidence.unifyPayload step)) := by
  refine { event_candidate := ?_ }
  intro event eventMembership candidate older
  have oldEventMembership : event ∈ prior.reservationLedger := by
    simpa [CanonicalTagHistory.reservationLedger,
      DispatchTagEvidence.reservationEvents] using eventMembership
  have afterInvariant := step.schedulerInvariant invariant
  have middleInvariant := step.prepared.schedulerInvariant invariant
  have eventUnchanged :=
    step.futureTouch_event_representative_eq_prepared_of_older invariant prior
      oldEventMembership candidate older
  have afterCandidateRoot :=
    candidate.work.representative_eq_rawAge afterInvariant
  rcases candidate.work.beforeUnifyPayloadOrMovedOrCreated step with
    oldWork | ⟨candidateAge, movedWork⟩ | ⟨candidateAge, candidateHead⟩
  · let middleCandidate :
        FutureNewCandidateAt certificate step.prepared.after := {
      rawAge := candidate.rawAge
      head := candidate.head
      work := oldWork
      tensor := candidate.tensor
      tensor_valid := candidate.tensor_valid
      mate_unmarked := by
        have mateUnmarked := candidate.mate_unmarked
        rw [step.after_marks_eq_prepared] at mateUnmarked
        exact mateUnmarked }
    let beforeCandidate : FutureNewCandidateAt certificate before :=
      middleCandidate.beforePrepared step.prepared
    have middleCandidateRoot :=
      oldWork.representative_eq_rawAge middleInvariant
    have olderMiddle :
        step.prepared.after.core.representative event.rawAge <
          step.prepared.after.core.representative candidate.rawAge := by
      calc
        step.prepared.after.core.representative event.rawAge =
            after.core.representative event.rawAge := eventUnchanged.symm
        _ < after.core.representative candidate.rawAge := older
        _ = candidate.rawAge := afterCandidateRoot
        _ = step.prepared.after.core.representative candidate.rawAge :=
          middleCandidateRoot.symm
    have olderBefore :
        before.core.representative event.rawAge <
          before.core.representative beforeCandidate.rawAge := by
      change
        before.core.representative event.rawAge <
          before.core.representative candidate.rawAge
      rw [← step.prepared.after_representative_eq_before event.rawAge,
        ← step.prepared.after_representative_eq_before candidate.rawAge]
      exact olderMiddle
    have oldUntouched :=
      separated.event_candidate oldEventMembership beforeCandidate olderBefore
    simpa [beforeCandidate, middleCandidate,
      FutureNewCandidateAt.beforePrepared] using oldUntouched
  · let middleCandidate :
        FutureNewCandidateAt certificate step.prepared.after := {
      rawAge := step.prepared.stackResult.rawAge
      head := candidate.head
      work := movedWork
      tensor := candidate.tensor
      tensor_valid := candidate.tensor_valid
      mate_unmarked := by
        have mateUnmarked := candidate.mate_unmarked
        rw [step.after_marks_eq_prepared] at mateUnmarked
        exact mateUnmarked }
    let beforeCandidate : FutureNewCandidateAt certificate before :=
      middleCandidate.beforePrepared step.prepared
    have movedRoot :=
      movedWork.representative_eq_rawAge middleInvariant
    have olderMiddle :
        step.prepared.after.core.representative event.rawAge <
          step.prepared.after.core.representative
            step.prepared.stackResult.rawAge := by
      calc
        step.prepared.after.core.representative event.rawAge =
            after.core.representative event.rawAge := eventUnchanged.symm
        _ < after.core.representative candidate.rawAge := older
        _ = candidate.rawAge := afterCandidateRoot
        _ = step.previousBoundary := candidateAge
        _ < step.prepared.stackResult.rawAge :=
          step.futureTouch_previous_lt_active
        _ = step.prepared.after.core.representative
            step.prepared.stackResult.rawAge := movedRoot.symm
    have olderBefore :
        before.core.representative event.rawAge <
          before.core.representative beforeCandidate.rawAge := by
      change
        before.core.representative event.rawAge <
          before.core.representative step.prepared.stackResult.rawAge
      rw [← step.prepared.after_representative_eq_before event.rawAge,
        ← step.prepared.after_representative_eq_before
          step.prepared.stackResult.rawAge]
      exact olderMiddle
    have oldUntouched :=
      separated.event_candidate oldEventMembership beforeCandidate olderBefore
    simpa [beforeCandidate, middleCandidate,
      FutureNewCandidateAt.beforePrepared] using oldUntouched
  · let created : UnifyPayloadCreatedCandidate certificate step := {
      tensor := candidate.tensor
      tensor_valid := by
        rw [← candidateHead]
        exact candidate.tensor_valid
      mate_unmarked := by
        have mateUnmarked := candidate.mate_unmarked
        rw [step.after_marks_eq_prepared] at mateUnmarked
        exact mateUnmarked }
    have olderMiddle :
        step.prepared.after.core.representative event.rawAge <
          step.prepared.after.core.representative step.previousBoundary := by
      calc
        step.prepared.after.core.representative event.rawAge =
            after.core.representative event.rawAge := eventUnchanged.symm
        _ < after.core.representative candidate.rawAge := older
        _ = candidate.rawAge := afterCandidateRoot
        _ = step.previousBoundary := candidateAge
        _ = step.prepared.after.core.representative step.previousBoundary :=
          step.futureTouch_middle_previous_root.symm
    intro touched
    exact createdSeparated oldEventMembership created olderMiddle
      (by simpa [candidateHead] using touched)

end UnifyPayloadStep

end SequentialFigure7

end ProofNetIR
