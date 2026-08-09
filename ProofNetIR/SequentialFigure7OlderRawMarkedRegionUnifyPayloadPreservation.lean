/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7CrossRepresentativeUnifyPayloadPreservation
import ProofNetIR.SequentialFigure7OlderRawMarkedRegionSeparation

namespace ProofNetIR

/-!
# Figure-7 UnifyPayload preservation of older raw-marked region separation

A successful `unifyPayload` preserves surviving future work, moves the active
ready bucket to the previous boundary, and inserts the selected tensor
conclusion there. The survivor, moved, and created alternatives used below
cover every output candidate; they are not asserted to be mutually exclusive.

The active-to-previous representative union is the only representative change.
Strict older-than ordering excludes a marked token from the retired active
class whenever the output candidate remains future work. Survivors and moved
candidates therefore reduce to the prepared-state invariant. Candidates
created by the selected tensor use the explicit transition-local premise below.

This module contains no event history or reachability witness. It proves only
conditional successful-step preservation, not applicability, totality,
correctness, progress, or completeness.
-/

namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge
open SequentialUnification

/--
Every prepared-state raw mark strictly older than a candidate created by the
selected tensor lies outside that candidate's source-left region.
-/
def UnifyPayloadCreatedRawMarksSeparated
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after) : Prop :=
  ∀ created : UnifyPayloadCreatedCandidate certificate step,
    OlderRawMarksSeparatedFrom certificate step.prepared.after
      step.previousBoundary created.tensor.mate

private theorem UnifyPayloadStep.middle_previous_root
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after) :
    step.prepared.after.core.representative step.previousBoundary =
      step.previousBoundary := by
  have middleInvariant :
      ReservationInvariant certificate step.prepared.after :=
    step.prepared.reservationInvariant step.before_invariant
  have previousLtActive :
      step.previousBoundary < step.prepared.stackResult.rawAge :=
    Nat.lt_of_le_of_lt step.lower step.upper
  have sigmaEquation :
      step.prepared.after.stack.sigma =
        step.mergeStep.sigmaPrefix ++
          [step.previousBoundary, step.prepared.stackResult.rawAge] := by
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
        sigmaEquation (Nat.le_refl _) previousLtActive
  have realized :=
    middleInvariant.realizesSigma.representative_eq_boundary previousBound
  exact Option.some.inj (realized.symm.trans lookup)

private theorem UnifyPayloadStep.rawMark_representative_eq_prepared_of_older
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after)
    (invariant : SchedulerInvariant certificate before)
    (candidate : FutureNewCandidateAt certificate after)
    {rawAge : RawTokenAge} {vertex : Vertex}
    (marked : after.core.marks[vertex]? = some (some rawAge))
    (older :
      after.core.representative rawAge <
        after.core.representative candidate.rawAge) :
    after.core.representative rawAge =
      step.prepared.after.core.representative rawAge := by
  have afterInvariant := step.schedulerInvariant invariant
  have middleInvariant := step.prepared.schedulerInvariant invariant
  have middleMarked :
      step.prepared.after.core.marks[vertex]? = some (some rawAge) := by
    have transported := marked
    rw [step.after_marks_eq_prepared] at transported
    exact transported
  have middleStackMarked :
      step.prepared.after.stack.marks[vertex]? = some (some rawAge) := by
    rw [← middleInvariant.realizesSigma.marks_eq]
    exact middleMarked
  have rawAgeStackBound :
      rawAge < step.prepared.after.stack.nextAge :=
    middleInvariant.stack_wellShaped.assigned_age_bound
      vertex rawAge middleStackMarked
  have rawAgeCoreBound :
      rawAge < step.prepared.after.core.parents.size := by
    rw [middleInvariant.realizesSigma.horizon_eq]
    exact rawAgeStackBound
  have mapped :=
    step.after_representative_eq_prepared_if rawAgeCoreBound
  by_cases retired :
      step.prepared.after.core.representative rawAge =
        step.prepared.stackResult.rawAge
  · have afterRaw :
        after.core.representative rawAge = step.previousBoundary := by
      simpa [retired] using mapped
    have afterCandidateRoot :=
      candidate.work.representative_eq_rawAge afterInvariant
    have candidateLe :=
      candidate.rawAge_le_previousBoundary_of_unifyPayload step invariant
    have impossible : step.previousBoundary < candidate.rawAge := by
      rw [afterRaw, afterCandidateRoot] at older
      exact older
    exact (Nat.not_lt_of_ge candidateLe impossible).elim
  · simpa [retired] using mapped

/--
A successful typed `unifyPayload` step preserves older raw-marked region
separation when its newly inserted tensor candidates satisfy the explicit
transition-local separation premise.
-/
theorem UnifyPayloadStep.olderRawMarkedRegionSeparated
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after)
    (invariant : SchedulerInvariant certificate before)
    (separated : OlderRawMarkedRegionSeparated certificate before)
    (createdSeparated : UnifyPayloadCreatedRawMarksSeparated step) :
    OlderRawMarkedRegionSeparated certificate after := by
  have afterInvariant := step.schedulerInvariant invariant
  have middleInvariant := step.prepared.schedulerInvariant invariant
  have middleSeparated :
      OlderRawMarkedRegionSeparated certificate step.prepared.after :=
    step.prepared.olderRawMarkedRegionSeparated invariant separated
  have previousLtActive :
      step.previousBoundary < step.prepared.stackResult.rawAge :=
    Nat.lt_of_le_of_lt step.lower step.upper
  refine { candidate := ?_ }
  intro candidate rawAge vertex marked older region
  have middleMarked :
      step.prepared.after.core.marks[vertex]? = some (some rawAge) := by
    have transported := marked
    rw [step.after_marks_eq_prepared] at transported
    exact transported
  have rawUnchanged :=
    step.rawMark_representative_eq_prepared_of_older
      invariant candidate marked older
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
        have transported := candidate.mate_unmarked
        rw [step.after_marks_eq_prepared] at transported
        exact transported }
    have middleCandidateRoot :=
      oldWork.representative_eq_rawAge middleInvariant
    have olderMiddle :
        step.prepared.after.core.representative rawAge <
          step.prepared.after.core.representative candidate.rawAge := by
      calc
        step.prepared.after.core.representative rawAge =
            after.core.representative rawAge := rawUnchanged.symm
        _ < after.core.representative candidate.rawAge := older
        _ = candidate.rawAge := afterCandidateRoot
        _ = step.prepared.after.core.representative candidate.rawAge :=
          middleCandidateRoot.symm
    exact middleSeparated.candidate middleCandidate rawAge vertex
      middleMarked olderMiddle region
  · let middleCandidate :
        FutureNewCandidateAt certificate step.prepared.after := {
      rawAge := step.prepared.stackResult.rawAge
      head := candidate.head
      work := movedWork
      tensor := candidate.tensor
      tensor_valid := candidate.tensor_valid
      mate_unmarked := by
        have transported := candidate.mate_unmarked
        rw [step.after_marks_eq_prepared] at transported
        exact transported }
    have movedRoot :=
      movedWork.representative_eq_rawAge middleInvariant
    have olderMiddle :
        step.prepared.after.core.representative rawAge <
          step.prepared.after.core.representative
            step.prepared.stackResult.rawAge := by
      calc
        step.prepared.after.core.representative rawAge =
            after.core.representative rawAge := rawUnchanged.symm
        _ < after.core.representative candidate.rawAge := older
        _ = candidate.rawAge := afterCandidateRoot
        _ = step.previousBoundary := candidateAge
        _ < step.prepared.stackResult.rawAge := previousLtActive
        _ = step.prepared.after.core.representative
            step.prepared.stackResult.rawAge := movedRoot.symm
    exact middleSeparated.candidate middleCandidate rawAge vertex
      middleMarked olderMiddle region
  · let created : UnifyPayloadCreatedCandidate certificate step := {
      tensor := candidate.tensor
      tensor_valid := by
        rw [← candidateHead]
        exact candidate.tensor_valid
      mate_unmarked := by
        have transported := candidate.mate_unmarked
        rw [step.after_marks_eq_prepared] at transported
        exact transported }
    have olderMiddle :
        step.prepared.after.core.representative rawAge <
          step.prepared.after.core.representative step.previousBoundary := by
      calc
        step.prepared.after.core.representative rawAge =
            after.core.representative rawAge := rawUnchanged.symm
        _ < after.core.representative candidate.rawAge := older
        _ = candidate.rawAge := afterCandidateRoot
        _ = step.previousBoundary := candidateAge
        _ = step.prepared.after.core.representative step.previousBoundary :=
          step.middle_previous_root.symm
    exact createdSeparated created rawAge vertex middleMarked olderMiddle region

end SequentialFigure7

end ProofNetIR
