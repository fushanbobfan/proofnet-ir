/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7CrossRepresentativeWaitPreservation
import ProofNetIR.SequentialFigure7OlderRawMarkedRegionSeparation

namespace ProofNetIR

/-!
# Figure-7 wait preservation of older raw-marked region separation

A successful `wait` retains the input raw marks, adds the selected raw mark,
and creates future candidates at the destination waiting boundary.  The
selected mark cannot be strictly older than that boundary, so only retained
input marks require an explicit separation assumption.

This module contains no history or reachability witness and no executor result
beyond the supplied typed `WaitStep`.  It proves conditional successful-step
preservation only, not applicability, totality, progress, or completeness.
-/

namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge
open SequentialUnification

/--
Every retained input raw mark that is strictly older than a candidate created
at the wait destination lies outside that candidate's source-left region.
-/
def WaitRetainedRawMarksSeparated
    {certificate : Certificate} {before after : ReservationState}
    (step : WaitStep certificate before after) : Prop :=
  ∀ created : WaitCreatedCandidate certificate step,
    OlderRawMarksSeparatedFrom certificate before
      step.destination.boundary created.tensor.mate

/--
The representative of the wait destination boundary is strictly below the
representative of the selected active raw age.
-/
theorem WaitStep.destination_representative_lt_selected
    {certificate : Certificate} {before after : ReservationState}
    (step : WaitStep certificate before after) :
    step.prepared.after.core.representative step.destination.boundary <
      step.prepared.after.core.representative
        step.prepared.stackResult.rawAge := by
  have middleInvariant :
      ReservationInvariant certificate step.prepared.after :=
    step.prepared.reservationInvariant step.before_invariant
  rcases SequentialStackState.popReadyMark?_exact step.prepared.stack_eq with
    ⟨_topReady, sigmaTopBefore, _selectedUnmarked, _stackMarks,
      _nextAge, sigmaEq, _readyEq, _waitingEq, stackSelectedMarked⟩
  have sigmaTopAfter :
      step.prepared.stackResult.after.sigma.getLast? =
        some step.prepared.stackResult.rawAge := by
    rw [sigmaEq]
    exact sigmaTopBefore
  have activeAgeBound :
      step.prepared.stackResult.rawAge <
        step.prepared.stackResult.after.nextAge :=
    middleInvariant.stack_wellShaped.assigned_age_bound
      step.prepared.stackResult.vertex step.prepared.stackResult.rawAge
      stackSelectedMarked
  have activeBoundary :=
    middleInvariant.stack_wellShaped.sigma_partition.sigmaBoundary?_eq_top
      sigmaTopAfter
  have activeRealized :=
    middleInvariant.realizesSigma.representative_eq_boundary activeAgeBound
  have activeRoot :
      step.prepared.after.core.representative
          step.prepared.stackResult.rawAge =
        step.prepared.stackResult.rawAge := by
    exact Option.some.inj (activeRealized.symm.trans activeBoundary)
  have boundaryRepresentativeLe :
      step.prepared.after.core.representative step.destination.boundary ≤
        step.destination.boundary :=
    UnificationState.OrderedParents.representative_le
      middleInvariant.core_orderedParents step.destination.boundary
  have boundaryLeMate :
      step.destination.boundary ≤ step.mateRawAge :=
    sigmaBoundary?_le step.destination.boundary_eq
  rw [activeRoot]
  exact Nat.lt_of_le_of_lt
    (Nat.le_trans boundaryRepresentativeLe boundaryLeMate) step.younger

/--
The created wait candidate is separated from every strictly older raw mark in
the prepared state: the selected mark is excluded by age, and every other mark
is transported from the retained-mark assumption.
-/
theorem WaitStep.created_rawMarksSeparatedFrom_of_retained
    {certificate : Certificate} {before after : ReservationState}
    (step : WaitStep certificate before after)
    (retained : WaitRetainedRawMarksSeparated step)
    (created : WaitCreatedCandidate certificate step) :
    OlderRawMarksSeparatedFrom certificate step.prepared.after
      step.destination.boundary created.tensor.mate := by
  intro rawAge vertex marked older
  by_cases selectedEq : step.prepared.stackResult.vertex = vertex
  · subst vertex
    have selectedMarked :
        step.prepared.after.core.marks[
            step.prepared.stackResult.vertex]? =
          some (some step.prepared.stackResult.rawAge) :=
      (UnificationState.markReadyRaw?_exact
        step.prepared.core_mark_eq).2.2.2.2.2.2
    have rawAgeEq : rawAge = step.prepared.stackResult.rawAge := by
      exact (Option.some.inj
        (Option.some.inj (selectedMarked.symm.trans marked))).symm
    subst rawAge
    have destinationLtSelected :=
      step.destination_representative_lt_selected
    exact (Nat.not_lt_of_ge
      (Nat.le_of_lt destinationLtSelected) older).elim
  · have beforeMarked :
        before.core.marks[vertex]? = some (some rawAge) := by
      change step.prepared.coreMarked.marks[vertex]? =
        some (some rawAge) at marked
      rw [(UnificationState.markReadyRaw?_exact
        step.prepared.core_mark_eq).2.1] at marked
      simpa [Array.getElem?_setIfInBounds, selectedEq] using marked
    have olderBefore :
        before.core.representative rawAge <
          before.core.representative step.destination.boundary := by
      rw [← step.prepared.after_representative_eq_before rawAge,
        ← step.prepared.after_representative_eq_before
          step.destination.boundary]
      exact older
    exact retained created rawAge vertex beforeMarked olderBefore

/--
A typed successful wait preserves older raw-marked region separation when its
retained input marks satisfy the explicit created-candidate side condition.
-/
theorem WaitStep.olderRawMarkedRegionSeparated
    {certificate : Certificate} {before after : ReservationState}
    (step : WaitStep certificate before after)
    (invariant : SchedulerInvariant certificate before)
    (separated : OlderRawMarkedRegionSeparated certificate before)
    (retained : WaitRetainedRawMarksSeparated step) :
    OlderRawMarkedRegionSeparated certificate after := by
  have middleSeparated :
      OlderRawMarkedRegionSeparated certificate step.prepared.after :=
    step.prepared.olderRawMarkedRegionSeparated invariant separated
  refine { candidate := ?_ }
  intro candidate
  intro rawAge vertex marked older
  have middleMarked :
      step.prepared.after.core.marks[vertex]? = some (some rawAge) := by
    rcases step.destination.exact with
      ⟨_payload, _initialized, _updated, _marks, _nextAge, _sigma,
        _ready, coreEquation, _tags⟩
    rw [coreEquation] at marked
    exact marked
  have olderMiddle :
      step.prepared.after.core.representative rawAge <
        step.prepared.after.core.representative candidate.rawAge := by
    rw [← step.destination.after_representative_eq_before rawAge,
      ← step.destination.after_representative_eq_before candidate.rawAge]
    exact older
  rcases candidate.work.beforeWaitOrInserted step with
    oldWork | ⟨candidateAge, candidateHead⟩
  · let middleCandidate :
        FutureNewCandidateAt certificate step.prepared.after := {
      rawAge := candidate.rawAge
      head := candidate.head
      work := oldWork
      tensor := candidate.tensor
      tensor_valid := candidate.tensor_valid
      mate_unmarked := by
        have mateUnmarked := candidate.mate_unmarked
        rcases step.destination.exact with
          ⟨_payload, _initialized, _updated, _marks, _nextAge, _sigma,
            _ready, coreEquation, _tags⟩
        rw [coreEquation] at mateUnmarked
        exact mateUnmarked }
    exact middleSeparated.candidate middleCandidate rawAge vertex
      middleMarked olderMiddle
  · let created : WaitCreatedCandidate certificate step := {
      tensor := candidate.tensor
      tensor_valid := by
        rw [← candidateHead]
        exact candidate.tensor_valid
      mate_unmarked := by
        have mateUnmarked := candidate.mate_unmarked
        rcases step.destination.exact with
          ⟨_payload, _initialized, _updated, _marks, _nextAge, _sigma,
            _ready, coreEquation, _tags⟩
        rw [coreEquation] at mateUnmarked
        exact mateUnmarked }
    have olderCreated :
        step.prepared.after.core.representative rawAge <
          step.prepared.after.core.representative
            step.destination.boundary := by
      rw [← candidateAge]
      exact olderMiddle
    simpa [created] using
      step.created_rawMarksSeparatedFrom_of_retained retained created
        rawAge vertex middleMarked olderCreated

end SequentialFigure7

end ProofNetIR
