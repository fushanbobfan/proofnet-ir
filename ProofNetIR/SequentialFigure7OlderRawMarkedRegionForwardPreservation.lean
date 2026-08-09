/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7CrossRepresentativeForwardPreservation
import ProofNetIR.SequentialFigure7OlderRawMarkedRegionSeparation

namespace ProofNetIR

/-!
# Figure-7 forward preservation of older raw-marked region separation

A successful `forward` retains the prepared raw marks and creates future
candidates at the active raw-age boundary by prepending the submitted par
conclusion. The selected mark has exactly that active raw age, so it cannot
satisfy the strict older-representative guard. Only retained input marks
require an explicit separation assumption.

This module contains no history or reachability witness and no executor result
beyond the supplied typed `ForwardStep`. It proves conditional successful-step
preservation only, not applicability, totality, progress, or completeness.
-/

namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge
open SequentialUnification

/--
Every retained input raw mark that is strictly older than a candidate created
at the active forward boundary lies outside that candidate's source-left
region.
-/
def ForwardRetainedRawMarksSeparated
    {certificate : Certificate} {before after : ReservationState}
    (step : ForwardStep certificate before after) : Prop :=
  ∀ created : ForwardCreatedCandidate certificate step,
    OlderRawMarksSeparatedFrom certificate before
      step.prepared.stackResult.rawAge created.tensor.mate

/--
A created forward candidate is separated from every strictly older raw mark in
the prepared state: the selected mark has the same raw age as the created
boundary, and every other mark transports from the retained-mark assumption.
-/
theorem ForwardStep.created_rawMarksSeparatedFrom_of_retained
    {certificate : Certificate} {before after : ReservationState}
    (step : ForwardStep certificate before after)
    (retained : ForwardRetainedRawMarksSeparated step)
    (created : ForwardCreatedCandidate certificate step) :
    OlderRawMarksSeparatedFrom certificate step.prepared.after
      step.prepared.stackResult.rawAge created.tensor.mate := by
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
    exact (Nat.lt_irrefl _ older).elim
  · have beforeMarked :
        before.core.marks[vertex]? = some (some rawAge) := by
      change step.prepared.coreMarked.marks[vertex]? =
        some (some rawAge) at marked
      rw [(UnificationState.markReadyRaw?_exact
        step.prepared.core_mark_eq).2.1] at marked
      simpa [Array.getElem?_setIfInBounds, selectedEq] using marked
    have olderBefore :
        before.core.representative rawAge <
          before.core.representative
            step.prepared.stackResult.rawAge := by
      rw [← step.prepared.after_representative_eq_before rawAge,
        ← step.prepared.after_representative_eq_before
          step.prepared.stackResult.rawAge]
      exact older
    exact retained created rawAge vertex beforeMarked olderBefore

/--
A typed successful forward preserves older raw-marked region separation when
its retained input marks satisfy the explicit created-candidate side
condition.
-/
theorem ForwardStep.olderRawMarkedRegionSeparated
    {certificate : Certificate} {before after : ReservationState}
    (step : ForwardStep certificate before after)
    (invariant : SchedulerInvariant certificate before)
    (separated : OlderRawMarkedRegionSeparated certificate before)
    (retained : ForwardRetainedRawMarksSeparated step) :
    OlderRawMarkedRegionSeparated certificate after := by
  have middleSeparated :
      OlderRawMarkedRegionSeparated certificate step.prepared.after :=
    step.prepared.olderRawMarkedRegionSeparated invariant separated
  refine { candidate := ?_ }
  intro candidate
  intro rawAge vertex marked older
  have middleMarked :
      step.prepared.after.core.marks[vertex]? = some (some rawAge) := by
    have afterCore : after.core = step.coreAfter :=
      congrArg (fun state : ReservationState ↦ state.core) step.output_eq
    rw [afterCore] at marked
    change step.coreAfter.marks[vertex]? = some (some rawAge) at marked
    rw [step.queueStep.after_eq] at marked
    exact marked
  have olderMiddle :
      step.prepared.after.core.representative rawAge <
        step.prepared.after.core.representative candidate.rawAge := by
    rw [← step.after_representative_eq_prepared rawAge,
      ← step.after_representative_eq_prepared candidate.rawAge]
    exact older
  rcases candidate.work.beforeForwardOrInserted step with
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
        have afterCore : after.core = step.coreAfter :=
          congrArg (fun state : ReservationState ↦ state.core)
            step.output_eq
        rw [afterCore] at mateUnmarked
        change step.coreAfter.marks[candidate.tensor.mate]? = some none
          at mateUnmarked
        rw [step.queueStep.after_eq] at mateUnmarked
        exact mateUnmarked }
    exact middleSeparated.candidate middleCandidate rawAge vertex
      middleMarked olderMiddle
  · let created : ForwardCreatedCandidate certificate step := {
      tensor := candidate.tensor
      tensor_valid := by
        rw [← candidateHead]
        exact candidate.tensor_valid
      mate_unmarked := by
        have mateUnmarked := candidate.mate_unmarked
        have afterCore : after.core = step.coreAfter :=
          congrArg (fun state : ReservationState ↦ state.core)
            step.output_eq
        rw [afterCore] at mateUnmarked
        change step.coreAfter.marks[candidate.tensor.mate]? = some none
          at mateUnmarked
        rw [step.queueStep.after_eq] at mateUnmarked
        exact mateUnmarked }
    have olderCreated :
        step.prepared.after.core.representative rawAge <
          step.prepared.after.core.representative
            step.prepared.stackResult.rawAge := by
      rw [← candidateAge]
      exact olderMiddle
    simpa [created] using
      step.created_rawMarksSeparatedFrom_of_retained retained created
        rawAge vertex middleMarked olderCreated

end SequentialFigure7

end ProofNetIR
