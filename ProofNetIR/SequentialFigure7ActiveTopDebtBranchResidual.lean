/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7ActiveTopMarkedNonconclusionDebt

/-!
# Active-top debt branch residuals

Exact branch-local residuals for the common prepared prefix, `nop`, `wait`,
and the global-created `forward` and `unifyPayload` branches.

These results isolate the remaining witness obligation at each branch. They do
not establish unconditional debt preservation, a canonical-history carrier,
progress, totality, or completeness of the scheduler.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge

/-- The exact extra witness needed when the common prefix marks its selected
non-conclusion: another raw-unmarked non-conclusion remains on that component's
frontier. -/
def PreparedStep.SelectedAwayRawNonconclusionWitness
    (certificate : Certificate) {before : ReservationState}
    (step : PreparedStep before) : Prop :=
  ∀ {component : UnificationComponent},
    before.core.components[step.stackResult.rawAge]? = some (some component) →
      step.stackResult.vertex ∈ component.frontier →
        step.stackResult.vertex ∉ certificate.conclusions →
          ∃ pending,
            pending ∈ component.frontier ∧
              pending ∉ certificate.conclusions ∧
                pending ≠ step.stackResult.vertex ∧
                  before.core.marks[pending]? = some none

private theorem PreparedStep.activeTopMarkedNonconclusionDebt_of_selectedAway
    {certificate : Certificate} {before : ReservationState}
    (step : PreparedStep before)
    (prior : ActiveTopMarkedNonconclusionDebt certificate before)
    (selectedAway :
      step.SelectedAwayRawNonconclusionWitness certificate) :
    ActiveTopMarkedNonconclusionDebt certificate step.after := by
  rcases SequentialStackState.popReadyMark?_exact step.stack_eq with
    ⟨_topReady, beforeSigmaTop, _selectedUnmarked, _stackMarks,
      _nextAge, sigmaEq, _ready, _waiting, _stackSelectedMarked⟩
  rcases UnificationState.markReadyRaw?_exact step.core_mark_eq with
    ⟨_coreSelectedUnmarked, marksEq, _parents, componentsEq,
      _started, _fired, _coreSelectedMarked⟩
  intro rawAge markedAge component markedVertex sigmaTop componentLookup
    markedFrontier marked notConclusion
  change step.stackResult.after.sigma.getLast? = some rawAge at sigmaTop
  rw [sigmaEq] at sigmaTop
  have rawAgeEq : rawAge = step.stackResult.rawAge :=
    Option.some.inj (sigmaTop.symm.trans beforeSigmaTop)
  subst rawAge
  change step.coreMarked.components[step.stackResult.rawAge]? =
    some (some component) at componentLookup
  rw [componentsEq] at componentLookup
  change step.coreMarked.marks[markedVertex]? = some (some markedAge) at marked
  rw [marksEq] at marked
  by_cases markedSelected : markedVertex = step.stackResult.vertex
  · subst markedVertex
    rcases selectedAway componentLookup markedFrontier notConclusion with
      ⟨pending, pendingFrontier, pendingNotConclusion, pendingDifferent,
        pendingUnmarked⟩
    refine ⟨pending, pendingFrontier, pendingNotConclusion, ?_⟩
    change step.coreMarked.marks[pending]? = some none
    rw [marksEq]
    simpa [Array.getElem?_setIfInBounds, Ne.symm pendingDifferent] using
      pendingUnmarked
  · have beforeMarked :
        before.core.marks[markedVertex]? = some (some markedAge) := by
      simpa [Array.getElem?_setIfInBounds, Ne.symm markedSelected] using marked
    rcases prior beforeSigmaTop componentLookup markedFrontier beforeMarked
        notConclusion with
      ⟨pending, pendingFrontier, pendingNotConclusion, pendingUnmarked⟩
    by_cases pendingSelected : pending = step.stackResult.vertex
    · subst pending
      rcases selectedAway componentLookup pendingFrontier pendingNotConclusion with
        ⟨replacement, replacementFrontier, replacementNotConclusion,
          replacementDifferent, replacementUnmarked⟩
      refine ⟨replacement, replacementFrontier, replacementNotConclusion, ?_⟩
      change step.coreMarked.marks[replacement]? = some none
      rw [marksEq]
      simpa [Array.getElem?_setIfInBounds, Ne.symm replacementDifferent] using
        replacementUnmarked
    · refine ⟨pending, pendingFrontier, pendingNotConclusion, ?_⟩
      change step.coreMarked.marks[pending]? = some none
      rw [marksEq]
      simpa [Array.getElem?_setIfInBounds, Ne.symm pendingSelected] using
        pendingUnmarked

private theorem PreparedStep.selectedAway_of_activeTopMarkedNonconclusionDebt
    {certificate : Certificate} {before : ReservationState}
    (step : PreparedStep before)
    (afterDebt :
      ActiveTopMarkedNonconclusionDebt certificate step.after) :
    step.SelectedAwayRawNonconclusionWitness certificate := by
  rcases SequentialStackState.popReadyMark?_exact step.stack_eq with
    ⟨_topReady, beforeSigmaTop, _selectedUnmarked, _stackMarks,
      _nextAge, sigmaEq, _ready, _waiting, _stackSelectedMarked⟩
  rcases UnificationState.markReadyRaw?_exact step.core_mark_eq with
    ⟨_coreSelectedUnmarked, marksEq, _parents, componentsEq,
      _started, _fired, coreSelectedMarked⟩
  intro component componentLookup selectedFrontier selectedNotConclusion
  have afterSigmaTop :
      step.after.stack.sigma.getLast? = some step.stackResult.rawAge := by
    change step.stackResult.after.sigma.getLast? = some step.stackResult.rawAge
    rw [sigmaEq]
    exact beforeSigmaTop
  have afterComponentLookup :
      step.after.core.components[step.stackResult.rawAge]? =
        some (some component) := by
    change step.coreMarked.components[step.stackResult.rawAge]? =
      some (some component)
    rw [componentsEq]
    exact componentLookup
  have afterSelectedMarked :
      step.after.core.marks[step.stackResult.vertex]? =
        some (some step.stackResult.rawAge) := coreSelectedMarked
  rcases afterDebt afterSigmaTop afterComponentLookup selectedFrontier
      afterSelectedMarked selectedNotConclusion with
    ⟨pending, pendingFrontier, pendingNotConclusion, pendingUnmarkedAfter⟩
  have pendingDifferent : pending ≠ step.stackResult.vertex := by
    intro same
    subst pending
    rw [afterSelectedMarked] at pendingUnmarkedAfter
    simp at pendingUnmarkedAfter
  have pendingUnmarkedBefore :
      before.core.marks[pending]? = some none := by
    change step.coreMarked.marks[pending]? = some none at pendingUnmarkedAfter
    rw [marksEq] at pendingUnmarkedAfter
    simpa [Array.getElem?_setIfInBounds, Ne.symm pendingDifferent] using
      pendingUnmarkedAfter
  exact ⟨pending, pendingFrontier, pendingNotConclusion,
    pendingDifferent, pendingUnmarkedBefore⟩

/-- With prior debt fixed, debt after the common prefix is exactly equivalent
to the selected-away raw witness. -/
theorem PreparedStep.activeTopMarkedNonconclusionDebt_iff_selectedAway
    {certificate : Certificate} {before : ReservationState}
    (step : PreparedStep before)
    (prior : ActiveTopMarkedNonconclusionDebt certificate before) :
    ActiveTopMarkedNonconclusionDebt certificate step.after ↔
      step.SelectedAwayRawNonconclusionWitness certificate :=
  ⟨step.selectedAway_of_activeTopMarkedNonconclusionDebt,
    step.activeTopMarkedNonconclusionDebt_of_selectedAway prior⟩

private theorem NopStep.activeTopMarkedNonconclusionDebt_of_selectedAway
    {certificate : Certificate} {before after : ReservationState}
    (step : NopStep certificate before after)
    (prior : ActiveTopMarkedNonconclusionDebt certificate before)
    (selectedAway :
      step.prepared.SelectedAwayRawNonconclusionWitness certificate) :
    ActiveTopMarkedNonconclusionDebt certificate after := by
  rw [step.output_eq]
  exact step.prepared.activeTopMarkedNonconclusionDebt_of_selectedAway
    prior selectedAway

/-- Under prior debt, post-`nop` debt is exactly equivalent to the common
prefix's selected-away raw witness. -/
theorem NopStep.activeTopMarkedNonconclusionDebt_iff_selectedAway
    {certificate : Certificate} {before after : ReservationState}
    (step : NopStep certificate before after)
    (prior : ActiveTopMarkedNonconclusionDebt certificate before) :
    ActiveTopMarkedNonconclusionDebt certificate after ↔
      step.prepared.SelectedAwayRawNonconclusionWitness certificate := by
  constructor
  · intro afterDebt
    have sigmaEq :
        after.stack.sigma = step.prepared.after.stack.sigma :=
      congrArg (fun state : ReservationState ↦ state.stack.sigma) step.output_eq
    have coreEq : after.core = step.prepared.after.core :=
      congrArg ReservationState.core step.output_eq
    have middleDebt :
        ActiveTopMarkedNonconclusionDebt certificate step.prepared.after := by
      intro rawAge markedAge component markedVertex sigmaTop componentLookup
        markedFrontier marked notConclusion
      rcases afterDebt (rawAge := rawAge) (markedAge := markedAge)
          (component := component) (markedVertex := markedVertex)
          (by simpa only [sigmaEq] using sigmaTop)
          (by simpa only [coreEq] using componentLookup)
          markedFrontier (by simpa only [coreEq] using marked) notConclusion with
        ⟨pending, pendingFrontier, pendingNotConclusion, pendingUnmarked⟩
      exact ⟨pending, pendingFrontier, pendingNotConclusion,
        by simpa only [coreEq] using pendingUnmarked⟩
    apply step.prepared.selectedAway_of_activeTopMarkedNonconclusionDebt
    exact middleDebt
  · exact step.activeTopMarkedNonconclusionDebt_of_selectedAway prior

private theorem WaitDestinationStep.activeTopMarkedNonconclusionDebt_iff
    {certificate : Certificate} {before after : ReservationState}
    {mateRawAge : RawTokenAge} {conclusion : Vertex}
    (step : WaitDestinationStep before after mateRawAge conclusion) :
    ActiveTopMarkedNonconclusionDebt certificate after ↔
      ActiveTopMarkedNonconclusionDebt certificate before := by
  rcases step.exact with
    ⟨_payload, _initialized, _updated, _stackMarks, _nextAge,
      sigmaEq, _ready, coreEq, _tags⟩
  constructor <;> intro debt rawAge markedAge component markedVertex
      sigmaTop componentLookup markedFrontier marked notConclusion
  · rcases debt (rawAge := rawAge) (markedAge := markedAge)
        (component := component) (markedVertex := markedVertex)
        (by simpa only [sigmaEq] using sigmaTop)
        (by simpa only [coreEq] using componentLookup)
        markedFrontier (by simpa only [coreEq] using marked) notConclusion with
      ⟨pending, pendingFrontier, pendingNotConclusion, pendingUnmarked⟩
    exact ⟨pending, pendingFrontier, pendingNotConclusion,
      by simpa only [coreEq] using pendingUnmarked⟩
  · rcases debt (rawAge := rawAge) (markedAge := markedAge)
        (component := component) (markedVertex := markedVertex)
        (by simpa only [sigmaEq] using sigmaTop)
        (by simpa only [coreEq] using componentLookup)
        markedFrontier (by simpa only [coreEq] using marked) notConclusion with
      ⟨pending, pendingFrontier, pendingNotConclusion, pendingUnmarked⟩
    exact ⟨pending, pendingFrontier, pendingNotConclusion,
      by simpa only [coreEq] using pendingUnmarked⟩

private theorem WaitStep.activeTopMarkedNonconclusionDebt_of_selectedAway
    {certificate : Certificate} {before after : ReservationState}
    (step : WaitStep certificate before after)
    (prior : ActiveTopMarkedNonconclusionDebt certificate before)
    (selectedAway :
      step.prepared.SelectedAwayRawNonconclusionWitness certificate) :
    ActiveTopMarkedNonconclusionDebt certificate after := by
  have middleDebt :
      ActiveTopMarkedNonconclusionDebt certificate step.prepared.after :=
    step.prepared.activeTopMarkedNonconclusionDebt_of_selectedAway
      prior selectedAway
  rcases step.destination.exact with
    ⟨_payload, _initialized, _updated, _stackMarks, _nextAge,
      sigmaEq, _ready, coreEq, _tags⟩
  intro rawAge markedAge component markedVertex sigmaTop componentLookup
    markedFrontier marked notConclusion
  rcases middleDebt (rawAge := rawAge) (markedAge := markedAge)
      (component := component) (markedVertex := markedVertex)
      (by simpa only [sigmaEq] using sigmaTop)
      (by simpa only [coreEq] using componentLookup)
      markedFrontier (by simpa only [coreEq] using marked) notConclusion with
    ⟨pending, pendingFrontier, pendingNotConclusion, pendingUnmarked⟩
  exact ⟨pending, pendingFrontier, pendingNotConclusion,
    by simpa only [coreEq] using pendingUnmarked⟩

/-- Under prior debt, post-`wait` debt is exactly equivalent to the common
prefix's selected-away raw witness. -/
theorem WaitStep.activeTopMarkedNonconclusionDebt_iff_selectedAway
    {certificate : Certificate} {before after : ReservationState}
    (step : WaitStep certificate before after)
    (prior : ActiveTopMarkedNonconclusionDebt certificate before) :
    ActiveTopMarkedNonconclusionDebt certificate after ↔
      step.prepared.SelectedAwayRawNonconclusionWitness certificate := by
  calc
    ActiveTopMarkedNonconclusionDebt certificate after ↔
        ActiveTopMarkedNonconclusionDebt certificate step.prepared.after :=
      WaitDestinationStep.activeTopMarkedNonconclusionDebt_iff step.destination
    _ ↔ step.prepared.SelectedAwayRawNonconclusionWitness certificate :=
      step.prepared.activeTopMarkedNonconclusionDebt_iff_selectedAway prior

/-- There is an actual marked non-conclusion on the active live frontier. -/
def ActiveTopMarkedNonconclusionPresent
    (certificate : Certificate) (state : ReservationState) : Prop :=
  ∃ rawAge markedAge component markedVertex,
    state.stack.sigma.getLast? = some rawAge ∧
      state.core.components[rawAge]? = some (some component) ∧
        markedVertex ∈ component.frontier ∧
          state.core.marks[markedVertex]? = some (some markedAge) ∧
            markedVertex ∉ certificate.conclusions

namespace ReadyHeadInput

private theorem activeTopMarkedNonconclusionDebt_of_tail
    {certificate : Certificate} {state : ReservationState}
    (input : ReadyHeadInput state)
    (invariant : SchedulerInvariant certificate state)
    (tailWitness :
      ∃ pending, pending ∈ input.readyTail ∧
        pending ∉ certificate.conclusions) :
    ActiveTopMarkedNonconclusionDebt certificate state := by
  rcases tailWitness with ⟨pending, pendingTail, pendingNotConclusion⟩
  rcases List.getLast?_eq_some_iff.mp input.top_ready with
    ⟨readyPrefix, readyEquation⟩
  rcases List.getLast?_eq_some_iff.mp input.sigma_top with
    ⟨sigmaPrefix, sigmaEquation⟩
  have prefixLengths : readyPrefix.length = sigmaPrefix.length := by
    have aligned := invariant.stack_wellShaped.ready_aligned
    rw [readyEquation, sigmaEquation] at aligned
    simp at aligned
    omega
  have sigmaLookup :
      state.stack.sigma[readyPrefix.length]? = some input.rawAge := by
    rw [sigmaEquation, prefixLengths]
    simp
  have readyLookup :
      state.stack.ready[readyPrefix.length]? =
        some (input.vertex :: input.readyTail) := by
    rw [readyEquation]
    simp
  rcases invariant.ready_bucket_frontier_exact sigmaLookup readyLookup with
    ⟨inputComponent, inputComponentLookup, inputExact⟩
  have pendingBucket : pending ∈ input.vertex :: input.readyTail :=
    List.mem_cons_of_mem input.vertex pendingTail
  have pendingExact := (inputExact pending).mp pendingBucket
  intro rawAge _markedAge component _markedVertex sigmaTop componentLookup
    _markedFrontier _marked _markedNotConclusion
  have rawAgeEq : rawAge = input.rawAge :=
    Option.some.inj (sigmaTop.symm.trans input.sigma_top)
  subst rawAge
  have componentEq : component = inputComponent :=
    Option.some.inj
      (Option.some.inj (componentLookup.symm.trans inputComponentLookup))
  subst component
  exact ⟨pending, pendingExact.1, pendingNotConclusion, pendingExact.2⟩

private theorem activeTopMarkedNonconclusionDebt_iff_tailLaw_of_vertex_conclusion
    {certificate : Certificate} {state : ReservationState}
    (input : ReadyHeadInput state)
    (invariant : SchedulerInvariant certificate state)
    (headConclusion : input.vertex ∈ certificate.conclusions) :
    ActiveTopMarkedNonconclusionDebt certificate state ↔
      (ActiveTopMarkedNonconclusionPresent certificate state →
        ∃ pending, pending ∈ input.readyTail ∧
          pending ∉ certificate.conclusions) := by
  constructor
  · intro debt present
    rcases present with
      ⟨rawAge, markedAge, component, markedVertex, sigmaTop,
        componentLookup, markedFrontier, marked, markedNotConclusion⟩
    rcases debt sigmaTop componentLookup markedFrontier marked
        markedNotConclusion with
      ⟨pending, pendingFrontier, pendingNotConclusion, pendingUnmarked⟩
    rcases List.getLast?_eq_some_iff.mp input.top_ready with
      ⟨readyPrefix, readyEquation⟩
    rcases List.getLast?_eq_some_iff.mp input.sigma_top with
      ⟨sigmaPrefix, sigmaEquation⟩
    have rawAgeEq : rawAge = input.rawAge :=
      Option.some.inj (sigmaTop.symm.trans input.sigma_top)
    subst rawAge
    have prefixLengths : readyPrefix.length = sigmaPrefix.length := by
      have aligned := invariant.stack_wellShaped.ready_aligned
      rw [readyEquation, sigmaEquation] at aligned
      simp at aligned
      omega
    have sigmaLookup :
        state.stack.sigma[readyPrefix.length]? = some input.rawAge := by
      rw [sigmaEquation, prefixLengths]
      simp
    have readyLookup :
        state.stack.ready[readyPrefix.length]? =
          some (input.vertex :: input.readyTail) := by
      rw [readyEquation]
      simp
    rcases invariant.ready_bucket_frontier_exact sigmaLookup readyLookup with
      ⟨inputComponent, inputComponentLookup, inputExact⟩
    have componentEq : component = inputComponent :=
      Option.some.inj
        (Option.some.inj (componentLookup.symm.trans inputComponentLookup))
    subst component
    have pendingBucket : pending ∈ input.vertex :: input.readyTail :=
      (inputExact pending).mpr ⟨pendingFrontier, pendingUnmarked⟩
    have pendingNeHead : pending ≠ input.vertex := by
      intro same
      apply pendingNotConclusion
      simpa [same] using headConclusion
    exact ⟨pending,
      (List.mem_cons.mp pendingBucket).resolve_left pendingNeHead,
      pendingNotConclusion⟩
  · intro tailLaw
    intro rawAge markedAge component markedVertex sigmaTop componentLookup
      markedFrontier marked markedNotConclusion
    have present :
        ActiveTopMarkedNonconclusionPresent certificate state :=
      ⟨rawAge, markedAge, component, markedVertex, sigmaTop,
        componentLookup, markedFrontier, marked, markedNotConclusion⟩
    have debt : ActiveTopMarkedNonconclusionDebt certificate state :=
      input.activeTopMarkedNonconclusionDebt_of_tail invariant
        (tailLaw present)
    exact debt sigmaTop componentLookup markedFrontier marked
      markedNotConclusion

end ReadyHeadInput

namespace ForwardStep

private def createdReadyHead
    {certificate : Certificate} {before after : ReservationState}
    (step : ForwardStep certificate before after) : ReadyHeadInput after where
  vertex := step.consumer.conclusion
  readyTail := step.prependStep.activeReady
  rawAge := step.prepared.stackResult.rawAge
  top_ready := by
    let activeReady := step.prependStep.activeReady
    have stackEq : after.stack = step.stackAfter :=
      congrArg ReservationState.stack step.output_eq
    have afterReady :
        step.stackAfter.ready =
          step.prependStep.readyPrefix ++
            [step.consumer.conclusion :: activeReady] := by
      have fields :=
        congrArg SequentialStackState.ready step.prependStep.after_eq
      simpa [activeReady] using fields
    change after.stack.ready.getLast? =
      some (step.consumer.conclusion :: activeReady)
    rw [stackEq, afterReady]
    simp
  sigma_top := by
    rcases SequentialStackState.popReadyMark?_exact step.prepared.stack_eq with
      ⟨_beforeReady, beforeSigma, _unmarked, _marks, _nextAge,
        sigmaEquation, _afterReady, _waiting, _selectedMarked⟩
    have stackEq : after.stack = step.stackAfter :=
      congrArg ReservationState.stack step.output_eq
    have afterSigma :
        step.stackAfter.sigma = step.prepared.stackResult.after.sigma := by
      have fields :=
        congrArg SequentialStackState.sigma step.prependStep.after_eq
      simpa using fields
    rw [stackEq, afterSigma, sigmaEquation]
    exact beforeSigma

/-- If a `forward` step creates a global ready head, post-debt is exactly the
conditional law requiring a non-global vertex in its preserved ready tail. -/
theorem activeTopMarkedNonconclusionDebt_iff_tailLaw_of_created_conclusion
    {certificate : Certificate} {before after : ReservationState}
    (step : ForwardStep certificate before after)
    (invariant : SchedulerInvariant certificate before)
    (createdConclusion :
      step.consumer.conclusion ∈ certificate.conclusions) :
    ActiveTopMarkedNonconclusionDebt certificate after ↔
      (ActiveTopMarkedNonconclusionPresent certificate after →
        ∃ pending, pending ∈ step.prependStep.activeReady ∧
          pending ∉ certificate.conclusions) := by
  exact step.createdReadyHead
    |>.activeTopMarkedNonconclusionDebt_iff_tailLaw_of_vertex_conclusion
      (step.schedulerInvariant invariant) createdConclusion

end ForwardStep

namespace UnifyPayloadStep

private def createdReadyHead
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after) : ReadyHeadInput after where
  vertex := step.consumer.conclusion
  readyTail :=
    step.mergeStep.payload ++ step.mergeStep.previousReady ++
      step.mergeStep.activeReady
  rawAge := step.previousBoundary
  top_ready := by
    let mergedTail :=
      step.mergeStep.payload ++ step.mergeStep.previousReady ++
        step.mergeStep.activeReady
    have stackEq : after.stack = step.stackAfter :=
      congrArg ReservationState.stack step.output_eq
    have afterReady :
        step.stackAfter.ready =
          step.mergeStep.readyPrefix ++
            [step.consumer.conclusion :: mergedTail] := by
      have fields :=
        congrArg SequentialStackState.ready step.mergeStep.after_eq
      simpa [mergedTail] using fields
    change after.stack.ready.getLast? =
      some (step.consumer.conclusion :: mergedTail)
    rw [stackEq, afterReady]
    simp
  sigma_top := by
    have stackEq : after.stack = step.stackAfter :=
      congrArg ReservationState.stack step.output_eq
    have afterSigma :
        step.stackAfter.sigma =
          step.mergeStep.sigmaPrefix ++ [step.previousBoundary] := by
      have fields :=
        congrArg SequentialStackState.sigma step.mergeStep.after_eq
      simpa using fields
    rw [stackEq, afterSigma]
    simp

/-- If an `unifyPayload` step creates a global ready head, post-debt is exactly
the conditional law requiring a non-global vertex in its merged ready tail. -/
theorem activeTopMarkedNonconclusionDebt_iff_tailLaw_of_created_conclusion
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after)
    (invariant : SchedulerInvariant certificate before)
    (createdConclusion :
      step.consumer.conclusion ∈ certificate.conclusions) :
    ActiveTopMarkedNonconclusionDebt certificate after ↔
      (ActiveTopMarkedNonconclusionPresent certificate after →
        ∃ pending,
          pending ∈
              step.mergeStep.payload ++ step.mergeStep.previousReady ++
                step.mergeStep.activeReady ∧
            pending ∉ certificate.conclusions) := by
  exact step.createdReadyHead
    |>.activeTopMarkedNonconclusionDebt_iff_tailLaw_of_vertex_conclusion
      (step.schedulerInvariant invariant) createdConclusion

end UnifyPayloadStep

end SequentialFigure7
end ProofNetIR
