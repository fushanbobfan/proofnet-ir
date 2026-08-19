/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7ActiveTopDebtBranchResidual

/-!
# Active-top debt branch-residual consumer

This executable consumer applies both directions of every public exact-boundary
theorem and destructures each returned branch witness. It also audits the
kernel axiom dependencies of the five public theorems.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge

private theorem Consumer.presentRoundTrip
    {certificate : Certificate} {state : ReservationState}
    (present : ActiveTopMarkedNonconclusionPresent certificate state) :
    ActiveTopMarkedNonconclusionPresent certificate state := by
  rcases present with
    ⟨rawAge, markedAge, component, markedVertex, sigmaTop,
      componentLookup, markedFrontier, marked, markedNotConclusion⟩
  exact ⟨rawAge, markedAge, component, markedVertex, sigmaTop,
    componentLookup, markedFrontier, marked, markedNotConclusion⟩

private theorem Consumer.preparedBoth
    {certificate : Certificate} {before : ReservationState}
    (step : PreparedStep before)
    (prior : ActiveTopMarkedNonconclusionDebt certificate before) :
    (step.SelectedAwayRawNonconclusionWitness certificate →
      ActiveTopMarkedNonconclusionDebt certificate step.after) ∧
      (ActiveTopMarkedNonconclusionDebt certificate step.after →
        step.SelectedAwayRawNonconclusionWitness certificate) := by
  have boundary :=
    step.activeTopMarkedNonconclusionDebt_iff_selectedAway prior
  constructor
  · intro selectedAway
    exact boundary.mpr selectedAway
  · intro afterDebt
    have selectedAway :
        step.SelectedAwayRawNonconclusionWitness certificate :=
      boundary.mp afterDebt
    intro component componentLookup selectedFrontier selectedNotConclusion
    rcases selectedAway componentLookup selectedFrontier selectedNotConclusion with
      ⟨pending, pendingFrontier, pendingNotConclusion, pendingDifferent,
        pendingUnmarked⟩
    exact ⟨pending, pendingFrontier, pendingNotConclusion,
      pendingDifferent, pendingUnmarked⟩

private theorem Consumer.nopBoth
    {certificate : Certificate} {before after : ReservationState}
    (step : NopStep certificate before after)
    (prior : ActiveTopMarkedNonconclusionDebt certificate before) :
    (step.prepared.SelectedAwayRawNonconclusionWitness certificate →
      ActiveTopMarkedNonconclusionDebt certificate after) ∧
      (ActiveTopMarkedNonconclusionDebt certificate after →
        step.prepared.SelectedAwayRawNonconclusionWitness certificate) := by
  have boundary :=
    step.activeTopMarkedNonconclusionDebt_iff_selectedAway prior
  constructor
  · intro selectedAway
    exact boundary.mpr selectedAway
  · intro afterDebt
    have selectedAway :
        step.prepared.SelectedAwayRawNonconclusionWitness certificate :=
      boundary.mp afterDebt
    intro component componentLookup selectedFrontier selectedNotConclusion
    rcases selectedAway componentLookup selectedFrontier selectedNotConclusion with
      ⟨pending, pendingFrontier, pendingNotConclusion, pendingDifferent,
        pendingUnmarked⟩
    exact ⟨pending, pendingFrontier, pendingNotConclusion,
      pendingDifferent, pendingUnmarked⟩

private theorem Consumer.waitBoth
    {certificate : Certificate} {before after : ReservationState}
    (step : WaitStep certificate before after)
    (prior : ActiveTopMarkedNonconclusionDebt certificate before) :
    (step.prepared.SelectedAwayRawNonconclusionWitness certificate →
      ActiveTopMarkedNonconclusionDebt certificate after) ∧
      (ActiveTopMarkedNonconclusionDebt certificate after →
        step.prepared.SelectedAwayRawNonconclusionWitness certificate) := by
  have boundary :=
    step.activeTopMarkedNonconclusionDebt_iff_selectedAway prior
  constructor
  · intro selectedAway
    exact boundary.mpr selectedAway
  · intro afterDebt
    have selectedAway :
        step.prepared.SelectedAwayRawNonconclusionWitness certificate :=
      boundary.mp afterDebt
    intro component componentLookup selectedFrontier selectedNotConclusion
    rcases selectedAway componentLookup selectedFrontier selectedNotConclusion with
      ⟨pending, pendingFrontier, pendingNotConclusion, pendingDifferent,
        pendingUnmarked⟩
    exact ⟨pending, pendingFrontier, pendingNotConclusion,
      pendingDifferent, pendingUnmarked⟩

private theorem Consumer.forwardGlobalBoth
    {certificate : Certificate} {before after : ReservationState}
    (step : ForwardStep certificate before after)
    (invariant : SchedulerInvariant certificate before)
    (createdConclusion :
      step.consumer.conclusion ∈ certificate.conclusions) :
    ((ActiveTopMarkedNonconclusionPresent certificate after →
        ∃ pending, pending ∈ step.prependStep.activeReady ∧
          pending ∉ certificate.conclusions) →
      ActiveTopMarkedNonconclusionDebt certificate after) ∧
      (ActiveTopMarkedNonconclusionDebt certificate after →
        ActiveTopMarkedNonconclusionPresent certificate after →
          ∃ pending, pending ∈ step.prependStep.activeReady ∧
            pending ∉ certificate.conclusions) := by
  have boundary :=
    step.activeTopMarkedNonconclusionDebt_iff_tailLaw_of_created_conclusion
      invariant createdConclusion
  constructor
  · intro tailLaw
    exact boundary.mpr tailLaw
  · intro afterDebt present
    have tailLaw := boundary.mp afterDebt
    rcases tailLaw present with ⟨pending, pendingTail, pendingNotConclusion⟩
    exact ⟨pending, pendingTail, pendingNotConclusion⟩

private theorem Consumer.unifyPayloadGlobalBoth
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after)
    (invariant : SchedulerInvariant certificate before)
    (createdConclusion :
      step.consumer.conclusion ∈ certificate.conclusions) :
    ((ActiveTopMarkedNonconclusionPresent certificate after →
        ∃ pending,
          pending ∈
              step.mergeStep.payload ++ step.mergeStep.previousReady ++
                step.mergeStep.activeReady ∧
            pending ∉ certificate.conclusions) →
      ActiveTopMarkedNonconclusionDebt certificate after) ∧
      (ActiveTopMarkedNonconclusionDebt certificate after →
        ActiveTopMarkedNonconclusionPresent certificate after →
          ∃ pending,
            pending ∈
                step.mergeStep.payload ++ step.mergeStep.previousReady ++
                  step.mergeStep.activeReady ∧
              pending ∉ certificate.conclusions) := by
  have boundary :=
    step.activeTopMarkedNonconclusionDebt_iff_tailLaw_of_created_conclusion
      invariant createdConclusion
  constructor
  · intro tailLaw
    exact boundary.mpr tailLaw
  · intro afterDebt present
    have tailLaw := boundary.mp afterDebt
    rcases tailLaw present with ⟨pending, pendingTail, pendingNotConclusion⟩
    exact ⟨pending, pendingTail, pendingNotConclusion⟩

#print axioms PreparedStep.activeTopMarkedNonconclusionDebt_iff_selectedAway
#print axioms NopStep.activeTopMarkedNonconclusionDebt_iff_selectedAway
#print axioms WaitStep.activeTopMarkedNonconclusionDebt_iff_selectedAway
#print axioms ForwardStep.activeTopMarkedNonconclusionDebt_iff_tailLaw_of_created_conclusion
#print axioms UnifyPayloadStep.activeTopMarkedNonconclusionDebt_iff_tailLaw_of_created_conclusion

end SequentialFigure7
end ProofNetIR

def main : IO Unit :=
  IO.println "active-top debt branch-residual consumer: kernel-green"
