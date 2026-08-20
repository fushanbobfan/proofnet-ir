/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7ActiveTopDebtHistoryTail

/-!
# Active-top debt history-tail consumer

This executable consumer applies both directions of the two public exact
queue-tail boundaries, unfolds every branch of the reset-aware history law,
and applies the endpoint-debt theorem.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge

private theorem Consumer.nopBoth
    {certificate : Certificate} {before after : ReservationState}
    (step : NopStep certificate before after)
    (invariant : SchedulerInvariant certificate before)
    (prior : ActiveTopMarkedNonconclusionDebt certificate before) :
    ((∃ pending,
        pending ∈ step.prepared.stackResult.remainingTop ∧
          pending ∉ certificate.conclusions) →
      ActiveTopMarkedNonconclusionDebt certificate after) ∧
      (ActiveTopMarkedNonconclusionDebt certificate after →
        ∃ pending,
          pending ∈ step.prepared.stackResult.remainingTop ∧
            pending ∉ certificate.conclusions) := by
  have boundary :=
    step.activeTopMarkedNonconclusionDebt_iff_readyTailNonconclusion invariant prior
  constructor
  · rintro ⟨pending, pendingTail, pendingNotConclusion⟩
    exact boundary.mpr ⟨pending, pendingTail, pendingNotConclusion⟩
  · intro afterDebt
    rcases boundary.mp afterDebt with
      ⟨pending, pendingTail, pendingNotConclusion⟩
    exact ⟨pending, pendingTail, pendingNotConclusion⟩

private theorem Consumer.waitBoth
    {certificate : Certificate} {before after : ReservationState}
    (step : WaitStep certificate before after)
    (invariant : SchedulerInvariant certificate before)
    (prior : ActiveTopMarkedNonconclusionDebt certificate before) :
    ((∃ pending,
        pending ∈ step.prepared.stackResult.remainingTop ∧
          pending ∉ certificate.conclusions) →
      ActiveTopMarkedNonconclusionDebt certificate after) ∧
      (ActiveTopMarkedNonconclusionDebt certificate after →
        ∃ pending,
          pending ∈ step.prepared.stackResult.remainingTop ∧
            pending ∉ certificate.conclusions) := by
  have boundary :=
    step.activeTopMarkedNonconclusionDebt_iff_readyTailNonconclusion invariant prior
  constructor
  · rintro ⟨pending, pendingTail, pendingNotConclusion⟩
    exact boundary.mpr ⟨pending, pendingTail, pendingNotConclusion⟩
  · intro afterDebt
    rcases boundary.mp afterDebt with
      ⟨pending, pendingTail, pendingNotConclusion⟩
    exact ⟨pending, pendingTail, pendingNotConclusion⟩

private theorem Consumer.tailLawAllBranches
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (law : tagHistory.ActiveTopDebtTailLaw) : True := by
  cases tagHistory with
  | empty => exact law
  | init _step => exact law
  | later prior evidence =>
      cases evidence with
      | concl _step =>
          change prior.ActiveTopDebtTailLaw at law
          exact True.intro
      | nop step =>
          change
            (∃ pending,
              pending ∈ step.prepared.stackResult.remainingTop ∧
                pending ∉ certificate.conclusions) ∧
              prior.ActiveTopDebtTailLaw at law
          rcases law.1 with ⟨_pending, _pendingTail, _pendingNotConclusion⟩
          exact True.intro
      | new _step => exact law
      | wait step =>
          change
            (∃ pending,
              pending ∈ step.prepared.stackResult.remainingTop ∧
                pending ∉ certificate.conclusions) ∧
              prior.ActiveTopDebtTailLaw at law
          rcases law.1 with ⟨_pending, _pendingTail, _pendingNotConclusion⟩
          exact True.intro
      | forward _step =>
          rcases law with _notGlobal | _tailLaw <;> exact True.intro
      | unifyPayload _step =>
          rcases law with _notGlobal | _tailLaw <;> exact True.intro

private theorem Consumer.endpointDebt
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (law : tagHistory.ActiveTopDebtTailLaw) :
    ActiveTopMarkedNonconclusionDebt certificate state := by
  exact tagHistory.activeTopMarkedNonconclusionDebt_of_tailLaw law

#print axioms NopStep.activeTopMarkedNonconclusionDebt_iff_readyTailNonconclusion
#print axioms WaitStep.activeTopMarkedNonconclusionDebt_iff_readyTailNonconclusion
#print axioms CanonicalTagHistory.ActiveTopDebtTailLaw
#print axioms CanonicalTagHistory.activeTopMarkedNonconclusionDebt_of_tailLaw

end SequentialFigure7
end ProofNetIR

def main : IO Unit :=
  IO.println "active-top debt history-tail consumer: kernel-green"
