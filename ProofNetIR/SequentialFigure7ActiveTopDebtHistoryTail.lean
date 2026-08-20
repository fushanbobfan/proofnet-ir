/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7ActiveTopDebtQueueTail
import ProofNetIR.SequentialFigure7TagHistory

/-!
# Active-top debt history-tail law

A reset-aware canonical-history carrier states the exact remaining queue-tail
obligations for `nop` and `wait`, together with the existing created-head tail
obligations for `forward` and `unifyPayload`. The carrier implies active-top
marked-nonconclusion debt at its endpoint.

This module does not derive the carrier from correctness, canonical history,
reachability, or progress. That history-level queue-ordering theorem remains
the open proof obligation.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge

namespace CanonicalTagHistory

/-- Reset-aware active-top debt law expressed by exact ready-tail obligations.
`concl` recurses. `nop` and `wait` require the current non-global
`remainingTop` witness and recurse. `new` resets to `True`. `forward` and
`unifyPayload` stop recursion and retain only their exact current created-head
alternative. -/
def ActiveTopDebtTailLaw
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state} :
    CanonicalTagHistory certificate history → Prop
  | .empty => True
  | .init _step => True
  | .later prior evidence =>
      match evidence with
      | .concl _ => prior.ActiveTopDebtTailLaw
      | .nop step =>
          (∃ pending,
            pending ∈ step.prepared.stackResult.remainingTop ∧
              pending ∉ certificate.conclusions) ∧
            prior.ActiveTopDebtTailLaw
      | .new _ => True
      | .wait step =>
          (∃ pending,
            pending ∈ step.prepared.stackResult.remainingTop ∧
              pending ∉ certificate.conclusions) ∧
            prior.ActiveTopDebtTailLaw
      | @DispatchTagEvidence.forward _ _ after step =>
          step.consumer.conclusion ∉ certificate.conclusions ∨
            (ActiveTopMarkedNonconclusionPresent certificate after →
              ∃ pending,
                pending ∈ step.prependStep.activeReady ∧
                  pending ∉ certificate.conclusions)
      | @DispatchTagEvidence.unifyPayload _ _ after step =>
          step.consumer.conclusion ∉ certificate.conclusions ∨
            (ActiveTopMarkedNonconclusionPresent certificate after →
              ∃ pending,
                pending ∈
                    step.mergeStep.payload ++ step.mergeStep.previousReady ++
                      step.mergeStep.activeReady ∧
                  pending ∉ certificate.conclusions)

/-- The exact reset-aware history-tail law suffices for active-top
marked-nonconclusion debt at the history endpoint. -/
theorem activeTopMarkedNonconclusionDebt_of_tailLaw
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (law : tagHistory.ActiveTopDebtTailLaw) :
    ActiveTopMarkedNonconclusionDebt certificate state := by
  induction tagHistory with
  | empty =>
      exact empty_activeTopMarkedNonconclusionDebt certificate
  | init step =>
      exact InitialReservationStep.activeTopMarkedNonconclusionDebt step
  | @later before result history invariant dispatch prior evidence induction =>
      cases evidence with
      | concl step =>
          change prior.ActiveTopDebtTailLaw at law
          exact step.activeTopMarkedNonconclusionDebt (induction law)
      | nop step =>
          change
            (∃ pending,
              pending ∈ step.prepared.stackResult.remainingTop ∧
                pending ∉ certificate.conclusions) ∧
              prior.ActiveTopDebtTailLaw at law
          exact
            (step.activeTopMarkedNonconclusionDebt_iff_readyTailNonconclusion
              invariant (induction law.2)).mpr law.1
      | new step =>
          exact step.activeTopMarkedNonconclusionDebt
      | wait step =>
          change
            (∃ pending,
              pending ∈ step.prepared.stackResult.remainingTop ∧
                pending ∉ certificate.conclusions) ∧
              prior.ActiveTopDebtTailLaw at law
          exact
            (step.activeTopMarkedNonconclusionDebt_iff_readyTailNonconclusion
              invariant (induction law.2)).mpr law.1
      | @forward after step =>
          change
            step.consumer.conclusion ∉ certificate.conclusions ∨
              (ActiveTopMarkedNonconclusionPresent certificate after →
                ∃ pending,
                  pending ∈ step.prependStep.activeReady ∧
                    pending ∉ certificate.conclusions) at law
          rcases law with notGlobal | tailLaw
          · exact
              step.activeTopMarkedNonconclusionDebt_of_created_not_conclusion
                invariant notGlobal
          · by_cases global : step.consumer.conclusion ∈ certificate.conclusions
            · exact
                (step.activeTopMarkedNonconclusionDebt_iff_tailLaw_of_created_conclusion
                  invariant global).mpr tailLaw
            · exact
                step.activeTopMarkedNonconclusionDebt_of_created_not_conclusion
                  invariant global
      | @unifyPayload after step =>
          change
            step.consumer.conclusion ∉ certificate.conclusions ∨
              (ActiveTopMarkedNonconclusionPresent certificate after →
                ∃ pending,
                  pending ∈
                      step.mergeStep.payload ++ step.mergeStep.previousReady ++
                        step.mergeStep.activeReady ∧
                    pending ∉ certificate.conclusions) at law
          rcases law with notGlobal | tailLaw
          · exact
              step.activeTopMarkedNonconclusionDebt_of_created_not_conclusion
                invariant notGlobal
          · by_cases global : step.consumer.conclusion ∈ certificate.conclusions
            · exact
                (step.activeTopMarkedNonconclusionDebt_iff_tailLaw_of_created_conclusion
                  invariant global).mpr tailLaw
            · exact
                step.activeTopMarkedNonconclusionDebt_of_created_not_conclusion
                  invariant global

end CanonicalTagHistory
end SequentialFigure7
end ProofNetIR
