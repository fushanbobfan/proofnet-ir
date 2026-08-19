/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7ActiveTopMarkedNonconclusionDebt

/-!
# Active-top debt production consumer

This executable import consumer applies every public theorem from the
branch-local debt module and audits their kernel axiom dependencies.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge
open ProofNetIR.SequentialFigure7.SchedulerInvariant

private theorem Consumer.emptyDebt (certificate : Certificate) :
    ActiveTopMarkedNonconclusionDebt certificate
      (ReservationState.empty certificate) :=
  empty_activeTopMarkedNonconclusionDebt certificate

private theorem Consumer.initialDebt
    {certificate : Certificate} {after : ReservationState} {start : Vertex}
    (step : InitialReservationStep certificate after start) :
    ActiveTopMarkedNonconclusionDebt certificate after :=
  InitialReservationStep.activeTopMarkedNonconclusionDebt step

private theorem Consumer.newDebt
    {certificate : Certificate} {before after : ReservationState}
    (step : NewStep certificate before after) :
    ActiveTopMarkedNonconclusionDebt certificate after :=
  NewStep.activeTopMarkedNonconclusionDebt step

private theorem Consumer.conclDebt
    {certificate : Certificate} {before after : ReservationState}
    (step : ConclStep certificate before after)
    (prior : ActiveTopMarkedNonconclusionDebt certificate before) :
    ActiveTopMarkedNonconclusionDebt certificate after :=
  ConclStep.activeTopMarkedNonconclusionDebt step prior

private theorem Consumer.forwardNonglobalDebt
    {certificate : Certificate} {before after : ReservationState}
    (step : ForwardStep certificate before after)
    (invariant : SchedulerInvariant certificate before)
    (notConclusion :
      step.consumer.conclusion ∉ certificate.conclusions) :
    ActiveTopMarkedNonconclusionDebt certificate after :=
  ForwardStep.activeTopMarkedNonconclusionDebt_of_created_not_conclusion
    step invariant notConclusion

private theorem Consumer.unifyPayloadNonglobalDebt
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after)
    (invariant : SchedulerInvariant certificate before)
    (notConclusion :
      step.consumer.conclusion ∉ certificate.conclusions) :
    ActiveTopMarkedNonconclusionDebt certificate after :=
  UnifyPayloadStep.activeTopMarkedNonconclusionDebt_of_created_not_conclusion
    step invariant notConclusion

private theorem Consumer.drainedAllMarked
    {certificate : Certificate} {state : ReservationState}
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate state)
    (drained : ActiveTopDrained state)
    (debt : ActiveTopMarkedNonconclusionDebt certificate state) :
    state.core.allMarked = true :=
  allMarked_of_activeTopDrained_of_nonconclusionDebt
    correct invariant drained debt

#print axioms empty_activeTopMarkedNonconclusionDebt
#print axioms InitialReservationStep.activeTopMarkedNonconclusionDebt
#print axioms NewStep.activeTopMarkedNonconclusionDebt
#print axioms ConclStep.activeTopMarkedNonconclusionDebt
#print axioms ForwardStep.activeTopMarkedNonconclusionDebt_of_created_not_conclusion
#print axioms UnifyPayloadStep.activeTopMarkedNonconclusionDebt_of_created_not_conclusion
#print axioms SchedulerInvariant.allMarked_of_activeTopDrained_of_nonconclusionDebt

end SequentialFigure7
end ProofNetIR

def main : IO Unit :=
  IO.println "active-top debt production consumer: kernel-green"
