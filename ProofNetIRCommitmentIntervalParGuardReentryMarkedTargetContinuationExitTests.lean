/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7CommitmentIntervalParGuardReentryMarkedTargetContinuationExit

/-!
# Consumer for marked re-entry target continuation exits

The consumer destructs every terminal receipt, invokes the generic finite
normalizer and both typed wrappers, and audits their kernel axioms.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerBridge
open SequentialSchedulerState

private theorem observeContinuationExitTarget
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {owned : List Vertex}
    {current : ConnectiveBelow certificate input.vertex}
    (target :
      ActiveCarrierExternalReentryMarkedMateSeparatedContinuationExitTarget
        tagHistory input component owned current) :
    ActiveCarrierExternalReentryMarkedMateSeparatedContinuationExitTarget
      tagHistory input component owned current := by
  rcases target with
    ⟨path, directed, markedAge, pathStarts, finishOwned, directedMembership,
      parentEdge, targetNeSelected, targetNeMate, targetMarked, authentic,
      representativeEq, targetConsumer, targetConsumerMateNeSelected,
      sourceConsumer, targetConclusionOutside, raw | future | global⟩
  · rcases raw with
      ⟨terminal, chain, terminalConsumer, mateUnmarked,
        mateOutside | returned⟩
    · exact ⟨path, directed, markedAge, pathStarts, finishOwned,
        directedMembership, parentEdge, targetNeSelected, targetNeMate,
        targetMarked, authentic, representativeEq, targetConsumer,
        targetConsumerMateNeSelected, sourceConsumer, targetConclusionOutside,
        Or.inl ⟨terminal, chain, terminalConsumer, mateUnmarked,
          Or.inl mateOutside⟩⟩
    · rcases returned with
        ⟨mateSelected, terminalEq, conclusionEq, complexityLt⟩
      exact ⟨path, directed, markedAge, pathStarts, finishOwned,
        directedMembership, parentEdge, targetNeSelected, targetNeMate,
        targetMarked, authentic, representativeEq, targetConsumer,
        targetConsumerMateNeSelected, sourceConsumer, targetConclusionOutside,
        Or.inl ⟨terminal, chain, terminalConsumer, mateUnmarked,
          Or.inr ⟨mateSelected, terminalEq, conclusionEq, complexityLt⟩⟩⟩
  · rcases future with
      ⟨terminal, chain, terminalConsumer, boundary, work, conclusionOutside,
        older⟩
    exact ⟨path, directed, markedAge, pathStarts, finishOwned,
      directedMembership, parentEdge, targetNeSelected, targetNeMate,
      targetMarked, authentic, representativeEq, targetConsumer,
      targetConsumerMateNeSelected, sourceConsumer, targetConclusionOutside,
      Or.inr (Or.inl ⟨terminal, chain, terminalConsumer, boundary, work,
        conclusionOutside, older⟩)⟩
  · rcases global with
      ⟨terminal, chain, terminalConsumer, conclusionAge, conclusionMarked,
        conclusionGlobal, conclusionOutside, older⟩
    exact ⟨path, directed, markedAge, pathStarts, finishOwned,
      directedMembership, parentEdge, targetNeSelected, targetNeMate,
      targetMarked, authentic, representativeEq, targetConsumer,
      targetConsumerMateNeSelected, sourceConsumer, targetConclusionOutside,
      Or.inr (Or.inr ⟨terminal, chain, terminalConsumer, conclusionAge,
        conclusionMarked, conclusionGlobal, conclusionOutside, older⟩)⟩

private theorem useGeneric
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {usedLinks owned : List Nat}
    (invariant : SchedulerInvariant certificate state)
    (current : ConnectiveBelow certificate input.vertex)
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component
        usedLinks owned)
    (target :
      ActiveCarrierExternalReentryMarkedMateSeparatedTemporalTarget tagHistory
        input component owned current)
    (noTail :
      ¬ ∃ pending,
        pending ∈ input.readyTail ∧ pending ∉ certificate.conclusions) :
    ActiveCarrierExternalReentryMarkedMateSeparatedContinuationExitTarget
      tagHistory input component owned current := by
  exact observeContinuationExitTarget
    (target.continuationExitTarget invariant current componentLookup occurrence
      noTail)

private theorem useNop
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    (connected : certificate.ReferenceSwitchingConnected)
    (tagHistory : CanonicalTagHistory certificate history)
    (invariant : SchedulerInvariant certificate before)
    (step : NopStep certificate before after)
    {component : UnificationComponent} {usedLinks owned : List Nat}
    (componentLookup :
      before.core.components[step.prepared.stackResult.rawAge]? =
        some (some component))
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component
        usedLinks owned)
    {position edgeCount : Nat} {first : RawTokenAge}
    (positive : 0 < edgeCount)
    (firstAt : before.stack.sigma[position]? = some first)
    (lastAt :
      before.stack.sigma[position + edgeCount]? =
        some step.prepared.stackResult.rawAge)
    (noTail :
      ¬ ∃ pending,
        pending ∈ step.prepared.stackResult.remainingTop ∧
          pending ∉ certificate.conclusions) :
    tagHistory.CommitmentIntervalParTraceOutcome
      step.prepared.readyHeadInput step.consumer position edgeCount first
        (step.consumer.mate ∉ owned ∧
          before.core.marks[step.consumer.mate]? = some none ∧
          ActiveCarrierExternalReentryMarkedMateSeparatedContinuationExitTarget
            tagHistory step.prepared.readyHeadInput component owned
              step.consumer) := by
  exact
    step.commitmentInterval_parTraceReentryMarkedContinuationExitOutcome
      connected tagHistory invariant componentLookup occurrence positive
      firstAt lastAt noTail

private theorem useWait
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    (connected : certificate.ReferenceSwitchingConnected)
    (tagHistory : CanonicalTagHistory certificate history)
    (invariant : SchedulerInvariant certificate before)
    (step : WaitStep certificate before after)
    {component : UnificationComponent} {usedLinks owned : List Nat}
    (componentLookup :
      before.core.components[step.prepared.stackResult.rawAge]? =
        some (some component))
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component
        usedLinks owned)
    {position edgeCount : Nat} {first : RawTokenAge}
    (positive : 0 < edgeCount)
    (firstAt : before.stack.sigma[position]? = some first)
    (lastAt :
      before.stack.sigma[position + edgeCount]? =
        some step.prepared.stackResult.rawAge)
    (noTail :
      ¬ ∃ pending,
        pending ∈ step.prepared.stackResult.remainingTop ∧
          pending ∉ certificate.conclusions) :
    tagHistory.CommitmentIntervalParTraceOutcome
      step.prepared.readyHeadInput step.consumer position edgeCount first
        (step.consumer.mate ∉ owned ∧
          before.core.marks[step.consumer.mate]? =
            some (some step.mateRawAge) ∧
          before.core.representative step.mateRawAge <
            step.prepared.stackResult.rawAge ∧
          ActiveCarrierExternalReentryMarkedMateSeparatedContinuationExitTarget
            tagHistory step.prepared.readyHeadInput component owned
              step.consumer) := by
  exact
    step.commitmentInterval_parTraceReentryMarkedContinuationExitOutcome
      connected tagHistory invariant componentLookup occurrence positive
      firstAt lastAt noTail

#print axioms
  ActiveCarrierExternalReentryMarkedMateSeparatedTemporalTarget.continuationExitTarget
#print axioms
  NopStep.commitmentInterval_parTraceReentryMarkedContinuationExitOutcome
#print axioms
  WaitStep.commitmentInterval_parTraceReentryMarkedContinuationExitOutcome

end SequentialFigure7
end ProofNetIR

def main : IO Unit :=
  IO.println "Figure-7 marked re-entry continuation exit: kernel-green"
