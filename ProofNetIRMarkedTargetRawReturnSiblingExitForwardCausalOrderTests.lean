/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7MarkedTargetRawReturnSiblingExitForwardCausalOrder

/-!
# Figure-7 sibling-exit forward-causal consumer

This consumer re-roots a sibling continuation after its marked shared parent,
observes all three forward-causal endpoint cases, strengthens the full target,
and invokes the typed Wait theorem.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerBridge

private theorem Consumer.afterMarkedSibling
    {certificate : Certificate} {state : ReservationState}
    (structural : certificate.StructurallyWellFormed)
    (queuedUnmarked : QueuedVerticesUnmarked state)
    {origin : Vertex} (consumer : ConnectiveBelow certificate origin)
    {originAge conclusionAge : RawTokenAge}
    (originMarked : state.core.marks[origin]? = some (some originAge))
    (conclusionMarked :
      state.core.marks[consumer.conclusion]? = some (some conclusionAge))
    (conclusionNotGlobal : consumer.conclusion ∉ certificate.conclusions)
    (exit : ContinuationExit certificate state consumer.mate) :
    ContinuationExit certificate state consumer.conclusion := by
  exact exit.afterMarkedSibling structural queuedUnmarked consumer originMarked
    conclusionMarked conclusionNotGlobal

private inductive ForwardOutcomeObserved
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (origin outer : Vertex) (outerAge : RawTokenAge) : Prop where
  | rawMate {terminal : Vertex}
      (chain : MarkedConclusionChain certificate state origin terminal)
      (consumer : ConnectiveBelow certificate terminal)
      (mateUnmarked : state.core.marks[consumer.mate]? = some none) :
      ForwardOutcomeObserved tagHistory origin outer outerAge
  | futureConclusion {terminal : Vertex}
      (chain : MarkedConclusionChain certificate state origin terminal)
      (consumer : ConnectiveBelow certificate terminal)
      (boundary : RawTokenAge)
      (work : FutureWorkAt state boundary consumer.conclusion) :
      ForwardOutcomeObserved tagHistory origin outer outerAge
  | markedGlobalAfter {terminal : Vertex}
      (chain : MarkedConclusionChain certificate state origin terminal)
      (consumer : ConnectiveBelow certificate terminal)
      (conclusionAge : RawTokenAge)
      (marked :
        state.core.marks[consumer.conclusion]? = some (some conclusionAge))
      (global : consumer.conclusion ∈ certificate.conclusions)
      (before : tagHistory.RawMarkedBefore outerAge outer conclusionAge
        consumer.conclusion) :
      ForwardOutcomeObserved tagHistory origin outer outerAge

private theorem Consumer.observeForwardOutcome
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {origin outer : Vertex} {outerAge : RawTokenAge}
    (outcome :
      ContinuationExitOuterTerminalForwardCausalOutcome tagHistory origin outer
        outerAge) :
    ForwardOutcomeObserved tagHistory origin outer outerAge := by
  cases outcome with
  | rawMate chain consumer mateUnmarked =>
      exact .rawMate chain consumer mateUnmarked
  | futureConclusion chain consumer boundary work =>
      exact .futureConclusion chain consumer boundary work
  | markedGlobalAfter chain consumer conclusionAge marked global before =>
      exact .markedGlobalAfter chain consumer conclusionAge marked global before

private theorem Consumer.forwardCausalOutcome
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {origin outer : Vertex} {outerAge : RawTokenAge}
    (exit : ContinuationExit certificate state origin)
    (outerChain : MarkedConclusionChain certificate state origin outer)
    (outerEvent : tagHistory.RawMarked outerAge outer) :
    ForwardOutcomeObserved tagHistory origin outer outerAge := by
  exact Consumer.observeForwardOutcome
    (exit.outerTerminalForwardCausalOutcome outerChain outerEvent)

private theorem Consumer.forwardCausalTarget
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {owned : List Vertex}
    {current : ConnectiveBelow certificate input.vertex}
    (invariant : SchedulerInvariant certificate state)
    (target :
      ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitCausalEndpointTarget
        tagHistory input component owned current) :
    ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitForwardCausalTarget
      tagHistory input component owned current := by
  exact target.forwardCausalTarget invariant.structural
    invariant.queued_vertices_unmarked

private theorem Consumer.waitForwardCausalOutcome
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    (correct : certificate.DeclarativelyCorrect)
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
          ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitForwardCausalTarget
            tagHistory step.prepared.readyHeadInput component owned
              step.consumer) := by
  exact step.commitmentInterval_parTraceReentryMarkedContinuationSiblingExitForwardCausalOutcome
    correct connected tagHistory invariant componentLookup occurrence positive
    firstAt lastAt noTail

#print axioms ContinuationExitOuterTerminalForwardCausalOutcome
#print axioms ContinuationExit.afterMarkedSibling
#print axioms ContinuationExit.outerTerminalForwardCausalOutcome
#print axioms
  ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitForwardCausalTarget
namespace ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitCausalEndpointTarget
#print axioms forwardCausalTarget
end ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitCausalEndpointTarget
#print axioms
  WaitStep.commitmentInterval_parTraceReentryMarkedContinuationSiblingExitForwardCausalOutcome

end SequentialFigure7
end ProofNetIR

def main : IO Unit :=
  IO.println "Figure-7 sibling-exit forward causal order: kernel-green"
