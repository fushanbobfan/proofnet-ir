/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7MarkedTargetRawReturnSiblingExitTemporal

/-!
# Figure-7 sibling temporal-exit consumer

This runnable consumer imports only the production module under test.  It
destructs every endpoint form, calls the generic normalizer and target adapter,
and consumes the typed Wait theorem.  It does not assert that the exact raw
return or the surrounding parent re-entry residual is impossible.
-/

namespace ProofNetIR
namespace SequentialFigure7
namespace Consumer

open SequentialSchedulerState
open SequentialSchedulerBridge

private inductive TemporalObservation
    (certificate : Certificate) (state : ReservationState)
    (input : ReadyHeadInput state) (owned : List Vertex)
    (current : ConnectiveBelow certificate input.vertex)
    (origin : Vertex) : Prop where
  | rawOutside {terminal : Vertex}
      (chain : MarkedConclusionChain certificate state origin terminal)
      (terminalOutside : terminal ∉ owned)
      (consumer : ConnectiveBelow certificate terminal)
      (mateUnmarked : state.core.marks[consumer.mate]? = some none)
      (mateOutside : consumer.mate ∉ owned) :
      TemporalObservation certificate state input owned current origin
  | rawSelectedReturn {terminal : Vertex}
      (chain : MarkedConclusionChain certificate state origin terminal)
      (terminalOutside : terminal ∉ owned)
      (consumer : ConnectiveBelow certificate terminal)
      (mateUnmarked : state.core.marks[consumer.mate]? = some none)
      (mateSelected : consumer.mate = input.vertex)
      (terminalCurrentMate : terminal = current.mate)
      (conclusionCurrent : consumer.conclusion = current.conclusion) :
      TemporalObservation certificate state input owned current origin
  | futureOlder {terminal : Vertex}
      (chain : MarkedConclusionChain certificate state origin terminal)
      (terminalOutside : terminal ∉ owned)
      (consumer : ConnectiveBelow certificate terminal)
      (boundary : RawTokenAge)
      (work : FutureWorkAt state boundary consumer.conclusion)
      (conclusionOutside : consumer.conclusion ∉ owned)
      (boundaryOlder : boundary < input.rawAge) :
      TemporalObservation certificate state input owned current origin

private theorem observeTemporalOutcome
    {certificate : Certificate} {state : ReservationState}
    {input : ReadyHeadInput state} {owned : List Vertex}
    {current : ConnectiveBelow certificate input.vertex}
    {origin : Vertex}
    (outcome :
      ContinuationExitRawOrFutureActiveCarrierOutcome certificate state input
        owned current origin) :
    TemporalObservation certificate state input owned current origin := by
  cases outcome with
  | rawOutside chain terminalOutside consumer mateUnmarked mateOutside =>
      exact .rawOutside chain terminalOutside consumer mateUnmarked mateOutside
  | rawSelectedReturn chain terminalOutside consumer mateUnmarked mateSelected
      terminalCurrentMate conclusionCurrent =>
      exact .rawSelectedReturn chain terminalOutside consumer mateUnmarked
        mateSelected terminalCurrentMate conclusionCurrent
  | futureOlder chain terminalOutside consumer boundary work conclusionOutside
      boundaryOlder =>
      exact .futureOlder chain terminalOutside consumer boundary work
        conclusionOutside boundaryOlder

private example
    {certificate : Certificate} {state : ReservationState}
    {origin : Vertex}
    (exit : ContinuationExitRawOrFuture certificate state origin)
    (invariant : SchedulerInvariant certificate state)
    (input : ReadyHeadInput state)
    (current : ConnectiveBelow certificate input.vertex)
    {component : UnificationComponent} {usedLinks owned : List Nat}
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component
        usedLinks owned)
    (originOutside : origin ∉ owned)
    (noTail :
      ¬ ∃ pending,
        pending ∈ input.readyTail ∧ pending ∉ certificate.conclusions) :
    TemporalObservation certificate state input owned current origin := by
  exact observeTemporalOutcome
    (exit.activeCarrierOutcome invariant input current componentLookup
      occurrence originOutside noTail)

private example
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {usedLinks owned : List Nat}
    {current : ConnectiveBelow certificate input.vertex}
    (invariant : SchedulerInvariant certificate state)
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component
        usedLinks owned)
    (noTail :
      ¬ ∃ pending,
        pending ∈ input.readyTail ∧ pending ∉ certificate.conclusions)
    (target :
      ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitOpenTarget
        tagHistory input component owned current) :
    ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitTemporalTarget
      tagHistory input component owned current := by
  exact target.temporalTarget invariant componentLookup occurrence noTail

private example
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
          ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitTemporalTarget
            tagHistory step.prepared.readyHeadInput component owned
              step.consumer) := by
  exact
    step.commitmentInterval_parTraceReentryMarkedContinuationSiblingExitTemporalOutcome
      correct connected tagHistory invariant componentLookup occurrence positive
      firstAt lastAt noTail

#print axioms ContinuationExitRawOrFutureActiveCarrierOutcome
#print axioms ContinuationExitRawOrFuture.activeCarrierOutcome
#print axioms ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitTemporalTarget
#print axioms
  ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitOpenTarget.temporalTarget
#print axioms
  WaitStep.commitmentInterval_parTraceReentryMarkedContinuationSiblingExitTemporalOutcome

end Consumer
end SequentialFigure7
end ProofNetIR

def main : IO Unit :=
  IO.println "Figure-7 sibling temporal exits: kernel-green"
