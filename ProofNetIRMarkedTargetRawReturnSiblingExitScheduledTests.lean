/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7MarkedTargetRawReturnSiblingExitScheduled

/-!
# Figure-7 sibling scheduled-exit consumer

This runnable consumer imports only the production module under test.  It
destructs both exact scheduler locations and every scheduled sibling endpoint,
calls the generic future-work facts and both target adapters, and consumes the
typed Wait theorem.  It does not eliminate the exact raw return or older future
endpoint and does not assert a history-tail law or progress.
-/

namespace ProofNetIR
namespace SequentialFigure7
namespace Consumer

open SequentialSchedulerState
open SequentialSchedulerBridge

private theorem locationRoundTrip
    {certificate : Certificate} {state : ReservationState}
    {boundary : RawTokenAge} {vertex : Vertex}
    (location :
      FutureWorkAtExactSchedulerLocation certificate state boundary vertex) :
    FutureWorkAtExactSchedulerLocation certificate state boundary vertex := by
  cases location with
  | ready sigmaAt readyAt member componentLookup frontier unmarked =>
      exact .ready sigmaAt readyAt member componentLookup frontier unmarked
  | waiting waitingAt member linkLookup sourceLookup unmarked orientation
      olderMarked youngerMarked olderBoundary youngerBoundaryLookup
      boundaryLt =>
      exact .waiting waitingAt member linkLookup sourceLookup unmarked
        orientation olderMarked youngerMarked olderBoundary
        youngerBoundaryLookup boundaryLt

private example
    {certificate : Certificate} {state : ReservationState}
    {boundary : RawTokenAge} {vertex : Vertex}
    (work : FutureWorkAt state boundary vertex)
    (invariant : SchedulerInvariant certificate state) :
    FutureWorkAtExactSchedulerLocation certificate state boundary vertex := by
  exact locationRoundTrip (work.exactSchedulerLocation invariant)

private example
    {certificate : Certificate} {state : ReservationState} {vertex : Vertex}
    (consumer : ConnectiveBelow certificate vertex)
    {boundary : RawTokenAge}
    (work : FutureWorkAt state boundary consumer.conclusion)
    (invariant : SchedulerInvariant certificate state) :
    (∃ vertexAge,
        state.core.marks[vertex]? = some (some vertexAge)) ∧
      ∃ mateAge,
        state.core.marks[consumer.mate]? = some (some mateAge) := by
  rcases ConnectiveBelow.premisesMarked_of_futureWork consumer work invariant
    with ⟨⟨vertexAge, vertexMarked⟩, mateAge, mateMarked⟩
  exact ⟨⟨vertexAge, vertexMarked⟩, mateAge, mateMarked⟩

private theorem scheduledOutcomeRoundTrip
    {certificate : Certificate} {state : ReservationState}
    {input : ReadyHeadInput state} {owned : List Vertex}
    {current : ConnectiveBelow certificate input.vertex} {origin : Vertex}
    (outcome :
      ContinuationExitRawOrFutureActiveCarrierScheduledOutcome certificate state
        input owned current origin) :
    ContinuationExitRawOrFutureActiveCarrierScheduledOutcome certificate state
      input owned current origin := by
  cases outcome with
  | rawOutside chain terminalOutside consumer mateUnmarked mateOutside =>
      exact .rawOutside chain terminalOutside consumer mateUnmarked mateOutside
  | rawSelectedReturn chain terminalOutside consumer mateUnmarked mateSelected
      terminalCurrentMate conclusionCurrent =>
      exact .rawSelectedReturn chain terminalOutside consumer mateUnmarked
        mateSelected terminalCurrentMate conclusionCurrent
  | futureOlder chain terminalOutside consumer boundary work conclusionOutside
      boundaryOlder terminalMarked mateMarked location =>
      rcases terminalMarked with ⟨terminalAge, terminalMarked⟩
      rcases mateMarked with ⟨mateAge, mateMarked⟩
      exact .futureOlder chain terminalOutside consumer boundary work
        conclusionOutside boundaryOlder ⟨terminalAge, terminalMarked⟩
        ⟨mateAge, mateMarked⟩ (locationRoundTrip location)

private example
    {certificate : Certificate} {state : ReservationState}
    {input : ReadyHeadInput state} {owned : List Vertex}
    {current : ConnectiveBelow certificate input.vertex} {origin : Vertex}
    (outcome : ContinuationExitRawOrFutureActiveCarrierOutcome certificate state
      input owned current origin)
    (invariant : SchedulerInvariant certificate state) :
    ContinuationExitRawOrFutureActiveCarrierScheduledOutcome certificate state
      input owned current origin := by
  exact scheduledOutcomeRoundTrip (outcome.scheduledOutcome invariant)

private example
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {owned : List Vertex}
    {current : ConnectiveBelow certificate input.vertex}
    (invariant : SchedulerInvariant certificate state)
    (target :
      ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitTemporalTarget
        tagHistory input component owned current) :
    ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitScheduledTarget
      tagHistory input component owned current := by
  exact target.scheduledTarget invariant

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
          ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitScheduledTarget
            tagHistory step.prepared.readyHeadInput component owned
              step.consumer) := by
  exact
    step.commitmentInterval_parTraceReentryMarkedContinuationSiblingExitScheduledOutcome
      correct connected tagHistory invariant componentLookup occurrence positive
      firstAt lastAt noTail

#print axioms FutureWorkAtExactSchedulerLocation
#print axioms FutureWorkAt.exactSchedulerLocation
#print axioms ConnectiveBelow.premisesMarked_of_futureWork
#print axioms ContinuationExitRawOrFutureActiveCarrierScheduledOutcome
#print axioms ContinuationExitRawOrFutureActiveCarrierOutcome.scheduledOutcome
#print axioms
  ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitScheduledTarget

end Consumer

namespace ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitTemporalTarget
#print axioms scheduledTarget
end ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitTemporalTarget
#print axioms
  WaitStep.commitmentInterval_parTraceReentryMarkedContinuationSiblingExitScheduledOutcome

end SequentialFigure7
end ProofNetIR

def main : IO Unit :=
  IO.println "Figure-7 sibling scheduled exits: kernel-green"
