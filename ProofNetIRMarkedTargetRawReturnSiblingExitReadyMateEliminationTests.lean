/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7MarkedTargetRawReturnSiblingExitReadyMateElimination

/-!
# Figure-7 active-mate ready-endpoint elimination consumer

Consumes every public declaration in the ready-mate elimination checkpoint,
including both directions of each carrier observation and the typed Wait lift.
-/

namespace ProofNetIRMarkedTargetRawReturnSiblingExitReadyMateEliminationTests

open ProofNetIR
open ProofNetIR.SequentialSchedulerState
open ProofNetIR.SequentialSchedulerBridge
open ProofNetIR.SequentialFigure7
open ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitCausalOwnershipTarget

example {certificate : Certificate} {state : ReservationState}
    {input : ReadyHeadInput state} {terminal : Vertex}
    {consumer : ConnectiveBelow certificate terminal}
    {boundary : RawTokenAge}
    (outcome : FutureWorkActiveMateWaitingOutcome certificate state input
      terminal consumer boundary) :
    FutureWorkActiveMateWaitingOutcome certificate state input terminal
      consumer boundary := by
  cases outcome with
  | waitingReturn waitingAt member linkLookup sourceLookup unmarked
      olderMarked youngerMarked olderBoundary boundaryOlder terminalOlder
      mateYounger youngerBoundaryActive =>
      exact .waitingReturn waitingAt member linkLookup sourceLookup unmarked
        olderMarked youngerMarked olderBoundary boundaryOlder terminalOlder
        mateYounger youngerBoundaryActive

example {certificate : Certificate} {state : ReservationState}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {usedLinks owned : List Nat}
    (invariant : SchedulerInvariant certificate state)
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      certificate.ComponentOccurrenceWitness component usedLinks owned)
    {terminal : Vertex} {consumer : ConnectiveBelow certificate terminal}
    {boundary : RawTokenAge}
    (mateActive : consumer.mate ∈ owned)
    (boundaryOlder : boundary < input.rawAge)
    (scheduler : FutureWorkActiveMateSchedulerOutcome certificate state input
      terminal consumer boundary) :
    FutureWorkActiveMateWaitingOutcome certificate state input terminal
      consumer boundary :=
  scheduler.waitingOutcome_of_activeOwned invariant componentLookup occurrence
    mateActive boundaryOlder

example {certificate : Certificate} {state : ReservationState}
    {input : ReadyHeadInput state} {owned : List Vertex}
    {terminal : Vertex} {consumer : ConnectiveBelow certificate terminal}
    {boundary mateAge : RawTokenAge}
    (status : FutureWorkMateActiveCarrierReadyEliminatedStatus certificate state
      input owned terminal consumer boundary mateAge) :
    FutureWorkMateActiveCarrierReadyEliminatedStatus certificate state input
      owned terminal consumer boundary mateAge := by
  cases status with
  | olderOutside notMembership representativeOlder =>
      exact .olderOutside notMembership representativeOlder
  | activeWaiting membership representative scheduler =>
      exact .activeWaiting membership representative scheduler

example {certificate : Certificate} {state : ReservationState}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {usedLinks owned : List Nat}
    (invariant : SchedulerInvariant certificate state)
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      certificate.ComponentOccurrenceWitness component usedLinks owned)
    {terminal : Vertex} {consumer : ConnectiveBelow certificate terminal}
    {boundary mateAge : RawTokenAge}
    (boundaryOlder : boundary < input.rawAge)
    (status : FutureWorkMateActiveCarrierScheduledStatus certificate state input
      owned terminal consumer boundary mateAge) :
    FutureWorkMateActiveCarrierReadyEliminatedStatus certificate state input
      owned terminal consumer boundary mateAge :=
  status.readyEliminatedStatus invariant componentLookup occurrence boundaryOlder

example {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {owned : List Vertex}
    {current : ConnectiveBelow certificate input.vertex} {origin : Vertex}
    (outcome : ContinuationExitRawOrFutureActiveCarrierReadyMateOutcome
      certificate state tagHistory input owned current origin) :
    ContinuationExitRawOrFutureActiveCarrierReadyMateOutcome certificate state
      tagHistory input owned current origin := by
  cases outcome with
  | rawOutside chain terminalOutside consumer mateUnmarked mateOutside =>
      exact .rawOutside chain terminalOutside consumer mateUnmarked mateOutside
  | rawSelectedReturn chain terminalOutside consumer mateUnmarked mateSelected
      terminalCurrentMate conclusionCurrent =>
      exact .rawSelectedReturn chain terminalOutside consumer mateUnmarked
        mateSelected terminalCurrentMate conclusionCurrent
  | futureOlder chain terminalOutside consumer boundary work conclusionOutside
      boundaryOlder terminalAge mateAge terminalMarked mateMarked terminalEvent
      mateEvent terminalRepresentativeOlder mateStatus premiseOrder location =>
      exact .futureOlder chain terminalOutside consumer boundary work
        conclusionOutside boundaryOlder terminalAge mateAge terminalMarked
        mateMarked terminalEvent mateEvent terminalRepresentativeOlder mateStatus
        premiseOrder location

example {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {usedLinks owned : List Nat}
    (invariant : SchedulerInvariant certificate state)
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      certificate.ComponentOccurrenceWitness component usedLinks owned)
    {current : ConnectiveBelow certificate input.vertex} {origin : Vertex}
    (outcome : ContinuationExitRawOrFutureActiveCarrierCausalOwnershipOutcome
      certificate state tagHistory input owned current origin) :
    ContinuationExitRawOrFutureActiveCarrierReadyMateOutcome certificate state
      tagHistory input owned current origin :=
  outcome.readyMateOutcome invariant componentLookup occurrence

example {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {owned : List Vertex} {current : ConnectiveBelow certificate input.vertex}
    (target :
      ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitReadyMateTarget
        tagHistory input component owned current) :
    ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitReadyMateTarget
      tagHistory input component owned current := target

example {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {usedLinks owned : List Nat}
    {current : ConnectiveBelow certificate input.vertex}
    (invariant : SchedulerInvariant certificate state)
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      certificate.ComponentOccurrenceWitness component usedLinks owned)
    (target :
      ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitCausalOwnershipTarget
        tagHistory input component owned current) :
    ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitReadyMateTarget
      tagHistory input component owned current :=
  target.readyMateTarget invariant componentLookup occurrence

example {certificate : Certificate} {before after : ReservationState}
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
      certificate.ComponentOccurrenceWitness component usedLinks owned)
    {position edgeCount : Nat} {first : RawTokenAge}
    (positive : 0 < edgeCount)
    (firstAt : before.stack.sigma[position]? = some first)
    (lastAt : before.stack.sigma[position + edgeCount]? =
      some step.prepared.stackResult.rawAge)
    (noTail :
      ¬ ∃ pending,
        pending ∈ step.prepared.stackResult.remainingTop ∧
          pending ∉ certificate.conclusions) :
    tagHistory.CommitmentIntervalParTraceOutcome
      step.prepared.readyHeadInput step.consumer position edgeCount first
        (step.consumer.mate ∉ owned ∧
          before.core.marks[step.consumer.mate]? = some (some step.mateRawAge) ∧
          before.core.representative step.mateRawAge <
            step.prepared.stackResult.rawAge ∧
        ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitReadyMateTarget
          tagHistory step.prepared.readyHeadInput component owned step.consumer) :=
  step.commitmentInterval_parTraceReentryMarkedContinuationSiblingExitReadyMateOutcome
    correct connected tagHistory invariant componentLookup occurrence positive
      firstAt lastAt noTail

#print axioms FutureWorkActiveMateWaitingOutcome
#print axioms FutureWorkActiveMateSchedulerOutcome.waitingOutcome_of_activeOwned
#print axioms FutureWorkMateActiveCarrierReadyEliminatedStatus
#print axioms FutureWorkMateActiveCarrierScheduledStatus.readyEliminatedStatus
#print axioms ContinuationExitRawOrFutureActiveCarrierReadyMateOutcome
#print axioms ContinuationExitRawOrFutureActiveCarrierCausalOwnershipOutcome.readyMateOutcome
#print axioms ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitReadyMateTarget
#print axioms readyMateTarget
#print axioms
  WaitStep.commitmentInterval_parTraceReentryMarkedContinuationSiblingExitReadyMateOutcome

end ProofNetIRMarkedTargetRawReturnSiblingExitReadyMateEliminationTests

def main : IO Unit :=
  IO.println "Figure-7 active-mate ready-endpoint elimination: kernel-green"
