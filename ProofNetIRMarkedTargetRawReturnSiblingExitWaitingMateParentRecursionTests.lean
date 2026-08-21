/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7MarkedTargetRawReturnSiblingExitWaitingMateParentRecursion

/-!
# Figure-7 active-mate waiting parent-recursion consumer

Consumes every public declaration in the waiting-mate parent-recursion
checkpoint, reconstructs each carrier, and invokes the typed Wait lift.
-/

namespace ProofNetIRMarkedTargetRawReturnSiblingExitWaitingMateParentRecursionTests

open ProofNetIR
open ProofNetIR.SequentialSchedulerState
open ProofNetIR.SequentialSchedulerBridge
open ProofNetIR.SequentialFigure7

example {certificate : Certificate} {state : ReservationState}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {usedLinks owned : List Nat}
    (structural : certificate.StructurallyWellFormed)
    (queuedUnmarked : QueuedVerticesUnmarked state)
    (occurrence :
      certificate.ComponentOccurrenceWitness component usedLinks owned)
    {terminal : Vertex} {consumer : ConnectiveBelow certificate terminal}
    {boundary : RawTokenAge}
    (conclusionOutside : consumer.conclusion ∉ owned)
    (mateActive : consumer.mate ∈ owned)
    (waiting :
      FutureWorkActiveMateWaitingOutcome certificate state input terminal
        consumer boundary) :
    ActiveCarrierParentEscape certificate state component owned input.vertex := by
  exact waiting.activeCarrierParentEscape structural queuedUnmarked occurrence
    conclusionOutside mateActive

example {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {usedLinks owned : List Nat}
    (invariant : SchedulerInvariant certificate state)
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      certificate.ComponentOccurrenceWitness component usedLinks owned)
    {terminal : Vertex} {consumer : ConnectiveBelow certificate terminal}
    {boundary : RawTokenAge}
    (conclusionOutside : consumer.conclusion ∉ owned)
    (mateActive : consumer.mate ∈ owned)
    (waiting :
      FutureWorkActiveMateWaitingOutcome certificate state input terminal
        consumer boundary)
    (noTail :
      ¬ ∃ pending,
        pending ∈ input.readyTail ∧ pending ∉ certificate.conclusions) :
    ActiveCarrierParentTemporalOutcome certificate state input.rawAge
      input.vertex owned := by
  exact waiting.parentTemporalOutcome tagHistory correct invariant
    componentLookup occurrence conclusionOutside mateActive noTail

example {certificate : Certificate} {state : ReservationState}
    {input : ReadyHeadInput state} {owned : List Vertex}
    {terminal : Vertex} {consumer : ConnectiveBelow certificate terminal}
    {boundary mateAge : RawTokenAge}
    (status :
      FutureWorkMateActiveCarrierParentRecursionStatus certificate state
        input owned terminal consumer boundary mateAge) :
    FutureWorkMateActiveCarrierParentRecursionStatus certificate state
      input owned terminal consumer boundary mateAge := by
  cases status with
  | olderOutside notMembership representativeOlder =>
      exact .olderOutside notMembership representativeOlder
  | activeParent membership representative waiting recursive =>
      exact .activeParent membership representative waiting recursive

example {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {usedLinks owned : List Nat}
    (invariant : SchedulerInvariant certificate state)
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      certificate.ComponentOccurrenceWitness component usedLinks owned)
    {terminal : Vertex} {consumer : ConnectiveBelow certificate terminal}
    {boundary mateAge : RawTokenAge}
    (conclusionOutside : consumer.conclusion ∉ owned)
    (status :
      FutureWorkMateActiveCarrierReadyEliminatedStatus certificate state input
        owned terminal consumer boundary mateAge)
    (noTail :
      ¬ ∃ pending,
        pending ∈ input.readyTail ∧ pending ∉ certificate.conclusions) :
    FutureWorkMateActiveCarrierParentRecursionStatus certificate state
      input owned terminal consumer boundary mateAge := by
  exact status.parentRecursionStatus tagHistory correct invariant
    componentLookup occurrence conclusionOutside noTail

example {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {owned : List Vertex}
    {current : ConnectiveBelow certificate input.vertex} {origin : Vertex}
    (outcome :
      ContinuationExitRawOrFutureActiveCarrierParentRecursionOutcome
        certificate state tagHistory input owned current origin) :
    ContinuationExitRawOrFutureActiveCarrierParentRecursionOutcome certificate
      state tagHistory input owned current origin := by
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
        mateMarked terminalEvent mateEvent terminalRepresentativeOlder
        mateStatus premiseOrder location

example {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {usedLinks owned : List Nat}
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate state)
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      certificate.ComponentOccurrenceWitness component usedLinks owned)
    {current : ConnectiveBelow certificate input.vertex} {origin : Vertex}
    (outcome :
      ContinuationExitRawOrFutureActiveCarrierReadyMateOutcome certificate
        state tagHistory input owned current origin)
    (noTail :
      ¬ ∃ pending,
        pending ∈ input.readyTail ∧ pending ∉ certificate.conclusions) :
    ContinuationExitRawOrFutureActiveCarrierParentRecursionOutcome certificate
      state tagHistory input owned current origin := by
  exact outcome.parentRecursionOutcome correct invariant componentLookup
    occurrence noTail

example {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {owned : List Vertex}
    {current : ConnectiveBelow certificate input.vertex}
    (target :
      ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitParentRecursionTarget
        tagHistory input component owned current) :
    ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitParentRecursionTarget
      tagHistory input component owned current := by
  rcases target with
    ⟨outerAge, outerEvent, path, directed, markedAge, pathStart, pathFinish,
      directedMembership, inbound, targetNeSelected, targetNeMate, targetMarked,
      targetEvent, targetRepresentative, targetConsumer, targetMateNeSelected,
      directedSource, conclusionOutside, exit⟩
  exact ⟨outerAge, outerEvent, path, directed, markedAge, pathStart,
    pathFinish, directedMembership, inbound, targetNeSelected, targetNeMate,
    targetMarked, targetEvent, targetRepresentative, targetConsumer,
    targetMateNeSelected, directedSource, conclusionOutside, exit⟩

example {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {usedLinks owned : List Nat}
    {current : ConnectiveBelow certificate input.vertex}
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate state)
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      certificate.ComponentOccurrenceWitness component usedLinks owned)
    (target :
      ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitReadyMateTarget
        tagHistory input component owned current)
    (noTail :
      ¬ ∃ pending,
        pending ∈ input.readyTail ∧ pending ∉ certificate.conclusions) :
    ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitParentRecursionTarget
      tagHistory input component owned current := by
  exact target.parentRecursionTarget correct invariant componentLookup
    occurrence noTail

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
        ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitParentRecursionTarget
            tagHistory step.prepared.readyHeadInput component owned
              step.consumer) := by
  exact step.commitmentInterval_parTraceReentryMarkedContinuationSiblingExitParentRecursionOutcome
    correct connected tagHistory invariant componentLookup occurrence positive
      firstAt lastAt noTail

#print axioms FutureWorkActiveMateWaitingOutcome.activeCarrierParentEscape
#print axioms FutureWorkActiveMateWaitingOutcome.parentTemporalOutcome
#print axioms FutureWorkMateActiveCarrierParentRecursionStatus
#print axioms FutureWorkMateActiveCarrierReadyEliminatedStatus.parentRecursionStatus
#print axioms ContinuationExitRawOrFutureActiveCarrierParentRecursionOutcome
#print axioms ContinuationExitRawOrFutureActiveCarrierReadyMateOutcome.parentRecursionOutcome
#print axioms
  ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitParentRecursionTarget
open
  ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitReadyMateTarget

#print axioms parentRecursionTarget
#print axioms
  WaitStep.commitmentInterval_parTraceReentryMarkedContinuationSiblingExitParentRecursionOutcome

end ProofNetIRMarkedTargetRawReturnSiblingExitWaitingMateParentRecursionTests

def main : IO Unit :=
  IO.println "Figure-7 active-mate waiting parent recursion: kernel-green"
