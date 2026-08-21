/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7MarkedTargetWaitingMateExternalCommitmentReentryMarked

/-!
# Figure-7 stored-right waiting re-entry marked-target consumer

Consumes the generic stored-right refinement and every public declaration in
the waiting-mate commitment re-entry marked-target checkpoint. Each carrier is
reconstructed, each refinement theorem is invoked, and the typed Wait lift is
exercised directly.
-/

namespace ProofNetIRMarkedTargetWaitingMateExternalCommitmentReentryMarkedTests

open ProofNetIR
open ProofNetIR.SequentialSchedulerState
open ProofNetIR.SequentialSchedulerBridge
open ProofNetIR.SequentialFigure7

example {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {owned : List Vertex} {endpoint : Vertex}
    (status : ActiveCarrierExternalReentryFailureHistoricalStatus tagHistory
      input component owned endpoint)
    (structural : certificate.StructurallyWellFormed)
    (current : ConnectiveBelow certificate input.vertex)
    (parEq : current.kind = .par)
    (sideRight : current.side = .storedRight) :
    ActiveCarrierExternalReentryMarkedHistoricalTarget tagHistory input
      component owned endpoint := by
  exact status.markedHistoricalTarget_of_storedRight structural current parEq
    sideRight

example {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {owned : List Vertex} {terminal : Vertex}
    {consumer : ConnectiveBelow certificate terminal}
    (outcome : ActiveMateWaitingParentExternalCommitmentReentryMarkedOutcome
      tagHistory input component owned consumer) :
    ActiveMateWaitingParentExternalCommitmentReentryMarkedOutcome tagHistory
      input component owned consumer := by
  cases outcome with
  | olderFuture boundary work older outside commitmentSplit crossing reentry
      markedTarget =>
      exact .olderFuture boundary work older outside commitmentSplit crossing
        reentry markedTarget
  | olderMarked conclusionAge marked olderRepresentative outside
      commitmentSplit crossing reentry markedTarget =>
      exact .olderMarked conclusionAge marked olderRepresentative outside
        commitmentSplit crossing reentry markedTarget

example {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {owned : List Vertex} {terminal : Vertex}
    {consumer : ConnectiveBelow certificate terminal}
    (outcome : ActiveMateWaitingParentExternalCommitmentReentryFailureOutcome
      tagHistory input component owned consumer)
    (structural : certificate.StructurallyWellFormed)
    (current : ConnectiveBelow certificate input.vertex)
    (parEq : current.kind = .par)
    (sideRight : current.side = .storedRight) :
    ActiveMateWaitingParentExternalCommitmentReentryMarkedOutcome tagHistory
      input component owned consumer := by
  exact outcome.markedOutcome_of_storedRight structural current parEq sideRight

example {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {owned : List Vertex} {terminal : Vertex}
    {consumer : ConnectiveBelow certificate terminal}
    {boundary mateAge : RawTokenAge}
    (status : FutureWorkMateActiveCarrierExternalCommitmentReentryMarkedStatus
      tagHistory input component owned terminal consumer boundary mateAge) :
    FutureWorkMateActiveCarrierExternalCommitmentReentryMarkedStatus tagHistory
      input component owned terminal consumer boundary mateAge := by
  cases status with
  | olderOutside notMembership representativeOlder =>
      exact .olderOutside notMembership representativeOlder
  | activeExternal membership representative waiting external =>
      exact .activeExternal membership representative waiting external

example {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {usedLinks owned : List Nat}
    (connected : certificate.ReferenceSwitchingConnected)
    (invariant : SchedulerInvariant certificate state)
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      certificate.ComponentOccurrenceWitness component usedLinks owned)
    (current : ConnectiveBelow certificate input.vertex)
    (parEq : current.kind = .par)
    (sideRight : current.side = .storedRight)
    (noTail :
      ¬ ∃ pending,
        pending ∈ input.readyTail ∧ pending ∉ certificate.conclusions)
    {terminal : Vertex} {consumer : ConnectiveBelow certificate terminal}
    {boundary mateAge : RawTokenAge}
    (status : FutureWorkMateActiveCarrierExternalTemporalStatus certificate
      state input owned terminal consumer boundary mateAge) :
    FutureWorkMateActiveCarrierExternalCommitmentReentryMarkedStatus tagHistory
      input component owned terminal consumer boundary mateAge := by
  exact status.commitmentReentryMarkedStatus_of_storedRight tagHistory
    connected invariant componentLookup occurrence current parEq sideRight
    noTail

example {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {owned : List Vertex}
    {current : ConnectiveBelow certificate input.vertex} {origin : Vertex}
    (outcome :
      ContinuationExitRawOrFutureActiveCarrierExternalCommitmentReentryMarkedOutcome
        certificate state tagHistory input component owned current origin) :
    ContinuationExitRawOrFutureActiveCarrierExternalCommitmentReentryMarkedOutcome
      certificate state tagHistory input component owned current origin := by
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
    (connected : certificate.ReferenceSwitchingConnected)
    (invariant : SchedulerInvariant certificate state)
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      certificate.ComponentOccurrenceWitness component usedLinks owned)
    {current : ConnectiveBelow certificate input.vertex}
    (parEq : current.kind = .par)
    (sideRight : current.side = .storedRight)
    (noTail :
      ¬ ∃ pending,
        pending ∈ input.readyTail ∧ pending ∉ certificate.conclusions)
    {origin : Vertex}
    (outcome : ContinuationExitRawOrFutureActiveCarrierExternalTemporalOutcome
      certificate state tagHistory input owned current origin) :
    ContinuationExitRawOrFutureActiveCarrierExternalCommitmentReentryMarkedOutcome
      certificate state tagHistory input component owned current origin := by
  exact outcome.commitmentReentryMarkedOutcome_of_storedRight connected
    invariant componentLookup occurrence parEq sideRight noTail

example {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {owned : List Vertex}
    {current : ConnectiveBelow certificate input.vertex}
    (target :
      ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitWaitingMarkedTarget
        tagHistory input component owned current) :
    ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitWaitingMarkedTarget
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
    (connected : certificate.ReferenceSwitchingConnected)
    (invariant : SchedulerInvariant certificate state)
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      certificate.ComponentOccurrenceWitness component usedLinks owned)
    (parEq : current.kind = .par)
    (sideRight : current.side = .storedRight)
    (noTail :
      ¬ ∃ pending,
        pending ∈ input.readyTail ∧ pending ∉ certificate.conclusions)
    (target :
      ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitExternalTemporalTarget
        tagHistory input component owned current) :
    ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitWaitingMarkedTarget
      tagHistory input component owned current := by
  exact target.waitingMarkedTarget_of_storedRight connected invariant
    componentLookup occurrence parEq sideRight noTail

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
        ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitWaitingMarkedTarget
            tagHistory step.prepared.readyHeadInput component owned
              step.consumer) := by
  exact
    step.commitmentInterval_parTraceReentryMarkedContinuationSiblingExitWaitingMarkedOutcome
      correct connected tagHistory invariant componentLookup occurrence
        positive firstAt lastAt noTail

#print axioms
  ActiveCarrierExternalReentryFailureHistoricalStatus.markedHistoricalTarget_of_storedRight
#print axioms ActiveMateWaitingParentExternalCommitmentReentryMarkedOutcome
#print axioms
  ActiveMateWaitingParentExternalCommitmentReentryFailureOutcome.markedOutcome_of_storedRight
#print axioms
  FutureWorkMateActiveCarrierExternalCommitmentReentryMarkedStatus
#print axioms
  FutureWorkMateActiveCarrierExternalTemporalStatus.commitmentReentryMarkedStatus_of_storedRight
#print axioms
  ContinuationExitRawOrFutureActiveCarrierExternalCommitmentReentryMarkedOutcome
open ContinuationExitRawOrFutureActiveCarrierExternalTemporalOutcome

#print axioms commitmentReentryMarkedOutcome_of_storedRight
#print axioms
  ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitWaitingMarkedTarget
open
  ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitExternalTemporalTarget

#print axioms waitingMarkedTarget_of_storedRight
#print axioms
  WaitStep.commitmentInterval_parTraceReentryMarkedContinuationSiblingExitWaitingMarkedOutcome

end ProofNetIRMarkedTargetWaitingMateExternalCommitmentReentryMarkedTests

def main : IO Unit :=
  IO.println "Figure-7 stored-right waiting re-entry marked target: kernel-green"
