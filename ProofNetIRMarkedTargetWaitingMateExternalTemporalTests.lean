/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7MarkedTargetWaitingMateExternalTemporal

/-!
# Figure-7 active-mate waiting external-temporal consumer

Consumes every public declaration in the waiting-mate external-temporal
checkpoint, reconstructs each carrier, and invokes the typed Wait lift.
-/

namespace ProofNetIRMarkedTargetWaitingMateExternalTemporalTests

open ProofNetIR
open ProofNetIR.SequentialSchedulerState
open ProofNetIR.SequentialSchedulerBridge
open ProofNetIR.SequentialFigure7

example {certificate : Certificate} {state : ReservationState}
    {input : ReadyHeadInput state} {owned : List Vertex}
    {terminal : Vertex} {consumer : ConnectiveBelow certificate terminal}
    (outcome :
      ActiveMateWaitingParentExternalTemporalOutcome certificate state input
        owned consumer) :
    ActiveMateWaitingParentExternalTemporalOutcome certificate state input
      owned consumer := by
  cases outcome with
  | olderFuture boundary work older outside =>
      exact .olderFuture boundary work older outside
  | olderMarked conclusionAge marked olderRepresentative outside =>
      exact .olderMarked conclusionAge marked olderRepresentative outside

example {certificate : Certificate} {state : ReservationState}
    {input : ReadyHeadInput state} {owned : List Vertex}
    {terminal : Vertex} {consumer : ConnectiveBelow certificate terminal}
    (outcome :
      ActiveMateWaitingParentExternalTemporalOutcome certificate state input
        owned consumer) :
    ActiveCarrierParentExternalTemporalOutcome certificate state input.rawAge
      owned := by
  exact outcome.activeCarrierOutcome

example {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
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
    (waiting :
      FutureWorkActiveMateWaitingOutcome certificate state input terminal
        consumer boundary) :
    ActiveMateWaitingParentExternalTemporalOutcome certificate state input
      owned consumer := by
  exact waiting.parentExternalTemporalOutcome tagHistory invariant
    componentLookup occurrence conclusionOutside

example {certificate : Certificate} {state : ReservationState}
    {input : ReadyHeadInput state} {owned : List Vertex}
    {terminal : Vertex} {consumer : ConnectiveBelow certificate terminal}
    {boundary mateAge : RawTokenAge}
    (status :
      FutureWorkMateActiveCarrierExternalTemporalStatus certificate state input
        owned terminal consumer boundary mateAge) :
    FutureWorkMateActiveCarrierExternalTemporalStatus certificate state input
      owned terminal consumer boundary mateAge := by
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
        owned terminal consumer boundary mateAge) :
    FutureWorkMateActiveCarrierExternalTemporalStatus certificate state input
      owned terminal consumer boundary mateAge := by
  exact status.externalTemporalStatus tagHistory invariant componentLookup
    occurrence conclusionOutside

example {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {owned : List Vertex}
    {current : ConnectiveBelow certificate input.vertex} {origin : Vertex}
    (outcome :
      ContinuationExitRawOrFutureActiveCarrierExternalTemporalOutcome
        certificate state tagHistory input owned current origin) :
    ContinuationExitRawOrFutureActiveCarrierExternalTemporalOutcome certificate
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
    (invariant : SchedulerInvariant certificate state)
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      certificate.ComponentOccurrenceWitness component usedLinks owned)
    {current : ConnectiveBelow certificate input.vertex} {origin : Vertex}
    (outcome :
      ContinuationExitRawOrFutureActiveCarrierReadyMateOutcome certificate
        state tagHistory input owned current origin) :
    ContinuationExitRawOrFutureActiveCarrierExternalTemporalOutcome certificate
      state tagHistory input owned current origin := by
  exact outcome.externalTemporalOutcome invariant componentLookup occurrence

example {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {owned : List Vertex}
    {current : ConnectiveBelow certificate input.vertex}
    (target :
      ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitExternalTemporalTarget
        tagHistory input component owned current) :
    ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitExternalTemporalTarget
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
    (invariant : SchedulerInvariant certificate state)
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      certificate.ComponentOccurrenceWitness component usedLinks owned)
    (target :
      ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitReadyMateTarget
        tagHistory input component owned current) :
    ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitExternalTemporalTarget
      tagHistory input component owned current := by
  exact target.externalTemporalTarget invariant componentLookup occurrence

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
        ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitExternalTemporalTarget
            tagHistory step.prepared.readyHeadInput component owned
              step.consumer) := by
  exact step.commitmentInterval_parTraceReentryMarkedContinuationSiblingExitExternalTemporalOutcome
    correct connected tagHistory invariant componentLookup occurrence positive
      firstAt lastAt noTail

#print axioms ActiveMateWaitingParentExternalTemporalOutcome
#print axioms
  ActiveMateWaitingParentExternalTemporalOutcome.activeCarrierOutcome
#print axioms FutureWorkActiveMateWaitingOutcome.parentExternalTemporalOutcome
#print axioms FutureWorkMateActiveCarrierExternalTemporalStatus
#print axioms FutureWorkMateActiveCarrierReadyEliminatedStatus.externalTemporalStatus
#print axioms ContinuationExitRawOrFutureActiveCarrierExternalTemporalOutcome
#print axioms
  ContinuationExitRawOrFutureActiveCarrierReadyMateOutcome.externalTemporalOutcome
#print axioms
  ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitExternalTemporalTarget
open
  ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitReadyMateTarget

#print axioms externalTemporalTarget
#print axioms
  WaitStep.commitmentInterval_parTraceReentryMarkedContinuationSiblingExitExternalTemporalOutcome

end ProofNetIRMarkedTargetWaitingMateExternalTemporalTests

def main : IO Unit :=
  IO.println "Figure-7 active-mate waiting external temporal: kernel-green"
