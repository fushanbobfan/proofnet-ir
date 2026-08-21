/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7MarkedTargetWaitingMateExternalCommitmentReentryTemporal

/-!
# Figure-7 waiting re-entry temporal normalization consumer

Consumes every public declaration in the endpoint-parametric temporal
normalization checkpoint. Each carrier is reconstructed, each refinement
theorem is invoked, and the typed Wait lift is exercised directly.
-/

namespace ProofNetIRMarkedTargetWaitingMateExternalCommitmentReentryTemporalTests

open ProofNetIR
open ProofNetIR.SequentialSchedulerState
open ProofNetIR.SequentialSchedulerBridge
open ProofNetIR.SequentialFigure7

example {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {owned : List Vertex} {endpoint : Vertex}
    {current : ConnectiveBelow certificate input.vertex}
    (target : ActiveCarrierExternalReentryMarkedOuterMateSeparatedTemporalTarget
      tagHistory input component owned endpoint current) :
    ActiveCarrierExternalReentryMarkedOuterMateSeparatedTemporalTarget
      tagHistory input component owned endpoint current := by
  rcases target with
    ⟨path, directed, markedAge, pathStarts, finishOwned, directedMembership,
      parentEdge, targetNeSelected, targetNeMate, targetMarked, authentic,
      representativeEq, targetConsumer, mateNeSelected, sourceConsumer,
      conclusionOutside, raw | future | marked⟩
  · rcases raw with ⟨mateUnmarked, mateOutside⟩
    exact ⟨path, directed, markedAge, pathStarts, finishOwned,
      directedMembership, parentEdge, targetNeSelected, targetNeMate,
      targetMarked, authentic, representativeEq, targetConsumer,
      mateNeSelected, sourceConsumer, conclusionOutside,
      Or.inl ⟨mateUnmarked, mateOutside⟩⟩
  · rcases future with ⟨boundary, work, older⟩
    exact ⟨path, directed, markedAge, pathStarts, finishOwned,
      directedMembership, parentEdge, targetNeSelected, targetNeMate,
      targetMarked, authentic, representativeEq, targetConsumer,
      mateNeSelected, sourceConsumer, conclusionOutside,
      Or.inr (Or.inl ⟨boundary, work, older⟩)⟩
  · rcases marked with ⟨conclusionAge, conclusionMarked, older⟩
    exact ⟨path, directed, markedAge, pathStarts, finishOwned,
      directedMembership, parentEdge, targetNeSelected, targetNeMate,
      targetMarked, authentic, representativeEq, targetConsumer,
      mateNeSelected, sourceConsumer, conclusionOutside,
      Or.inr (Or.inr ⟨conclusionAge, conclusionMarked, older⟩)⟩

example {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {usedLinks owned : List Nat} {endpoint : Vertex}
    (invariant : SchedulerInvariant certificate state)
    (current : ConnectiveBelow certificate input.vertex)
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component
        usedLinks owned)
    (mateOutside : current.mate ∉ owned)
    (target : ActiveCarrierExternalReentryMarkedHistoricalTarget tagHistory
      input component owned endpoint)
    (noTail :
      ¬ ∃ pending,
        pending ∈ input.readyTail ∧ pending ∉ certificate.conclusions) :
    ActiveCarrierExternalReentryMarkedOuterMateSeparatedTemporalTarget
      tagHistory input component owned endpoint current := by
  exact target.outerMateSeparatedTemporalTarget invariant current
    componentLookup occurrence mateOutside noTail

example {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {owned : List Vertex} {current : ConnectiveBelow certificate input.vertex}
    {terminal : Vertex} {consumer : ConnectiveBelow certificate terminal}
    (outcome : ActiveMateWaitingParentExternalCommitmentReentryTemporalOutcome
      tagHistory input component owned current consumer) :
    ActiveMateWaitingParentExternalCommitmentReentryTemporalOutcome
      tagHistory input component owned current consumer := by
  cases outcome with
  | olderFuture boundary work older outside commitmentSplit crossing reentry
      temporalTarget =>
      exact .olderFuture boundary work older outside commitmentSplit crossing
        reentry temporalTarget
  | olderMarked conclusionAge marked olderRepresentative outside
      commitmentSplit crossing reentry temporalTarget =>
      exact .olderMarked conclusionAge marked olderRepresentative outside
        commitmentSplit crossing reentry temporalTarget

example {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {usedLinks owned : List Nat}
    {terminal : Vertex} {consumer : ConnectiveBelow certificate terminal}
    (outcome : ActiveMateWaitingParentExternalCommitmentReentryMarkedOutcome
      tagHistory input component owned consumer)
    (invariant : SchedulerInvariant certificate state)
    (current : ConnectiveBelow certificate input.vertex)
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component
        usedLinks owned)
    (mateOutside : current.mate ∉ owned)
    (noTail :
      ¬ ∃ pending,
        pending ∈ input.readyTail ∧ pending ∉ certificate.conclusions) :
    ActiveMateWaitingParentExternalCommitmentReentryTemporalOutcome
      tagHistory input component owned current consumer := by
  exact outcome.temporalOutcome invariant current componentLookup occurrence
    mateOutside noTail

example {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {owned : List Vertex} {current : ConnectiveBelow certificate input.vertex}
    {terminal : Vertex} {consumer : ConnectiveBelow certificate terminal}
    {boundary mateAge : RawTokenAge}
    (status :
      FutureWorkMateActiveCarrierExternalCommitmentReentryTemporalStatus
        tagHistory input component owned current terminal consumer boundary
          mateAge) :
    FutureWorkMateActiveCarrierExternalCommitmentReentryTemporalStatus
      tagHistory input component owned current terminal consumer boundary
        mateAge := by
  cases status with
  | olderOutside notMembership representativeOlder =>
      exact .olderOutside notMembership representativeOlder
  | activeExternal membership representative waiting external =>
      exact .activeExternal membership representative waiting external

example {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {usedLinks owned : List Nat}
    {terminal : Vertex} {consumer : ConnectiveBelow certificate terminal}
    {boundary mateAge : RawTokenAge}
    (status :
      FutureWorkMateActiveCarrierExternalCommitmentReentryMarkedStatus
        tagHistory input component owned terminal consumer boundary mateAge)
    (invariant : SchedulerInvariant certificate state)
    (current : ConnectiveBelow certificate input.vertex)
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component
        usedLinks owned)
    (mateOutside : current.mate ∉ owned)
    (noTail :
      ¬ ∃ pending,
        pending ∈ input.readyTail ∧ pending ∉ certificate.conclusions) :
    FutureWorkMateActiveCarrierExternalCommitmentReentryTemporalStatus
      tagHistory input component owned current terminal consumer boundary
        mateAge := by
  exact status.temporalStatus invariant current componentLookup occurrence
    mateOutside noTail

example {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {owned : List Vertex}
    {current : ConnectiveBelow certificate input.vertex} {origin : Vertex}
    (outcome :
      ContinuationExitRawOrFutureActiveCarrierExternalCommitmentReentryTemporalOutcome
        certificate state tagHistory input component owned current origin) :
    ContinuationExitRawOrFutureActiveCarrierExternalCommitmentReentryTemporalOutcome
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
    {current : ConnectiveBelow certificate input.vertex} {origin : Vertex}
    (outcome :
      ContinuationExitRawOrFutureActiveCarrierExternalCommitmentReentryMarkedOutcome
        certificate state tagHistory input component owned current origin)
    (invariant : SchedulerInvariant certificate state)
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component
        usedLinks owned)
    (mateOutside : current.mate ∉ owned)
    (noTail :
      ¬ ∃ pending,
        pending ∈ input.readyTail ∧ pending ∉ certificate.conclusions) :
    ContinuationExitRawOrFutureActiveCarrierExternalCommitmentReentryTemporalOutcome
      certificate state tagHistory input component owned current origin := by
  exact outcome.temporalOutcome invariant componentLookup occurrence
    mateOutside noTail

example {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {owned : List Vertex}
    {current : ConnectiveBelow certificate input.vertex}
    (target :
      ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitWaitingTemporalTarget
        tagHistory input component owned current) :
    ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitWaitingTemporalTarget
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
    (target :
      ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitWaitingMarkedTarget
        tagHistory input component owned current)
    (invariant : SchedulerInvariant certificate state)
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component
        usedLinks owned)
    (mateOutside : current.mate ∉ owned)
    (noTail :
      ¬ ∃ pending,
        pending ∈ input.readyTail ∧ pending ∉ certificate.conclusions) :
    ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitWaitingTemporalTarget
      tagHistory input component owned current := by
  exact target.temporalTarget invariant componentLookup occurrence mateOutside
    noTail

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
        ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitWaitingTemporalTarget
            tagHistory step.prepared.readyHeadInput component owned
              step.consumer) := by
  exact
    step.commitmentInterval_parTraceReentryMarkedContinuationSiblingExitWaitingTemporalOutcome
      correct connected tagHistory invariant componentLookup occurrence
        positive firstAt lastAt noTail

#print axioms
  ActiveCarrierExternalReentryMarkedHistoricalTarget.outerMateSeparatedTemporalTarget
#print axioms
  ActiveMateWaitingParentExternalCommitmentReentryMarkedOutcome.temporalOutcome
#print axioms
  FutureWorkMateActiveCarrierExternalCommitmentReentryMarkedStatus.temporalStatus
#print axioms
  ContinuationExitRawOrFutureActiveCarrierExternalCommitmentReentryMarkedOutcome.temporalOutcome
open
  ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitWaitingMarkedTarget

#print axioms temporalTarget
#print axioms
  WaitStep.commitmentInterval_parTraceReentryMarkedContinuationSiblingExitWaitingTemporalOutcome

end ProofNetIRMarkedTargetWaitingMateExternalCommitmentReentryTemporalTests

def main : IO Unit :=
  IO.println "Figure-7 waiting re-entry temporal normalization: kernel-green"
