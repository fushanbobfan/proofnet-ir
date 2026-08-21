/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7MarkedTargetRawReturnSiblingExitCausalOwnership

/-!
# Figure-7 sibling future-endpoint causal-ownership consumer

This runnable consumer imports only the production module under test.  It
destructs every public carrier, applies the generic causal/ownership and
active-mate scheduler theorems, upgrades a scheduled sibling outcome and
target, and consumes the typed Wait theorem.  It does not eliminate the
remaining endpoint, produce a payer, or establish a history-tail law.
-/

namespace ProofNetIR
namespace SequentialFigure7
namespace Consumer

open SequentialSchedulerState
open SequentialSchedulerBridge

private theorem markedStatusRoundTrip
    {state : ReservationState} {active : RawTokenAge} {owned : List Vertex}
    {vertex : Vertex} {rawAge : RawTokenAge}
    (status : MarkedVertexActiveCarrierStatus state active owned vertex rawAge) :
    MarkedVertexActiveCarrierStatus state active owned vertex rawAge := by
  cases status with
  | active membership representative => exact .active membership representative
  | olderOutside notMembership representativeOlder =>
      exact .olderOutside notMembership representativeOlder

private example
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (input : ReadyHeadInput state)
    (invariant : SchedulerInvariant certificate state)
    {component : UnificationComponent} {usedLinks owned : List Nat}
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component
        usedLinks owned)
    {terminal : Vertex}
    (consumer : ConnectiveBelow certificate terminal)
    {boundary : RawTokenAge}
    (work : FutureWorkAt state boundary consumer.conclusion)
    (terminalOutside : terminal ∉ owned) :
    ∃ terminalAge mateAge,
      state.core.marks[terminal]? = some (some terminalAge) ∧
        state.core.marks[consumer.mate]? = some (some mateAge) ∧
        tagHistory.RawMarked terminalAge terminal ∧
        tagHistory.RawMarked mateAge consumer.mate ∧
        state.core.representative terminalAge < input.rawAge ∧
        MarkedVertexActiveCarrierStatus state input.rawAge owned consumer.mate
          mateAge ∧
        (tagHistory.RawMarkedBefore terminalAge terminal mateAge consumer.mate ∨
          tagHistory.RawMarkedBefore mateAge consumer.mate terminalAge terminal) := by
  rcases ConnectiveBelow.futureWorkPremises_causalOwnership tagHistory input
      invariant componentLookup occurrence consumer work terminalOutside with
    ⟨terminalAge, mateAge, terminalMarked, mateMarked, terminalEvent, mateEvent,
      terminalOlder, mateStatus, premiseOrder⟩
  exact ⟨terminalAge, mateAge, terminalMarked, mateMarked, terminalEvent,
    mateEvent, terminalOlder, markedStatusRoundTrip mateStatus, premiseOrder⟩

private theorem activeMateSchedulerRoundTrip
    {certificate : Certificate} {state : ReservationState}
    {input : ReadyHeadInput state} {terminal : Vertex}
    {consumer : ConnectiveBelow certificate terminal} {boundary : RawTokenAge}
    (outcome :
      FutureWorkActiveMateSchedulerOutcome certificate state input terminal
        consumer boundary) :
    FutureWorkActiveMateSchedulerOutcome certificate state input terminal
      consumer boundary := by
  cases outcome with
  | ready sigmaAt readyAt member componentLookup frontier unmarked =>
      exact .ready sigmaAt readyAt member componentLookup frontier unmarked
  | waitingReturn waitingAt member linkLookup sourceLookup unmarked olderMarked
      youngerMarked olderBoundary boundaryOlder terminalOlder mateYounger
      youngerBoundaryActive =>
      exact .waitingReturn waitingAt member linkLookup sourceLookup unmarked
        olderMarked youngerMarked olderBoundary boundaryOlder terminalOlder
        mateYounger youngerBoundaryActive

private example
    {certificate : Certificate} {state : ReservationState}
    {input : ReadyHeadInput state} {terminal : Vertex}
    {consumer : ConnectiveBelow certificate terminal}
    {boundary terminalAge mateAge : RawTokenAge}
    (location :
      FutureWorkAtExactSchedulerLocation certificate state boundary
        consumer.conclusion)
    (invariant : SchedulerInvariant certificate state)
    (terminalMarked :
      state.core.marks[terminal]? = some (some terminalAge))
    (mateMarked :
      state.core.marks[consumer.mate]? = some (some mateAge))
    (terminalRepresentativeOlder :
      state.core.representative terminalAge < input.rawAge)
    (mateRepresentativeActive :
      state.core.representative mateAge = input.rawAge) :
    FutureWorkActiveMateSchedulerOutcome certificate state input terminal
      consumer boundary := by
  exact activeMateSchedulerRoundTrip
    (location.activeMateSchedulerOutcome invariant terminalMarked mateMarked
      terminalRepresentativeOlder mateRepresentativeActive)

private theorem mateScheduledStatusRoundTrip
    {certificate : Certificate} {state : ReservationState}
    {input : ReadyHeadInput state} {owned : List Vertex}
    {terminal : Vertex} {consumer : ConnectiveBelow certificate terminal}
    {boundary mateAge : RawTokenAge}
    (status :
      FutureWorkMateActiveCarrierScheduledStatus certificate state input owned
        terminal consumer boundary mateAge) :
    FutureWorkMateActiveCarrierScheduledStatus certificate state input owned
      terminal consumer boundary mateAge := by
  cases status with
  | olderOutside notMembership representativeOlder =>
      exact .olderOutside notMembership representativeOlder
  | active membership representative scheduler =>
      exact .active membership representative
        (activeMateSchedulerRoundTrip scheduler)

private theorem causalOwnershipOutcomeRoundTrip
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {owned : List Vertex}
    {current : ConnectiveBelow certificate input.vertex} {origin : Vertex}
    (outcome :
      ContinuationExitRawOrFutureActiveCarrierCausalOwnershipOutcome certificate
        state tagHistory input owned current origin) :
    ContinuationExitRawOrFutureActiveCarrierCausalOwnershipOutcome certificate
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
        (mateScheduledStatusRoundTrip mateStatus) premiseOrder location

private example
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {usedLinks owned : List Nat}
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component
        usedLinks owned)
    {current : ConnectiveBelow certificate input.vertex} {origin : Vertex}
    (outcome :
      ContinuationExitRawOrFutureActiveCarrierScheduledOutcome certificate state
        input owned current origin)
    (invariant : SchedulerInvariant certificate state) :
    ContinuationExitRawOrFutureActiveCarrierCausalOwnershipOutcome certificate
      state tagHistory input owned current origin := by
  exact causalOwnershipOutcomeRoundTrip
    (outcome.causalOwnershipOutcome componentLookup occurrence invariant)

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
    (target :
      ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitScheduledTarget
        tagHistory input component owned current) :
    ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitCausalOwnershipTarget
      tagHistory input component owned current := by
  exact target.causalOwnershipTarget invariant componentLookup occurrence

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
        ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitCausalOwnershipTarget
            tagHistory step.prepared.readyHeadInput component owned
              step.consumer) := by
  exact
    step.commitmentInterval_parTraceReentryMarkedContinuationSiblingExitCausalOwnershipOutcome
      correct connected tagHistory invariant componentLookup occurrence positive
      firstAt lastAt noTail

#print axioms MarkedVertexActiveCarrierStatus
#print axioms ConnectiveBelow.futureWorkPremises_causalOwnership
#print axioms FutureWorkActiveMateSchedulerOutcome
#print axioms FutureWorkAtExactSchedulerLocation.activeMateSchedulerOutcome
#print axioms FutureWorkMateActiveCarrierScheduledStatus
#print axioms ContinuationExitRawOrFutureActiveCarrierCausalOwnershipOutcome
#print axioms
  ContinuationExitRawOrFutureActiveCarrierScheduledOutcome.causalOwnershipOutcome
#print axioms
  ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitCausalOwnershipTarget

end Consumer

namespace ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitScheduledTarget
#print axioms causalOwnershipTarget
end ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitScheduledTarget

#print axioms
  WaitStep.commitmentInterval_parTraceReentryMarkedContinuationSiblingExitCausalOwnershipOutcome

end SequentialFigure7
end ProofNetIR

def main : IO Unit :=
  IO.println "Figure-7 sibling future-endpoint causal ownership: kernel-green"
