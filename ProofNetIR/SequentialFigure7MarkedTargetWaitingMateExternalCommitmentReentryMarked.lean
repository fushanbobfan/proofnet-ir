/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7MarkedTargetWaitingMateExternalCommitmentReentry
import ProofNetIR.SequentialFigure7CommitmentIntervalParGuardReentryFailure

/-!
# Figure-7 stored-right waiting re-entry marked target

The stored-right branch of an outer par interval eliminates the selected-head
alternative from each failure-conditioned historical re-entry status retained
by an active waiting mate. The surviving target is therefore a distinct,
canonical-history-authenticated mark at the active representative. This module
propagates that refinement through the exact external waiting endpoints, the
future-work mate status, the continuation sibling exit, and the typed Wait
commitment-interval trace.

The outer avoiding and equal-final selected/mate trace branches are preserved,
as are the older-outside mate, raw-outside, and selected-return alternatives
that do not contain the refined failure status. The older-future and
older-marked endpoint shapes are retained while their failure field is
strengthened. The causal-descent and cyclic-junction receipts are transported
unchanged.

This is a target-classification refinement. It does not eliminate the remaining
marked target, identify it with an outer mate or payer, equate arbitrary stored
crossing and re-entry witnesses, derive the history-tail law, or establish
completion, progress, termination, or totality.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge

/-- The exact two-case waiting-parent endpoint after the stored-right guard has
eliminated the selected-head re-entry target and retained the authenticated
marked target. -/
inductive ActiveMateWaitingParentExternalCommitmentReentryMarkedOutcome
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (input : ReadyHeadInput state) (component : UnificationComponent)
    (owned : List Vertex) {terminal : Vertex}
    (consumer : ConnectiveBelow certificate terminal) : Prop where
  | olderFuture
      (boundary : RawTokenAge)
      (work : FutureWorkAt state boundary consumer.conclusion)
      (older : boundary < input.rawAge)
      (outside : consumer.conclusion ∉ owned)
      (commitmentSplit :
        tagHistory.StrictOlderCommitmentSplit boundary input.rawAge)
      (crossing :
        ActiveCarrierExternalEndpointCrossing certificate owned
          consumer.conclusion)
      (reentry :
        ActiveCarrierExternalEndpointReentry certificate owned
          consumer.conclusion)
      (markedTarget :
        ActiveCarrierExternalReentryMarkedHistoricalTarget tagHistory input
          component owned consumer.conclusion) :
      ActiveMateWaitingParentExternalCommitmentReentryMarkedOutcome tagHistory
        input component owned consumer
  | olderMarked
      (conclusionAge : RawTokenAge)
      (marked :
        state.core.marks[consumer.conclusion]? = some (some conclusionAge))
      (olderRepresentative :
        state.core.representative conclusionAge < input.rawAge)
      (outside : consumer.conclusion ∉ owned)
      (commitmentSplit : tagHistory.StrictOlderCommitmentSplit
        (state.core.representative conclusionAge) input.rawAge)
      (crossing :
        ActiveCarrierExternalEndpointCrossing certificate owned
          consumer.conclusion)
      (reentry :
        ActiveCarrierExternalEndpointReentry certificate owned
          consumer.conclusion)
      (markedTarget :
        ActiveCarrierExternalReentryMarkedHistoricalTarget tagHistory input
          component owned consumer.conclusion) :
      ActiveMateWaitingParentExternalCommitmentReentryMarkedOutcome tagHistory
        input component owned consumer

namespace ActiveMateWaitingParentExternalCommitmentReentryFailureOutcome

/-- Refine either exact waiting endpoint by using the enclosing stored-right
par guard to eliminate its selected-head failure target. -/
theorem markedOutcome_of_storedRight
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {owned : List Vertex}
    {terminal : Vertex} {consumer : ConnectiveBelow certificate terminal}
    (outcome :
      ActiveMateWaitingParentExternalCommitmentReentryFailureOutcome tagHistory
        input component owned consumer)
    (structural : certificate.StructurallyWellFormed)
    (current : ConnectiveBelow certificate input.vertex)
    (parEq : current.kind = .par)
    (sideRight : current.side = .storedRight) :
    ActiveMateWaitingParentExternalCommitmentReentryMarkedOutcome tagHistory
      input component owned consumer := by
  cases outcome with
  | olderFuture boundary work older outside commitmentSplit crossing reentry
      failureStatus =>
      exact .olderFuture boundary work older outside commitmentSplit crossing
        reentry
        (failureStatus.markedHistoricalTarget_of_storedRight structural current
          parEq sideRight)
  | olderMarked conclusionAge marked olderRepresentative outside
      commitmentSplit crossing reentry failureStatus =>
      exact .olderMarked conclusionAge marked olderRepresentative outside
        commitmentSplit crossing reentry
        (failureStatus.markedHistoricalTarget_of_storedRight structural current
          parEq sideRight)

end ActiveMateWaitingParentExternalCommitmentReentryFailureOutcome

/-- The future-work mate split with an unchanged older-outside branch and an
active-owned branch whose waiting endpoint has a marked historical re-entry
target. -/
inductive FutureWorkMateActiveCarrierExternalCommitmentReentryMarkedStatus
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (input : ReadyHeadInput state) (component : UnificationComponent)
    (owned : List Vertex) (terminal : Vertex)
    (consumer : ConnectiveBelow certificate terminal)
    (boundary mateAge : RawTokenAge) : Prop where
  | olderOutside
      (notMembership : consumer.mate ∉ owned)
      (representativeOlder :
        state.core.representative mateAge < input.rawAge) :
      FutureWorkMateActiveCarrierExternalCommitmentReentryMarkedStatus
        tagHistory input component owned terminal consumer boundary mateAge
  | activeExternal
      (membership : consumer.mate ∈ owned)
      (representative :
        state.core.representative mateAge = input.rawAge)
      (waiting :
        FutureWorkActiveMateWaitingOutcome certificate state input terminal
          consumer boundary)
      (external :
        ActiveMateWaitingParentExternalCommitmentReentryMarkedOutcome tagHistory
          input component owned consumer) :
      FutureWorkMateActiveCarrierExternalCommitmentReentryMarkedStatus
        tagHistory input component owned terminal consumer boundary mateAge

namespace FutureWorkMateActiveCarrierExternalTemporalStatus

/-- Refine the active-owned future-work mate branch under the enclosing
stored-right par guard; preserve the older-outside branch verbatim. -/
theorem commitmentReentryMarkedStatus_of_storedRight
    {certificate : Certificate} {state : ReservationState}
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
    (status :
      FutureWorkMateActiveCarrierExternalTemporalStatus certificate state input
        owned terminal consumer boundary mateAge) :
    FutureWorkMateActiveCarrierExternalCommitmentReentryMarkedStatus tagHistory
      input component owned terminal consumer boundary mateAge := by
  cases status with
  | olderOutside notMembership representativeOlder =>
      exact .olderOutside notMembership representativeOlder
  | activeExternal membership representative waiting external =>
      have failure :=
        external.commitmentReentryFailureOutcome tagHistory connected invariant
          componentLookup occurrence noTail
      exact .activeExternal membership representative waiting
        (failure.markedOutcome_of_storedRight invariant.structural current parEq
          sideRight)

end FutureWorkMateActiveCarrierExternalTemporalStatus

/-- A continuation exit that preserves the raw exits and refines only the
future-work mate status to its stored-right marked-target form. -/
inductive ContinuationExitRawOrFutureActiveCarrierExternalCommitmentReentryMarkedOutcome
    (certificate : Certificate) (state : ReservationState)
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (input : ReadyHeadInput state) (component : UnificationComponent)
    (owned : List Vertex) (current : ConnectiveBelow certificate input.vertex)
    (origin : Vertex) : Prop where
  | rawOutside {terminal : Vertex}
      (chain : MarkedConclusionChain certificate state origin terminal)
      (terminalOutside : terminal ∉ owned)
      (consumer : ConnectiveBelow certificate terminal)
      (mateUnmarked : state.core.marks[consumer.mate]? = some none)
      (mateOutside : consumer.mate ∉ owned) :
      ContinuationExitRawOrFutureActiveCarrierExternalCommitmentReentryMarkedOutcome
        certificate state tagHistory input component owned current origin
  | rawSelectedReturn {terminal : Vertex}
      (chain : MarkedConclusionChain certificate state origin terminal)
      (terminalOutside : terminal ∉ owned)
      (consumer : ConnectiveBelow certificate terminal)
      (mateUnmarked : state.core.marks[consumer.mate]? = some none)
      (mateSelected : consumer.mate = input.vertex)
      (terminalCurrentMate : terminal = current.mate)
      (conclusionCurrent : consumer.conclusion = current.conclusion) :
      ContinuationExitRawOrFutureActiveCarrierExternalCommitmentReentryMarkedOutcome
        certificate state tagHistory input component owned current origin
  | futureOlder {terminal : Vertex}
      (chain : MarkedConclusionChain certificate state origin terminal)
      (terminalOutside : terminal ∉ owned)
      (consumer : ConnectiveBelow certificate terminal)
      (boundary : RawTokenAge)
      (work : FutureWorkAt state boundary consumer.conclusion)
      (conclusionOutside : consumer.conclusion ∉ owned)
      (boundaryOlder : boundary < input.rawAge)
      (terminalAge mateAge : RawTokenAge)
      (terminalMarked : state.core.marks[terminal]? = some (some terminalAge))
      (mateMarked :
        state.core.marks[consumer.mate]? = some (some mateAge))
      (terminalEvent : tagHistory.RawMarked terminalAge terminal)
      (mateEvent : tagHistory.RawMarked mateAge consumer.mate)
      (terminalRepresentativeOlder :
        state.core.representative terminalAge < input.rawAge)
      (mateStatus :
        FutureWorkMateActiveCarrierExternalCommitmentReentryMarkedStatus
          tagHistory input component owned terminal consumer boundary mateAge)
      (premiseOrder :
        tagHistory.RawMarkedBefore terminalAge terminal mateAge consumer.mate ∨
          tagHistory.RawMarkedBefore mateAge consumer.mate terminalAge terminal)
      (location :
        FutureWorkAtExactSchedulerLocation certificate state boundary
          consumer.conclusion) :
      ContinuationExitRawOrFutureActiveCarrierExternalCommitmentReentryMarkedOutcome
        certificate state tagHistory input component owned current origin

namespace ContinuationExitRawOrFutureActiveCarrierExternalTemporalOutcome

/-- Refine the future-work branch of an external temporal continuation under
the enclosing stored-right par guard while preserving both raw exits. -/
theorem commitmentReentryMarkedOutcome_of_storedRight
    {certificate : Certificate} {state : ReservationState}
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
    (outcome :
      ContinuationExitRawOrFutureActiveCarrierExternalTemporalOutcome
        certificate state tagHistory input owned current origin) :
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
        (mateStatus.commitmentReentryMarkedStatus_of_storedRight tagHistory
          connected invariant componentLookup occurrence current parEq sideRight
          noTail)
        premiseOrder location

end ContinuationExitRawOrFutureActiveCarrierExternalTemporalOutcome

/-- The external temporal sibling-exit target with its causal continuation
refined to retain a stored-right marked historical re-entry target. -/
def ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitWaitingMarkedTarget
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (input : ReadyHeadInput state) (component : UnificationComponent)
    (owned : List Vertex) (current : ConnectiveBelow certificate input.vertex) :
    Prop :=
  ∃ (outerAge : RawTokenAge),
    tagHistory.RawMarked outerAge current.mate ∧
      ∃ (path : certificate.referenceSwitchingGraph.EdgeSimplePath)
          (directed : certificate.referenceSwitchingGraph.DirectedEdge)
          (markedAge : RawTokenAge),
        path.start = current.mate ∧
          path.finish ∈ owned ∧
          directed ∈ path.traversed ∧
          ActiveCarrierInboundParentEdge certificate component owned directed ∧
          directed.target ≠ input.vertex ∧
          directed.target ≠ current.mate ∧
          state.core.marks[directed.target]? = some (some markedAge) ∧
          tagHistory.RawMarked markedAge directed.target ∧
          state.core.representative markedAge = input.rawAge ∧
          ∃ targetConsumer : ConnectiveBelow certificate directed.target,
            targetConsumer.mate ≠ input.vertex ∧
            directed.source = targetConsumer.conclusion ∧
            targetConsumer.conclusion ∉ owned ∧
            ((∃ terminal,
                MarkedConclusionChain certificate state directed.target
                    terminal ∧
                  ∃ terminalConsumer : ConnectiveBelow certificate terminal,
                    state.core.marks[terminalConsumer.mate]? = some none ∧
                    terminalConsumer.mate ∉ owned) ∨
              (MarkedConclusionChainFirstCausalDescent certificate state
                  tagHistory directed.target current.mate input.rawAge ∧
                ∃ (consumer : ConnectiveBelow certificate directed.target)
                    (mateAge : RawTokenAge),
                  tagHistory.RawMarkedBefore mateAge consumer.mate outerAge
                      current.mate ∧
                    ContinuationExitRawOrFutureActiveCarrierExternalCommitmentReentryMarkedOutcome
                        certificate state tagHistory input component owned current
                          consumer.conclusion ∧
                      MarkedConclusionRawReturnCyclicJunctionCausalOutcome
                        certificate state tagHistory current.mate
                          consumer.conclusion outerAge) ∨
              (∃ terminal,
                MarkedConclusionChain certificate state directed.target
                    terminal ∧
                  ∃ terminalConsumer : ConnectiveBelow certificate terminal,
                    ∃ boundary,
                      FutureWorkAt state boundary terminalConsumer.conclusion ∧
                      terminalConsumer.conclusion ∉ owned ∧
                      boundary < input.rawAge) ∨
              ∃ terminal,
                MarkedConclusionChain certificate state directed.target terminal ∧
                  ∃ terminalConsumer : ConnectiveBelow certificate terminal,
                    ∃ conclusionAge,
                      state.core.marks[terminalConsumer.conclusion]? =
                          some (some conclusionAge) ∧
                        terminalConsumer.conclusion ∈ certificate.conclusions ∧
                        terminalConsumer.conclusion ∉ owned ∧
                        state.core.representative conclusionAge < input.rawAge)

namespace
  ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitExternalTemporalTarget

/-- Refine only the causal-continuation branch of the external temporal sibling
target; preserve its raw, future, marked, and causal/cyclic receipt evidence. -/
theorem waitingMarkedTarget_of_storedRight
    {certificate : Certificate} {state : ReservationState}
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
  rcases target with
    ⟨outerAge, outerEvent, path, directed, markedAge, pathStart, pathFinish,
      directedMembership, inbound, targetNeSelected, targetNeMate, targetMarked,
      targetEvent, targetRepresentative, targetConsumer, targetMateNeSelected,
      directedSource, conclusionOutside, exit⟩
  refine ⟨outerAge, outerEvent, path, directed, markedAge, pathStart, pathFinish,
    directedMembership, inbound, targetNeSelected, targetNeMate, targetMarked,
    targetEvent, targetRepresentative, targetConsumer, targetMateNeSelected,
    directedSource, conclusionOutside, ?_⟩
  rcases exit with raw | causal | future | marked
  · exact Or.inl raw
  · rcases causal with
      ⟨descent, consumer, mateAge, mateBeforeOuter, siblingOutcome,
        causalOutcome⟩
    exact Or.inr (Or.inl ⟨descent, consumer, mateAge, mateBeforeOuter,
      siblingOutcome.commitmentReentryMarkedOutcome_of_storedRight connected
        invariant componentLookup occurrence parEq sideRight noTail,
      causalOutcome⟩)
  · exact Or.inr (Or.inr (Or.inl future))
  · exact Or.inr (Or.inr (Or.inr marked))

end
  ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitExternalTemporalTarget

namespace CanonicalTagHistory

private theorem CommitmentIntervalParTraceOutcome.mapExternalCommitmentReentryMarkedStatus
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state}
    {consumer : ConnectiveBelow certificate input.vertex}
    {position edgeCount : Nat} {first : RawTokenAge}
    {beforeStatus afterStatus : Prop}
    (outcome : tagHistory.CommitmentIntervalParTraceOutcome input consumer
      position edgeCount first beforeStatus)
    (mapStatus :
      consumer.side = .storedRight → beforeStatus → afterStatus) :
    tagHistory.CommitmentIntervalParTraceOutcome input consumer position
      edgeCount first afterStatus := by
  cases outcome with
  | avoiding path => exact .avoiding path
  | equalSelected offset parent child event offsetLt parentAt childAt
      notAvoiding membership eventAge childEq side beforeTrace afterTrace trace =>
      exact .equalSelected offset parent child event offsetLt parentAt childAt
        notAvoiding membership eventAge childEq side beforeTrace afterTrace trace
  | equalMate offset parent child event offsetLt parentAt childAt notAvoiding
      membership eventAge childEq side beforeTrace afterTrace trace =>
      exact .equalMate offset parent child event offsetLt parentAt childAt
        notAvoiding membership eventAge childEq side beforeTrace afterTrace trace
  | olderMate offset parent child event offsetLt parentAt childAt notAvoiding
      membership eventAge childLt side beforeTrace afterTrace trace status =>
      exact .olderMate offset parent child event offsetLt parentAt childAt
        notAvoiding membership eventAge childLt side beforeTrace afterTrace trace
        (mapStatus side status)

end CanonicalTagHistory

namespace WaitStep

/-- Lift the stored-right marked-target refinement to the older-mate status of
the typed Wait commitment-interval trace, leaving every other trace branch
unchanged. -/
theorem commitmentInterval_parTraceReentryMarkedContinuationSiblingExitWaitingMarkedOutcome
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
        ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitWaitingMarkedTarget
            tagHistory step.prepared.readyHeadInput component owned
              step.consumer) := by
  apply
    CanonicalTagHistory.CommitmentIntervalParTraceOutcome.mapExternalCommitmentReentryMarkedStatus
      (step.commitmentInterval_parTraceReentryMarkedContinuationSiblingExitExternalTemporalOutcome
        correct connected tagHistory invariant componentLookup occurrence
          positive firstAt lastAt noTail)
  intro side status
  rcases status with ⟨mateOutside, mateMarked, representativeOlder, target⟩
  exact ⟨mateOutside, mateMarked, representativeOlder,
    target.waitingMarkedTarget_of_storedRight connected invariant
      componentLookup occurrence step.par_eq side noTail⟩

end WaitStep

end SequentialFigure7
end ProofNetIR
