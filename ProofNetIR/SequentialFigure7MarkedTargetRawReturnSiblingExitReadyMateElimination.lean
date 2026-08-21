/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7MarkedTargetRawReturnSiblingExitCausalOwnership

/-!
# Figure-7 active-mate ready-endpoint elimination

Eliminates the ready scheduler case when an older future sibling endpoint has
an active-owned mate. Exact ready-component occurrence provenance would then
own both submitted premises at the older boundary, while the active occurrence
carrier owns the same mate at the active boundary. Live-carrier disjointness
contradicts the strict boundary order.

The surviving active-owned case is the already oriented waiting return from an
older terminal to the active mate. A mate outside the active carrier retains
its existing older representative and may still belong to ready or waiting
work. The result eliminates one scheduler subcase; it does not eliminate the
future endpoint, construct a payer, derive the history-tail law, or prove
completion or progress.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge

private theorem connectiveBelow_mate_owned
    {certificate : Certificate} (structural : certificate.StructurallyWellFormed)
    {tree : CutFreeDerivation} {frontier usedLinks owned : List Nat}
    (witness : certificate.OccurrenceDerivation tree frontier usedLinks owned)
    {vertex : Vertex} (consumer : ConnectiveBelow certificate vertex)
    (conclusionOwned : consumer.conclusion ∈ owned) :
    consumer.mate ∈ owned := by
  have premises := witness.connectivePremises_owned_of_conclusion_owned
    structural conclusionOwned
      (by
        cases kindEq : consumer.kind with
        | tensor =>
            left
            simpa [ConnectiveBelow.submittedLink,
              SequentialConnectiveKind.asLink, kindEq] using consumer.link_eq
        | par =>
            right
            simpa [ConnectiveBelow.submittedLink,
              SequentialConnectiveKind.asLink, kindEq] using consumer.link_eq)
  cases kindEq : consumer.kind <;> cases sideEq : consumer.side <;>
    simp [ConnectiveBelow.mate, TensorPremiseSide.mate, sideEq]
      at premises ⊢
  · exact premises.2
  · exact premises.1
  · exact premises.2
  · exact premises.1

/-- Exact waiting-return semantics left after eliminating ready work for an
active-owned future-endpoint mate. -/
inductive FutureWorkActiveMateWaitingOutcome
    (certificate : Certificate) (state : ReservationState)
    (input : ReadyHeadInput state) (terminal : Vertex)
    (consumer : ConnectiveBelow certificate terminal)
    (boundary : RawTokenAge) : Prop where
  | waitingReturn {payload : List Vertex} {linkIndex : Nat}
      {left right olderPremise youngerPremise : Vertex}
      {olderAge youngerAge : RawTokenAge}
      (waitingAt : state.stack.waiting[boundary]? =
        some (.initialized payload))
      (member : consumer.conclusion ∈ payload)
      (linkLookup :
        certificate.links[linkIndex]? =
          some (.par left right consumer.conclusion))
      (sourceLookup :
        (SequentialUnification.sourceIndex certificate)[consumer.conclusion]? =
          some [{ linkIndex := linkIndex, link := .par left right consumer.conclusion }])
      (unmarked : state.core.marks[consumer.conclusion]? = some none)
      (olderMarked :
        state.core.marks[olderPremise]? = some (some olderAge))
      (youngerMarked :
        state.core.marks[youngerPremise]? = some (some youngerAge))
      (olderBoundary :
        sigmaBoundary? state.stack.sigma olderAge = some boundary)
      (boundaryOlder : boundary < input.rawAge)
      (terminalOlder : terminal = olderPremise)
      (mateYounger : consumer.mate = youngerPremise)
      (youngerBoundaryActive :
        sigmaBoundary? state.stack.sigma youngerAge = some input.rawAge) :
      FutureWorkActiveMateWaitingOutcome certificate state input terminal
        consumer boundary

/-- An active-owned mate rules out the ready scheduler alternative at a
strictly older future-work boundary. -/
theorem FutureWorkActiveMateSchedulerOutcome.waitingOutcome_of_activeOwned
    {certificate : Certificate} {state : ReservationState}
    {input : ReadyHeadInput state} {activeComponent : UnificationComponent}
    {activeUsed activeOwned : List Nat}
    (invariant : SchedulerInvariant certificate state)
    (activeLookup :
      state.core.components[input.rawAge]? = some (some activeComponent))
    (activeOccurrence :
      certificate.ComponentOccurrenceWitness activeComponent activeUsed activeOwned)
    {terminal : Vertex} {consumer : ConnectiveBelow certificate terminal}
    {boundary : RawTokenAge}
    (mateActive : consumer.mate ∈ activeOwned)
    (boundaryOlder : boundary < input.rawAge)
    (scheduler :
      FutureWorkActiveMateSchedulerOutcome certificate state input terminal
        consumer boundary) :
    FutureWorkActiveMateWaitingOutcome certificate state input terminal
      consumer boundary := by
  cases scheduler with
  | ready sigmaAt readyAt member componentLookup frontier unmarked =>
      rcases invariant.component_forest_provenance with
        ⟨usedAt, ownedAt, live, separated, markedOwned⟩
      have activeFacts := live activeLookup
      have activeOwnedEq : activeOwned = ownedAt input.rawAge :=
        Certificate.OccurrenceDerivation.owned_unique invariant.structural
          activeOccurrence.derivation activeFacts.1.derivation
      have mateActiveAt : consumer.mate ∈ ownedAt input.rawAge := by
        rwa [← activeOwnedEq]
      have endpointFacts := live componentLookup
      have conclusionOwned : consumer.conclusion ∈ ownedAt boundary :=
        endpointFacts.1.derivation.frontier_subset_owned _ frontier
      have mateBoundary : consumer.mate ∈ ownedAt boundary :=
        connectiveBelow_mate_owned invariant.structural
          endpointFacts.1.derivation consumer conclusionOwned
      have different : boundary ≠ input.rawAge := Nat.ne_of_lt boundaryOlder
      exact False.elim
        ((separated componentLookup activeLookup different).2 consumer.mate
          mateBoundary mateActiveAt)
  | waitingReturn waitingAt member linkLookup sourceLookup unmarked
      olderMarked youngerMarked olderBoundary boundaryOlder' terminalOlder
      mateYounger youngerBoundaryActive =>
      exact .waitingReturn waitingAt member linkLookup sourceLookup unmarked
        olderMarked youngerMarked olderBoundary boundaryOlder' terminalOlder
        mateYounger youngerBoundaryActive

/-- The future-endpoint mate is older outside the active carrier or is an
active-owned exact waiting return. -/
inductive FutureWorkMateActiveCarrierReadyEliminatedStatus
    (certificate : Certificate) (state : ReservationState)
    (input : ReadyHeadInput state) (owned : List Vertex)
    (terminal : Vertex) (consumer : ConnectiveBelow certificate terminal)
    (boundary mateAge : RawTokenAge) : Prop where
  | olderOutside
      (notMembership : consumer.mate ∉ owned)
      (representativeOlder :
        state.core.representative mateAge < input.rawAge) :
      FutureWorkMateActiveCarrierReadyEliminatedStatus certificate state input
        owned terminal consumer boundary mateAge
  | activeWaiting
      (membership : consumer.mate ∈ owned)
      (representative :
        state.core.representative mateAge = input.rawAge)
      (scheduler :
        FutureWorkActiveMateWaitingOutcome certificate state input terminal
          consumer boundary) :
      FutureWorkMateActiveCarrierReadyEliminatedStatus certificate state input
        owned terminal consumer boundary mateAge

/-- Remove the active-owned ready alternative from the scheduled mate status. -/
theorem FutureWorkMateActiveCarrierScheduledStatus.readyEliminatedStatus
    {certificate : Certificate} {state : ReservationState}
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
    (status :
      FutureWorkMateActiveCarrierScheduledStatus certificate state input owned
        terminal consumer boundary mateAge) :
    FutureWorkMateActiveCarrierReadyEliminatedStatus certificate state input
      owned terminal consumer boundary mateAge := by
  cases status with
  | olderOutside notMembership representativeOlder =>
      exact .olderOutside notMembership representativeOlder
  | active membership representative scheduler =>
      exact .activeWaiting membership representative
        (scheduler.waitingOutcome_of_activeOwned invariant componentLookup
          occurrence membership boundaryOlder)

/-- A causal sibling exit after eliminating ready work only from the
active-owned future-mate branch. -/
inductive ContinuationExitRawOrFutureActiveCarrierReadyMateOutcome
    (certificate : Certificate) (state : ReservationState)
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (input : ReadyHeadInput state) (owned : List Vertex)
    (current : ConnectiveBelow certificate input.vertex)
    (origin : Vertex) : Prop where
  | rawOutside {terminal : Vertex}
      (chain : MarkedConclusionChain certificate state origin terminal)
      (terminalOutside : terminal ∉ owned)
      (consumer : ConnectiveBelow certificate terminal)
      (mateUnmarked : state.core.marks[consumer.mate]? = some none)
      (mateOutside : consumer.mate ∉ owned) :
      ContinuationExitRawOrFutureActiveCarrierReadyMateOutcome certificate
        state tagHistory input owned current origin
  | rawSelectedReturn {terminal : Vertex}
      (chain : MarkedConclusionChain certificate state origin terminal)
      (terminalOutside : terminal ∉ owned)
      (consumer : ConnectiveBelow certificate terminal)
      (mateUnmarked : state.core.marks[consumer.mate]? = some none)
      (mateSelected : consumer.mate = input.vertex)
      (terminalCurrentMate : terminal = current.mate)
      (conclusionCurrent : consumer.conclusion = current.conclusion) :
      ContinuationExitRawOrFutureActiveCarrierReadyMateOutcome certificate
        state tagHistory input owned current origin
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
        FutureWorkMateActiveCarrierReadyEliminatedStatus certificate state
          input owned terminal consumer boundary mateAge)
      (premiseOrder :
        tagHistory.RawMarkedBefore terminalAge terminal mateAge consumer.mate ∨
          tagHistory.RawMarkedBefore mateAge consumer.mate terminalAge terminal)
      (location :
        FutureWorkAtExactSchedulerLocation certificate state boundary
          consumer.conclusion) :
      ContinuationExitRawOrFutureActiveCarrierReadyMateOutcome certificate
        state tagHistory input owned current origin

/-- Refine causal/ownership sibling exits by removing the active-owned ready
future-mate case. -/
theorem ContinuationExitRawOrFutureActiveCarrierCausalOwnershipOutcome.readyMateOutcome
    {certificate : Certificate} {state : ReservationState}
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
      ContinuationExitRawOrFutureActiveCarrierCausalOwnershipOutcome certificate
        state tagHistory input owned current origin) :
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
        mateMarked terminalEvent mateEvent terminalRepresentativeOlder
        (mateStatus.readyEliminatedStatus invariant componentLookup occurrence
          boundaryOlder)
        premiseOrder location

/-- The marked re-entry target after eliminating the active-owned ready
future-mate subcase. -/
def ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitReadyMateTarget
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
                    ContinuationExitRawOrFutureActiveCarrierReadyMateOutcome
                        certificate state tagHistory input owned current
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
  ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitCausalOwnershipTarget

/-- Upgrade the causal/ownership target to its ready-mate-eliminated form. -/
theorem readyMateTarget
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
      certificate.ComponentOccurrenceWitness component usedLinks owned)
    (target :
      ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitCausalOwnershipTarget
        tagHistory input component owned current) :
    ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitReadyMateTarget
      tagHistory input component owned current := by
  rcases target with
    ⟨outerAge, outerEvent, path, directed, markedAge, pathStart, finishOwned,
      directedMembership, parentEdge, targetNeSelected, targetNeMate,
      targetMarked, targetEvent, representativeEq, targetConsumer,
      targetConsumerMateNeSelected, sourceConsumer, targetConclusionOutside,
      status⟩
  refine ⟨outerAge, outerEvent, path, directed, markedAge, pathStart,
    finishOwned, directedMembership, parentEdge, targetNeSelected,
    targetNeMate, targetMarked, targetEvent, representativeEq, targetConsumer,
    targetConsumerMateNeSelected, sourceConsumer, targetConclusionOutside, ?_⟩
  rcases status with raw | descent | future | marked
  · exact Or.inl raw
  · rcases descent with
      ⟨descent, consumer, mateAge, mateBeforeOuter, siblingOutcome,
        causalOutcome⟩
    exact Or.inr (Or.inl ⟨descent, consumer, mateAge, mateBeforeOuter,
      siblingOutcome.readyMateOutcome invariant componentLookup occurrence,
      causalOutcome⟩)
  · exact Or.inr (Or.inr (Or.inl future))
  · exact Or.inr (Or.inr (Or.inr marked))

end ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitCausalOwnershipTarget

namespace CanonicalTagHistory

private theorem CommitmentIntervalParTraceOutcome.mapReadyMateStatus
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state}
    {consumer : ConnectiveBelow certificate input.vertex}
    {position edgeCount : Nat} {first : RawTokenAge}
    {beforeStatus afterStatus : Prop}
    (outcome : tagHistory.CommitmentIntervalParTraceOutcome input consumer
      position edgeCount first beforeStatus)
    (mapStatus : beforeStatus → afterStatus) :
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
      membership eventAge childEq side beforeTrace afterTrace trace status =>
      exact .olderMate offset parent child event offsetLt parentAt childAt
        notAvoiding membership eventAge childEq side beforeTrace afterTrace trace
        (mapStatus status)

end CanonicalTagHistory

namespace WaitStep

/-- In the strictly older Wait branch, remove the active-owned ready
future-mate case from every retained sibling exit. -/
theorem commitmentInterval_parTraceReentryMarkedContinuationSiblingExitReadyMateOutcome
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
        ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitReadyMateTarget
            tagHistory step.prepared.readyHeadInput component owned
              step.consumer) := by
  apply CanonicalTagHistory.CommitmentIntervalParTraceOutcome.mapReadyMateStatus
    (step.commitmentInterval_parTraceReentryMarkedContinuationSiblingExitCausalOwnershipOutcome
      correct connected tagHistory invariant componentLookup occurrence positive
        firstAt lastAt noTail)
  intro status
  rcases status with ⟨mateOutside, mateMarked, representativeOlder, target⟩
  exact ⟨mateOutside, mateMarked, representativeOlder,
    target.readyMateTarget invariant componentLookup occurrence⟩

end WaitStep

end SequentialFigure7
end ProofNetIR
