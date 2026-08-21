/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7MarkedTargetRawReturnSiblingExitReadyMateElimination
import ProofNetIR.SequentialFigure7ActiveTopDebtParentTemporalOutcome

/-!
# Figure-7 active-mate waiting parent recursion

Turns the active-owned waiting case left by ready-mate elimination into an
authenticated parent-escape temporal outcome. The waiting mate is a marked,
non-global active-frontier premise distinct from the selected ready head, and
its submitted conclusion lies outside the active occurrence carrier. Existing
parent-escape normalization therefore supplies the recursive temporal status.

The result refines the future-sibling exit and its typed Wait trace target. A
mate outside the active carrier keeps the existing strictly older status. The
checkpoint does not eliminate the active waiting return or the older outside
case, prove repeated parent normalization well-founded, produce a ready-tail
payer, derive the history-tail law, or establish completion or progress.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge
open Certificate.OccurrenceDerivation

private theorem connectiveMateMembership
    {certificate : Certificate} {vertex : Vertex}
    (consumer : ConnectiveBelow certificate vertex) :
    consumer.mate ∈ consumer.submittedLink.premises := by
  cases kindEq : consumer.kind <;> cases sideEq : consumer.side <;>
    simp [ConnectiveBelow.mate, ConnectiveBelow.submittedLink,
      SequentialConnectiveKind.asLink, Link.premises,
      TensorPremiseSide.mate, kindEq, sideEq]

private theorem connectiveMatePairMembership
    {certificate : Certificate} {vertex : Vertex}
    (consumer : ConnectiveBelow certificate vertex) :
    consumer.mate ∈ [consumer.storedLeft, consumer.storedRight] := by
  cases sideEq : consumer.side <;>
    simp [ConnectiveBelow.mate, TensorPremiseSide.mate, sideEq]

private theorem readyHeadVertex_mem_queued
    {state : ReservationState} (input : ReadyHeadInput state) :
    input.vertex ∈ state.stack.queuedVertices := by
  unfold SequentialStackState.queuedVertices
  apply List.mem_append_left
  apply List.mem_flatten.mpr
  exact ⟨input.vertex :: input.readyTail,
    List.mem_of_getLast? input.top_ready, by simp⟩

private theorem connectiveSubmitted
    {certificate : Certificate} {vertex : Vertex}
    (consumer : ConnectiveBelow certificate vertex) :
    certificate.links[consumer.linkIndex]? =
        some (.tensor consumer.storedLeft consumer.storedRight
          consumer.conclusion) ∨
      certificate.links[consumer.linkIndex]? =
        some (.par consumer.storedLeft consumer.storedRight
          consumer.conclusion) := by
  cases kindEq : consumer.kind with
  | tensor =>
      left
      simpa [ConnectiveBelow.submittedLink,
        SequentialConnectiveKind.asLink, kindEq] using consumer.link_eq
  | par =>
      right
      simpa [ConnectiveBelow.submittedLink,
        SequentialConnectiveKind.asLink, kindEq] using consumer.link_eq

private theorem activeOccurrence_accounted
    {certificate : Certificate} {state : ReservationState}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {usedLinks owned : List Nat}
    (invariant : SchedulerInvariant certificate state)
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      certificate.ComponentOccurrenceWitness component usedLinks owned) :
    Certificate.OwnedOccurrenceAccounted state.core input.rawAge component
      owned := by
  rcases invariant.component_forest_provenance with
    ⟨usedAt, ownedAt, live, separated, markedOwned⟩
  have facts := live componentLookup
  have ownedEq : owned = ownedAt input.rawAge :=
    Certificate.OccurrenceDerivation.owned_unique invariant.structural
      occurrence.derivation facts.1.derivation
  simpa [ownedEq] using facts.2

/-- Rebuild an active-owned waiting future mate as a parent escape from the
active occurrence carrier. -/
theorem FutureWorkActiveMateWaitingOutcome.activeCarrierParentEscape
    {certificate : Certificate} {state : ReservationState}
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
  cases waiting with
  | @waitingReturn payload linkIndex left right olderPremise youngerPremise
      olderAge youngerAge waitingAt member linkLookup sourceLookup unmarked
      olderMarked youngerMarked olderBoundary boundaryOlder terminalOlder
      mateYounger youngerBoundaryActive =>
      have mateMarked :
          state.core.marks[consumer.mate]? = some (some youngerAge) := by
        simpa [mateYounger] using youngerMarked
      have mateNeSelected : consumer.mate ≠ input.vertex := by
        intro same
        have selectedUnmarked :=
          queuedUnmarked input.vertex (readyHeadVertex_mem_queued input)
        rw [← same, mateMarked] at selectedUnmarked
        simp at selectedUnmarked
      have mateFrontier : consumer.mate ∈ component.frontier :=
        Classical.byContradiction fun mateNotFrontier ↦ conclusionOutside
          (connectiveConclusion_owned_of_premise_owned_not_frontier
            structural occurrence.derivation
              (connectiveSubmitted consumer)
              (connectiveMatePairMembership consumer)
              mateActive mateNotFrontier)
      refine ⟨consumer.mate, youngerAge, consumer.linkIndex, consumer.kind,
        consumer.storedLeft, consumer.storedRight, consumer.conclusion,
        mateNeSelected, mateFrontier, mateMarked, ?_, consumer.link_eq, ?_,
        conclusionOutside⟩
      · exact submittedPremise_not_conclusion structural
          consumer.link_eq (connectiveMateMembership consumer)
      · exact connectiveMateMembership consumer

/-- Normalize an active-owned waiting future mate through the existing
no-ready-tail parent temporal outcome. -/
theorem FutureWorkActiveMateWaitingOutcome.parentTemporalOutcome
    {certificate : Certificate} {state : ReservationState}
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
  have escape := waiting.activeCarrierParentEscape invariant.structural
    invariant.queued_vertices_unmarked occurrence conclusionOutside mateActive
  have residual := escape.temporalResidual_of_no_readyTail tagHistory correct
    input invariant componentLookup occurrence
      (activeOccurrence_accounted invariant componentLookup occurrence) noTail
  exact residual.temporalOutcome invariant componentLookup

/-- Ready-eliminated future-mate status with the active waiting branch exposed
as a recursive parent temporal outcome. -/
inductive FutureWorkMateActiveCarrierParentRecursionStatus
    (certificate : Certificate) (state : ReservationState)
    (input : ReadyHeadInput state) (owned : List Vertex)
    (terminal : Vertex) (consumer : ConnectiveBelow certificate terminal)
    (boundary mateAge : RawTokenAge) : Prop where
  | olderOutside
      (notMembership : consumer.mate ∉ owned)
      (representativeOlder :
        state.core.representative mateAge < input.rawAge) :
      FutureWorkMateActiveCarrierParentRecursionStatus certificate state
        input owned terminal consumer boundary mateAge
  | activeParent
      (membership : consumer.mate ∈ owned)
      (representative :
        state.core.representative mateAge = input.rawAge)
      (waiting :
        FutureWorkActiveMateWaitingOutcome certificate state input terminal
          consumer boundary)
      (recursive :
        ActiveCarrierParentTemporalOutcome certificate state input.rawAge
          input.vertex owned) :
      FutureWorkMateActiveCarrierParentRecursionStatus certificate state
        input owned terminal consumer boundary mateAge

/-- Refine ready-mate elimination by normalizing its active waiting branch to
the parent temporal interface. -/
theorem FutureWorkMateActiveCarrierReadyEliminatedStatus.parentRecursionStatus
    {certificate : Certificate} {state : ReservationState}
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
  cases status with
  | olderOutside notMembership representativeOlder =>
      exact .olderOutside notMembership representativeOlder
  | activeWaiting membership representative waiting =>
      exact .activeParent membership representative waiting
        (waiting.parentTemporalOutcome tagHistory correct invariant
          componentLookup occurrence conclusionOutside membership noTail)

/-- Raw-or-future sibling exit after refining every active-owned future mate
to a recursive parent temporal outcome. -/
inductive ContinuationExitRawOrFutureActiveCarrierParentRecursionOutcome
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
      ContinuationExitRawOrFutureActiveCarrierParentRecursionOutcome
        certificate state tagHistory input owned current origin
  | rawSelectedReturn {terminal : Vertex}
      (chain : MarkedConclusionChain certificate state origin terminal)
      (terminalOutside : terminal ∉ owned)
      (consumer : ConnectiveBelow certificate terminal)
      (mateUnmarked : state.core.marks[consumer.mate]? = some none)
      (mateSelected : consumer.mate = input.vertex)
      (terminalCurrentMate : terminal = current.mate)
      (conclusionCurrent : consumer.conclusion = current.conclusion) :
      ContinuationExitRawOrFutureActiveCarrierParentRecursionOutcome
        certificate state tagHistory input owned current origin
  | futureOlder {terminal : Vertex}
      (chain : MarkedConclusionChain certificate state origin terminal)
      (terminalOutside : terminal ∉ owned)
      (consumer : ConnectiveBelow certificate terminal)
      (boundary : RawTokenAge)
      (work : FutureWorkAt state boundary consumer.conclusion)
      (conclusionOutside : consumer.conclusion ∉ owned)
      (boundaryOlder : boundary < input.rawAge)
      (terminalAge mateAge : RawTokenAge)
      (terminalMarked :
        state.core.marks[terminal]? = some (some terminalAge))
      (mateMarked :
        state.core.marks[consumer.mate]? = some (some mateAge))
      (terminalEvent : tagHistory.RawMarked terminalAge terminal)
      (mateEvent : tagHistory.RawMarked mateAge consumer.mate)
      (terminalRepresentativeOlder :
        state.core.representative terminalAge < input.rawAge)
      (mateStatus :
        FutureWorkMateActiveCarrierParentRecursionStatus certificate state
          input owned terminal consumer boundary mateAge)
      (premiseOrder :
        tagHistory.RawMarkedBefore terminalAge terminal mateAge consumer.mate ∨
          tagHistory.RawMarkedBefore mateAge consumer.mate terminalAge terminal)
      (location :
        FutureWorkAtExactSchedulerLocation certificate state boundary
          consumer.conclusion) :
      ContinuationExitRawOrFutureActiveCarrierParentRecursionOutcome
        certificate state tagHistory input owned current origin

/-- Lift parent-recursion refinement across a ready-mate-eliminated sibling
exit. -/
theorem ContinuationExitRawOrFutureActiveCarrierReadyMateOutcome.parentRecursionOutcome
    {certificate : Certificate} {state : ReservationState}
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
        (mateStatus.parentRecursionStatus tagHistory correct invariant
          componentLookup occurrence conclusionOutside noTail)
        premiseOrder location

/-- Causal-ownership target whose first-descending sibling exit records active
waiting as a recursive parent temporal outcome. -/
def ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitParentRecursionTarget
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
                    ContinuationExitRawOrFutureActiveCarrierParentRecursionOutcome
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
  ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitReadyMateTarget

/-- Refine the causal sibling branch of the ready-mate target to the recursive
parent temporal target. -/
theorem parentRecursionTarget
    {certificate : Certificate} {state : ReservationState}
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
      siblingOutcome.parentRecursionOutcome correct invariant
        componentLookup occurrence noTail,
      causalOutcome⟩)
  · exact Or.inr (Or.inr (Or.inl future))
  · exact Or.inr (Or.inr (Or.inr marked))

end
  ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitReadyMateTarget

namespace CanonicalTagHistory

private theorem CommitmentIntervalParTraceOutcome.mapParentRecursionStatus
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

/-- In the strictly older Wait branch, normalize every active-owned waiting
future sibling mate to its parent temporal outcome. -/
theorem commitmentInterval_parTraceReentryMarkedContinuationSiblingExitParentRecursionOutcome
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
        ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitParentRecursionTarget
            tagHistory step.prepared.readyHeadInput component owned
              step.consumer) := by
  apply CanonicalTagHistory.CommitmentIntervalParTraceOutcome.mapParentRecursionStatus
    (step.commitmentInterval_parTraceReentryMarkedContinuationSiblingExitReadyMateOutcome
      correct connected tagHistory invariant componentLookup occurrence positive
        firstAt lastAt noTail)
  intro status
  rcases status with ⟨mateOutside, mateMarked, representativeOlder, target⟩
  exact ⟨mateOutside, mateMarked, representativeOlder,
    target.parentRecursionTarget correct invariant componentLookup
      occurrence noTail⟩

end WaitStep

end SequentialFigure7
end ProofNetIR
