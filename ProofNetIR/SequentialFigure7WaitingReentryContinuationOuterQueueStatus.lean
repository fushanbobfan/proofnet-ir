/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7FutureWorkQueueStatus
import
  ProofNetIR.SequentialFigure7MarkedTargetWaitingMateExternalCommitmentReentryContinuationWaiting
import ProofNetIR.SequentialFigure7WaitingReentryContinuationOuterContainsMarkedStoredRight

/-!
# Waiting re-entry continuation: outer queue status

This module refines the raw-unmarked leaf of each stored-right marked outer
target with its current scheduler status. It preserves the common exact waiting
path and its crossing. Each disjunct retains only its branch-local classifier
at that branch's endpoint; it does not supply simultaneous classifiers.

The classifier supplies neither a unique boundary nor historical, persistence,
elimination, payer, progress, completion, termination, or totality evidence.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerBridge

/-- A normalized external marked parent whose remaining raw-unmarked mate has
its current scheduler status, while the exact initialized-waiting alternative
is preserved unchanged. -/
def ActiveCarrierExternalReentryMarkedOuterMateSeparatedWaitingParentQueueStatusTarget
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (input : ReadyHeadInput state) (component : UnificationComponent)
    (owned : List Vertex) (endpoint : Vertex)
    (current : ConnectiveBelow certificate input.vertex) : Prop :=
  ∃ (path : certificate.referenceSwitchingGraph.EdgeSimplePath)
      (directed : certificate.referenceSwitchingGraph.DirectedEdge)
      (markedAge : RawTokenAge),
    path.start = endpoint ∧
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
          (UnmarkedOutsideActiveSchedulerStatus certificate state input owned
              targetConsumer.mate ∨
            ∃ boundary,
              FutureWorkAt state boundary targetConsumer.conclusion ∧
                boundary < input.rawAge ∧
                FutureWorkAtExactWaitingLocation certificate state boundary
                  targetConsumer.conclusion)

namespace ActiveCarrierExternalReentryMarkedOuterMateSeparatedWaitingParentTarget

/-- Refine the raw-unmarked outside leaf of a waiting-parent target with its
current scheduler status. -/
theorem queueStatusTarget
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {usedLinks owned : List Nat} {endpoint : Vertex}
    (invariant : SchedulerInvariant certificate state)
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      certificate.ComponentOccurrenceWitness component usedLinks owned)
    {current : ConnectiveBelow certificate input.vertex}
    (target :
      ActiveCarrierExternalReentryMarkedOuterMateSeparatedWaitingParentTarget
        tagHistory input component owned endpoint current) :
    ActiveCarrierExternalReentryMarkedOuterMateSeparatedWaitingParentQueueStatusTarget
      tagHistory input component owned endpoint current := by
  rcases target with
    ⟨path, directed, markedAge, pathStarts, finishOwned, directedMembership,
      parentEdge, targetNeSelected, targetNeMate, targetMarked, authentic,
      representativeEq, targetConsumer, targetConsumerMateNeSelected,
      sourceConsumer, targetConclusionOutside, status⟩
  refine ⟨path, directed, markedAge, pathStarts, finishOwned,
    directedMembership, parentEdge, targetNeSelected, targetNeMate,
    targetMarked, authentic, representativeEq, targetConsumer,
    targetConsumerMateNeSelected, sourceConsumer, targetConclusionOutside, ?_⟩
  rcases status with raw | waiting
  · exact Or.inl
      (invariant.unmarkedOutsideActiveSchedulerStatus input componentLookup
        occurrence raw.1 raw.2)
  · exact Or.inr waiting

end ActiveCarrierExternalReentryMarkedOuterMateSeparatedWaitingParentTarget

namespace FutureWorkAtExactWaitingLocation

/-- Under a stored-right current par and an outside current mate, refine each
marked outer branch to a waiting-parent queue-status target while preserving
the common exact path and crossing evidence. Each disjunct retains only the
branch-local classifier at its own endpoint, not simultaneous classifiers. -/
theorem activeTargetMateOuterWaitingParentQueueStatus_of_storedRight
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (input : ReadyHeadInput state)
    (current : ConnectiveBelow certificate input.vertex)
    (currentPar : current.kind = .par)
    (currentSideRight : current.side = .storedRight)
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate state)
    {component : UnificationComponent} {usedLinks owned : List Nat}
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      certificate.ComponentOccurrenceWitness component usedLinks owned)
    (currentMateOutside : current.mate ∉ owned)
    {boundary targetAge : RawTokenAge} {target : Vertex}
    (consumer : ConnectiveBelow certificate target)
    (location :
      FutureWorkAtExactWaitingLocation certificate state boundary
        consumer.conclusion)
    (targetMarked : state.core.marks[target]? = some (some targetAge))
    (targetRepresentative :
      state.core.representative targetAge = input.rawAge)
    (boundaryOlder : boundary < input.rawAge)
    (noTail :
      ¬ ∃ pending,
        pending ∈ input.readyTail ∧ pending ∉ certificate.conclusions) :
    consumer.kind = .par ∧
      Certificate.OwnedOccurrenceAccounted
        state.core input.rawAge component owned ∧
      target ∈ owned ∧
      consumer.mate ∉ owned ∧
      ¬ Produced state current.conclusion ∧
      current.conclusion ∉ owned ∧
      ∃ (path : certificate.referenceSwitchingGraph.EdgeSimplePath)
          (directed : certificate.referenceSwitchingGraph.DirectedEdge),
        path.start = consumer.mate ∧
          path.finish = target ∧
          directed ∈ path.traversed ∧
          directed.source ∉ owned ∧
          directed.target ∈ owned ∧
          consumer.conclusion ∉ path.vertices ∧
          ((current.conclusion ∉ path.vertices ∧
              ActiveCarrierExternalReentryMarkedOuterMateSeparatedWaitingParentQueueStatusTarget
                tagHistory input component owned consumer.mate current) ∨
            (current.conclusion ∈ path.vertices ∧
              ActiveCarrierExternalReentryMarkedOuterMateSeparatedWaitingParentQueueStatusTarget
                tagHistory input component owned current.conclusion current)) := by
  rcases
      location.activeTargetMateOuterAvoidingOrContainingReentryMarkedHistoricalTarget_of_storedRight
        tagHistory input current currentPar currentSideRight correct invariant
        componentLookup occurrence consumer targetMarked targetRepresentative
        boundaryOlder noTail with
    ⟨consumerPar, activeAccounted, targetOwned, mateOutside,
      currentNotProduced, currentOutside, path, directed, pathStarts,
      pathFinishes, directedMembership, sourceOutside, targetInside,
      innerAvoided, outer⟩
  refine ⟨consumerPar, activeAccounted, targetOwned, mateOutside,
    currentNotProduced, currentOutside, path, directed, pathStarts,
    pathFinishes, directedMembership, sourceOutside, targetInside,
    innerAvoided, ?_⟩
  rcases outer with avoiding | containing
  · rcases avoiding with ⟨outerAvoided, historicalTarget⟩
    have temporalTarget :=
      historicalTarget.outerMateSeparatedTemporalTarget invariant current
        componentLookup occurrence currentMateOutside noTail
    have continuationTarget :=
      temporalTarget.continuationExitTarget invariant current componentLookup
        occurrence noTail
    have waitingTarget :=
      continuationTarget.waitingParentTarget invariant componentLookup occurrence
    exact Or.inl ⟨outerAvoided,
      waitingTarget.queueStatusTarget invariant componentLookup occurrence⟩
  · rcases containing with ⟨outerMember, historicalTarget⟩
    have temporalTarget :=
      historicalTarget.outerMateSeparatedTemporalTarget invariant current
        componentLookup occurrence currentMateOutside noTail
    have continuationTarget :=
      temporalTarget.continuationExitTarget invariant current componentLookup
        occurrence noTail
    have waitingTarget :=
      continuationTarget.waitingParentTarget invariant componentLookup occurrence
    exact Or.inr ⟨outerMember,
      waitingTarget.queueStatusTarget invariant componentLookup occurrence⟩

end FutureWorkAtExactWaitingLocation
end SequentialFigure7
end ProofNetIR
