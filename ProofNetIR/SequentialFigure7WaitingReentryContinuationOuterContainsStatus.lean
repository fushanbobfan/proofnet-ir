/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7CommitmentEdgeTargetAvoidance
import ProofNetIR.SequentialFigure7WaitingReentryContinuationOuterObstruction

/-!
# Waiting re-entry continuation: outer-containing historical status

The outer-containing branch keeps membership in the common exact waiting-mate
path and derives an independent failure-conditioned historical re-entry status
from the outer conclusion. The status existential may use a suffix and a new
boundary edge; no identity with the retained common crossing is asserted.

The result eliminates neither branch and proves no payer, history-tail law,
progress, completion, termination, or totality.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerBridge

namespace FutureWorkAtExactWaitingLocation

/-- Strengthens the outer-containing branch with a failure-conditioned
historical status at the outer conclusion while retaining its membership in
the common exact waiting-mate path. The status does not expose witness identity
with that common path or its crossing edge. -/
theorem
    activeTargetMateOuterAvoidingReentryMarkedHistoricalTargetOrContainsFailureHistoricalStatus
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (input : ReadyHeadInput state)
    (current : ConnectiveBelow certificate input.vertex)
    (currentPar : current.kind = .par)
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate state)
    {component : UnificationComponent} {usedLinks owned : List Nat}
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      certificate.ComponentOccurrenceWitness component usedLinks owned)
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
              ActiveCarrierExternalReentryMarkedHistoricalTarget
                tagHistory input component owned consumer.mate) ∨
            (current.conclusion ∈ path.vertices ∧
              ActiveCarrierExternalReentryFailureHistoricalStatus
                tagHistory input component owned current.conclusion)) := by
  rcases
      location.activeTargetMateOuterAvoidingReentryMarkedHistoricalTargetOrContains
        tagHistory input current currentPar correct invariant componentLookup
        occurrence consumer targetMarked targetRepresentative boundaryOlder
        noTail with
    ⟨consumerPar, activeAccounted, targetOwned, mateOutside, path, directed,
      pathStarts, pathFinishes, directedMembership, sourceOutside,
      targetInside, innerAvoided, obstruction⟩
  have currentNotProduced : ¬ Produced state current.conclusion :=
    input.connectiveConclusion_not_produced invariant current
  have currentOutside : current.conclusion ∉ owned :=
    input.connectiveConclusion_not_owned_of_accounted invariant current
      componentLookup activeAccounted
  rcases obstruction with avoiding | contains
  · exact ⟨consumerPar, activeAccounted, targetOwned, mateOutside,
      currentNotProduced, currentOutside, path, directed, pathStarts,
      pathFinishes, directedMembership, sourceOutside, targetInside,
      innerAvoided, Or.inl avoiding⟩
  · have currentNotFinish : current.conclusion ≠ path.finish := by
      intro currentFinish
      apply currentOutside
      rw [currentFinish, pathFinishes]
      exact targetOwned
    rcases path.outgoingAtVertex contains currentNotFinish with
      ⟨before, next, after, traversalEquation, nextSource⟩
    rcases path.suffixPath traversalEquation with
      ⟨suffix, suffixStarts, suffixFinishes, _suffixTraversal,
        _suffixSubset⟩
    have suffixStartsCurrent : suffix.start = current.conclusion :=
      suffixStarts.trans nextSource
    have suffixFinishOwned : suffix.finish ∈ owned := by
      rw [suffixFinishes, pathFinishes]
      exact targetOwned
    have suffixStartOutside : suffix.start ∉ owned := by
      simpa [suffixStartsCurrent] using currentOutside
    have finishMembership : suffix.finish ∈ suffix.vertices := by
      simpa [Graph.EdgeSimplePath.vertices] using
        suffix.walk.finish_mem_visitedVertices
    have finishInside : (!(owned.contains suffix.finish)) = false := by
      simp [suffixFinishOwned]
    rcases suffix.exists_traversed_boundary_of_start_true
        (fun vertex ↦ !(owned.contains vertex))
        (by simpa using suffixStartOutside)
        ⟨suffix.finish, finishMembership, finishInside⟩ with
      ⟨boundaryEdge, boundaryMembership, boundarySourceOutside,
        boundaryTargetInside⟩
    have reentry :
        ActiveCarrierExternalEndpointReentry certificate owned
          current.conclusion :=
      ⟨suffix, boundaryEdge, suffixStartsCurrent, suffixFinishOwned,
        boundaryMembership, by simpa using boundarySourceOutside,
        by simpa using boundaryTargetInside⟩
    have historicalStatus :=
      reentry.targetFailureHistoricalStatus tagHistory input invariant
        componentLookup occurrence activeAccounted noTail
    exact ⟨consumerPar, activeAccounted, targetOwned, mateOutside,
      currentNotProduced, currentOutside, path, directed, pathStarts,
      pathFinishes, directedMembership, sourceOutside, targetInside,
      innerAvoided, Or.inr ⟨contains, historicalStatus⟩⟩

end FutureWorkAtExactWaitingLocation

end SequentialFigure7
end ProofNetIR
