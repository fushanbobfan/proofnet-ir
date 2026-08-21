/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7WaitingReentryContinuationMateAvoiding

/-!
# Waiting re-entry continuation: outer obstruction

The result retains one common exact older-mate-to-target re-entry path, its
crossing edge, and its inner waiting-conclusion avoidance before splitting on
the selected outer par conclusion. In the avoiding branch, the historical
classifier is obtained separately from the same re-entry evidence; its
existential interface does not expose classifier-path identity with the common
exact path.

Containment means only list membership in `path.vertices`. It does not locate
an occurrence, establish a first visit, eliminate the obstruction, recover a
payer or tail law, or prove progress, completion, termination, or totality.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerBridge

namespace FutureWorkAtExactWaitingLocation

/-- Retains one common exact waiting-mate re-entry path before the outer split.
The avoiding branch separately obtains a historical classifier whose interface
does not expose classifier-path identity. The containing branch states only
vertex-list membership and proves no elimination, payer, tail law, progress,
completion, termination, or totality. -/
theorem activeTargetMateOuterAvoidingReentryMarkedHistoricalTargetOrContains
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
            current.conclusion ∈ path.vertices) := by
  rcases location.activeTargetMateAlignedAvoidingReentry correct invariant
      componentLookup occurrence consumer targetMarked targetRepresentative
      boundaryOlder with
    ⟨consumerPar, activeAccounted, targetOwned, mateOutside, path, directed,
      pathStarts, pathFinishes, directedMembership, sourceOutside,
      targetInside, innerAvoided⟩
  refine ⟨consumerPar, activeAccounted, targetOwned, mateOutside, path,
    directed, pathStarts, pathFinishes, directedMembership, sourceOutside,
    targetInside, innerAvoided, ?_⟩
  by_cases outerContained : current.conclusion ∈ path.vertices
  · exact Or.inr outerContained
  · have finishOwned : path.finish ∈ owned := by
      simpa [pathFinishes] using targetOwned
    have reentry :
        ActiveCarrierExternalEndpointReentryAvoiding certificate owned
          consumer.mate current.conclusion :=
      ⟨path, directed, pathStarts, finishOwned, directedMembership,
        sourceOutside, targetInside, outerContained⟩
    have historicalTarget := reentry.markedHistoricalTarget tagHistory input
      invariant current currentPar componentLookup occurrence activeAccounted
      noTail
    exact Or.inl ⟨outerContained, historicalTarget⟩

end FutureWorkAtExactWaitingLocation

end SequentialFigure7
end ProofNetIR
