/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7CommitmentIntervalParGuardReentryFailure
import ProofNetIR.SequentialFigure7WaitingReentryContinuationOuterContainsStatus

/-!
# Waiting re-entry continuation: stored-right marked outer split

Under an explicit stored-right orientation of the selected outer par, the
outer-containing failure status narrows to a marked historical re-entry target.
The avoiding and containing branches retain classifiers at different endpoints,
and neither classifier is identified with the common exact path or crossing.

The result eliminates neither marked target and proves no occurrence position,
first visit, payer, history-tail law, progress, completion, termination, or
totality.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerBridge

namespace FutureWorkAtExactWaitingLocation

/-- Under a stored-right current par, both outer-obstruction branches retain
marked historical re-entry targets. The containing branch keeps its membership
in the common exact waiting-mate path, but its marked-target witness remains
independent of that path and its crossing edge. -/
theorem
    activeTargetMateOuterAvoidingOrContainingReentryMarkedHistoricalTarget_of_storedRight
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
              ActiveCarrierExternalReentryMarkedHistoricalTarget
                tagHistory input component owned current.conclusion)) := by
  have base :=
    activeTargetMateOuterAvoidingReentryMarkedHistoricalTargetOrContainsFailureHistoricalStatus
      tagHistory input current currentPar correct invariant componentLookup
      occurrence consumer location targetMarked targetRepresentative
      boundaryOlder noTail
  rcases base with
    ⟨consumerPar, activeAccounted, targetOwned, mateOutside,
      currentNotProduced, currentOutside, path, directed, pathStarts,
      pathFinishes, directedMembership, sourceOutside, targetInside,
      innerAvoided, outer⟩
  refine ⟨consumerPar, activeAccounted, targetOwned, mateOutside,
    currentNotProduced, currentOutside, path, directed, pathStarts,
    pathFinishes, directedMembership, sourceOutside, targetInside,
    innerAvoided, ?_⟩
  rcases outer with avoiding | containing
  · exact Or.inl avoiding
  · rcases containing with ⟨outerMember, failureStatus⟩
    exact Or.inr ⟨outerMember,
      failureStatus.markedHistoricalTarget_of_storedRight
        invariant.structural current currentPar currentSideRight⟩

end FutureWorkAtExactWaitingLocation

end SequentialFigure7
end ProofNetIR
