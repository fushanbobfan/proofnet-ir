/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7WaitingReentryContinuationOuterContainsMarkedStoredRight

/-!
# Figure-7 waiting re-entry stored-right marked outer-split consumer

Reconstructs the exact stored-right refinement through the public surface,
checks its trust boundary, and executes a kernel-green marker.
-/

namespace ProofNetIRWaitingReentryContinuationOuterContainsMarkedStoredRightTests

open ProofNetIR
open ProofNetIR.SequentialSchedulerState
open ProofNetIR.SequentialSchedulerBridge
open ProofNetIR.SequentialFigure7
open ProofNetIR.SequentialFigure7.FutureWorkAtExactWaitingLocation

example {certificate : Certificate} {state : ReservationState}
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
  exact
    activeTargetMateOuterAvoidingOrContainingReentryMarkedHistoricalTarget_of_storedRight
      tagHistory input current currentPar currentSideRight correct invariant
      componentLookup occurrence consumer location targetMarked
      targetRepresentative boundaryOlder noTail

#print axioms
  activeTargetMateOuterAvoidingOrContainingReentryMarkedHistoricalTarget_of_storedRight

end ProofNetIRWaitingReentryContinuationOuterContainsMarkedStoredRightTests

def main : IO Unit :=
  IO.println
    "Figure-7 waiting re-entry stored-right marked outer split: kernel-green"
