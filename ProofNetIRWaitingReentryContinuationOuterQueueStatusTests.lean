/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7WaitingReentryContinuationOuterQueueStatus

/-!
# Waiting re-entry continuation outer queue-status consumer

Reconstructs the public adapter and stored-right lift, checks every new trust
boundary, and emits a kernel-green marker.
-/

namespace ProofNetIRWaitingReentryContinuationOuterQueueStatusTests

open ProofNetIR
open ProofNetIR.SequentialSchedulerState
open ProofNetIR.SequentialSchedulerBridge
open ProofNetIR.SequentialFigure7

example {certificate : Certificate} {state : ReservationState}
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
  exact target.queueStatusTarget invariant componentLookup occurrence

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
  exact
    location.activeTargetMateOuterWaitingParentQueueStatus_of_storedRight
      tagHistory input current currentPar currentSideRight correct invariant
      componentLookup occurrence currentMateOutside consumer targetMarked
      targetRepresentative boundaryOlder noTail

end ProofNetIRWaitingReentryContinuationOuterQueueStatusTests

namespace ProofNetIR
namespace SequentialFigure7

#print axioms
  ActiveCarrierExternalReentryMarkedOuterMateSeparatedWaitingParentQueueStatusTarget

namespace ActiveCarrierExternalReentryMarkedOuterMateSeparatedWaitingParentTarget
#print axioms queueStatusTarget
end ActiveCarrierExternalReentryMarkedOuterMateSeparatedWaitingParentTarget

namespace FutureWorkAtExactWaitingLocation
#print axioms activeTargetMateOuterWaitingParentQueueStatus_of_storedRight
end FutureWorkAtExactWaitingLocation

end SequentialFigure7
end ProofNetIR

def main : IO Unit :=
  IO.println "Figure-7 waiting re-entry outer queue status: kernel-green"
