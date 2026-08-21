/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7WaitingReentryContinuationProducerOrientation

/-!
# Figure-7 waiting re-entry producer-orientation consumer

Invokes the exact waiting-location orientation theorem through its public
surface and checks its trust boundary.
-/

namespace ProofNetIRWaitingReentryContinuationProducerOrientationTests

open ProofNetIR
open ProofNetIR.SequentialSchedulerState
open ProofNetIR.SequentialSchedulerState.SequentialStackState
open ProofNetIR.SequentialSchedulerBridge
open ProofNetIR.SequentialFigure7

example {certificate : Certificate} {state : ReservationState}
    {active boundary targetAge : RawTokenAge} {target : Vertex}
    (invariant : SchedulerInvariant certificate state)
    (consumer : ConnectiveBelow certificate target)
    (location :
      FutureWorkAtExactWaitingLocation certificate state boundary
        consumer.conclusion)
    (targetMarked : state.core.marks[target]? = some (some targetAge))
    (targetRepresentative : state.core.representative targetAge = active)
    (boundaryOlder : boundary < active) :
    ∃ (payload : List Vertex) (linkIndex : Nat) (left right : Vertex)
        (olderPremise youngerPremise : Vertex)
        (olderAge youngerAge youngerBoundary : RawTokenAge),
      state.stack.waiting[boundary]? = some (.initialized payload) ∧
        consumer.conclusion ∈ payload ∧
        certificate.links[linkIndex]? =
          some (.par left right consumer.conclusion) ∧
        (SequentialUnification.sourceIndex certificate)[consumer.conclusion]? =
          some
            [{ linkIndex := linkIndex,
               link := .par left right consumer.conclusion }] ∧
        state.core.marks[consumer.conclusion]? = some none ∧
        ((olderPremise = left ∧ youngerPremise = right) ∨
          (olderPremise = right ∧ youngerPremise = left)) ∧
        state.core.marks[olderPremise]? = some (some olderAge) ∧
        state.core.marks[youngerPremise]? = some (some youngerAge) ∧
        sigmaBoundary? state.stack.sigma olderAge = some boundary ∧
        sigmaBoundary? state.stack.sigma youngerAge = some youngerBoundary ∧
        boundary < youngerBoundary ∧
        target = youngerPremise ∧
        consumer.mate = olderPremise ∧
        targetAge = youngerAge ∧
        youngerBoundary = active ∧
        state.core.representative olderAge = boundary ∧
        state.core.representative youngerAge = active := by
  exact location.activeTargetProducerOrientation invariant consumer targetMarked
    targetRepresentative boundaryOlder

#print axioms FutureWorkAtExactWaitingLocation.activeTargetProducerOrientation

end ProofNetIRWaitingReentryContinuationProducerOrientationTests

def main : IO Unit :=
  IO.println "Figure-7 waiting re-entry producer orientation: kernel-green"
