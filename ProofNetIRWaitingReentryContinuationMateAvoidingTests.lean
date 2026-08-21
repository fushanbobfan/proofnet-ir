/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7WaitingReentryContinuationMateAvoiding

/-!
# Figure-7 waiting re-entry mate-avoidance consumer

Invokes the exact avoiding path, aligned re-entry, and wrapper-oriented
corollary through their public surface and checks their trust boundaries.
-/

namespace ProofNetIRWaitingReentryContinuationMateAvoidingTests

open ProofNetIR
open ProofNetIR.SequentialSchedulerState
open ProofNetIR.SequentialSchedulerState.SequentialStackState
open ProofNetIR.SequentialSchedulerBridge
open ProofNetIR.SequentialFigure7

example {certificate : Certificate} {state : ReservationState}
    {boundary : RawTokenAge} {target : Vertex}
    (correct : certificate.DeclarativelyCorrect)
    (consumer : ConnectiveBelow certificate target)
    (location :
      FutureWorkAtExactWaitingLocation certificate state boundary
        consumer.conclusion) :
    ∃ path : certificate.referenceSwitchingGraph.EdgeSimplePath,
      path.start = consumer.mate ∧
        path.finish = target ∧
        consumer.conclusion ∉ path.vertices := by
  exact location.mateToTargetAvoidingPath correct consumer

example {certificate : Certificate} {state : ReservationState}
    {active boundary targetAge : RawTokenAge} {target : Vertex}
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate state)
    {component : UnificationComponent} {usedLinks owned : List Nat}
    (componentLookup :
      state.core.components[active]? = some (some component))
    (occurrence :
      certificate.ComponentOccurrenceWitness component usedLinks owned)
    (consumer : ConnectiveBelow certificate target)
    (location :
      FutureWorkAtExactWaitingLocation certificate state boundary
        consumer.conclusion)
    (targetMarked : state.core.marks[target]? = some (some targetAge))
    (targetRepresentative : state.core.representative targetAge = active)
    (boundaryOlder : boundary < active) :
    consumer.kind = .par ∧
      Certificate.OwnedOccurrenceAccounted state.core active component owned ∧
      target ∈ owned ∧
      consumer.mate ∉ owned ∧
      ∃ (path : certificate.referenceSwitchingGraph.EdgeSimplePath)
          (directed : certificate.referenceSwitchingGraph.DirectedEdge),
        path.start = consumer.mate ∧
          path.finish = target ∧
          directed ∈ path.traversed ∧
          directed.source ∉ owned ∧
          directed.target ∈ owned ∧
          consumer.conclusion ∉ path.vertices := by
  exact location.activeTargetMateAlignedAvoidingReentry correct invariant
    componentLookup occurrence consumer targetMarked targetRepresentative
    boundaryOlder

example {certificate : Certificate} {state : ReservationState}
    {active boundary targetAge : RawTokenAge} {target : Vertex}
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate state)
    {component : UnificationComponent} {usedLinks owned : List Nat}
    (componentLookup :
      state.core.components[active]? = some (some component))
    (occurrence :
      certificate.ComponentOccurrenceWitness component usedLinks owned)
    (consumer : ConnectiveBelow certificate target)
    (location :
      FutureWorkAtExactWaitingLocation certificate state boundary
        consumer.conclusion)
    (targetMarked : state.core.marks[target]? = some (some targetAge))
    (targetRepresentative : state.core.representative targetAge = active)
    (boundaryOlder : boundary < active) :
    consumer.kind = .par ∧
      Certificate.OwnedOccurrenceAccounted state.core active component owned ∧
      target ∈ owned ∧
      consumer.mate ∉ owned ∧
      ActiveCarrierExternalEndpointReentryAvoiding certificate owned
        consumer.mate consumer.conclusion := by
  exact location.activeTargetMateAvoidingReentry correct invariant
    componentLookup occurrence consumer targetMarked targetRepresentative
    boundaryOlder

#print axioms FutureWorkAtExactWaitingLocation.mateToTargetAvoidingPath
#print axioms FutureWorkAtExactWaitingLocation.activeTargetMateAlignedAvoidingReentry
#print axioms FutureWorkAtExactWaitingLocation.activeTargetMateAvoidingReentry

end ProofNetIRWaitingReentryContinuationMateAvoidingTests

def main : IO Unit :=
  IO.println "Figure-7 waiting re-entry mate avoidance: kernel-green"
