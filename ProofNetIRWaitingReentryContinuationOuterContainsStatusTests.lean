/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7WaitingReentryContinuationOuterContainsStatus

/-!
# Figure-7 waiting re-entry outer-containing-status consumer

Reconstructs both generic ready-head freshness facts and the exact strengthened
outer-containing status through the public surface, then checks their trust
boundaries.
-/

namespace ProofNetIRWaitingReentryContinuationOuterContainsStatusTests

open ProofNetIR
open ProofNetIR.SequentialSchedulerState
open ProofNetIR.SequentialSchedulerBridge
open ProofNetIR.SequentialFigure7
open ProofNetIR.SequentialFigure7.FutureWorkAtExactWaitingLocation

example {certificate : Certificate} {state : ReservationState}
    (input : ReadyHeadInput state)
    (invariant : SchedulerInvariant certificate state)
    (consumer : ConnectiveBelow certificate input.vertex) :
    ¬ Produced state consumer.conclusion := by
  exact input.connectiveConclusion_not_produced invariant consumer

example {certificate : Certificate} {state : ReservationState}
    (input : ReadyHeadInput state)
    (invariant : SchedulerInvariant certificate state)
    (consumer : ConnectiveBelow certificate input.vertex)
    {index : Nat} {component : UnificationComponent} {owned : List Vertex}
    (componentLookup :
      state.core.components[index]? = some (some component))
    (accounted :
      Certificate.OwnedOccurrenceAccounted state.core index component owned) :
    consumer.conclusion ∉ owned := by
  exact input.connectiveConclusion_not_owned_of_accounted invariant consumer
    componentLookup accounted

example {certificate : Certificate} {state : ReservationState}
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
  exact
    activeTargetMateOuterAvoidingReentryMarkedHistoricalTargetOrContainsFailureHistoricalStatus
      tagHistory input current currentPar correct invariant componentLookup
      occurrence consumer location targetMarked targetRepresentative
      boundaryOlder noTail

#print axioms ReadyHeadInput.connectiveConclusion_not_produced
#print axioms ReadyHeadInput.connectiveConclusion_not_owned_of_accounted
#print axioms
  activeTargetMateOuterAvoidingReentryMarkedHistoricalTargetOrContainsFailureHistoricalStatus

end ProofNetIRWaitingReentryContinuationOuterContainsStatusTests

def main : IO Unit :=
  IO.println "Figure-7 waiting re-entry outer contains status: kernel-green"
