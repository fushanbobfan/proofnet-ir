/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7FutureWorkQueueStatus

/-!
# Figure-7 future-work queue-status consumer

Reconstructs the public current-state queue classifier, checks the trust
boundary of every new declaration, and executes a kernel-green marker.
-/

namespace ProofNetIRFutureWorkQueueStatusTests

open ProofNetIR
open ProofNetIR.SequentialSchedulerState
open ProofNetIR.SequentialSchedulerState.SequentialStackState
open ProofNetIR.SequentialSchedulerBridge
open ProofNetIR.SequentialFigure7

example {certificate : Certificate} {state : ReservationState}
    (input : ReadyHeadInput state)
    (invariant : SchedulerInvariant certificate state)
    {component : UnificationComponent} {usedLinks owned : List Nat}
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      certificate.ComponentOccurrenceWitness component usedLinks owned)
    {boundary : RawTokenAge} {vertex : Vertex}
    (work : FutureWorkAt state boundary vertex)
    (outside : vertex ∉ owned) :
    boundary < input.rawAge := by
  exact work.boundary_lt_active_of_not_owned input invariant componentLookup
    occurrence outside

example {certificate : Certificate} {state : ReservationState}
    (invariant : SchedulerInvariant certificate state)
    {vertex : Vertex} :
    vertex ∈ state.stack.queuedVertices ↔
      ∃ boundary, FutureWorkAt state boundary vertex := by
  exact invariant.mem_queued_iff_exists_futureWorkAt

example {certificate : Certificate} {state : ReservationState}
    (input : ReadyHeadInput state)
    (invariant : SchedulerInvariant certificate state)
    {component : UnificationComponent} {usedLinks owned : List Nat}
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      certificate.ComponentOccurrenceWitness component usedLinks owned)
    {vertex : Vertex}
    (unmarked : state.core.marks[vertex]? = some none)
    (outside : vertex ∉ owned) :
    UnmarkedOutsideActiveSchedulerStatus certificate state input owned vertex := by
  exact invariant.unmarkedOutsideActiveSchedulerStatus input componentLookup
    occurrence unmarked outside

#print axioms ProofNetIR.SequentialFigure7.UnmarkedOutsideActiveSchedulerStatus
#print axioms
  ProofNetIR.SequentialFigure7.FutureWorkAt.boundary_lt_active_of_not_owned
#print axioms
  ProofNetIR.SequentialSchedulerBridge.SchedulerInvariant.mem_queued_iff_exists_futureWorkAt
#print axioms
  ProofNetIR.SequentialSchedulerBridge.SchedulerInvariant.unmarkedOutsideActiveSchedulerStatus

end ProofNetIRFutureWorkQueueStatusTests

def main : IO Unit :=
  IO.println "Figure-7 future-work queue status: kernel-green"
