/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7ActiveTopResidual

/-!
# Active-top ready-head-residual consumer

Checks the public no-ready-head equivalence and reachable-state disjunction.
The examples destructure both exact outcomes. They do not identify a drained
active top with completion, terminality, or progress.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerBridge

/-- Consume the no-ready-head equivalence and expose every field of the
active-top residual. -/
private theorem consumeNoReadyHead
    {certificate : Certificate} {state : ReservationState}
    (invariant : SchedulerInvariant certificate state)
    (started : 0 < state.stack.nextAge)
    (noHead : ¬ Nonempty (ReadyHeadInput state)) :
    ∃ rawAge component,
      state.stack.sigma.getLast? = some rawAge ∧
        state.core.components[rawAge]? = some (some component) ∧
          ∀ vertex, vertex ∈ component.frontier →
            state.core.marks[vertex]? ≠ some none := by
  have drained :=
    (SchedulerInvariant.no_readyHead_iff_activeTopDrained
      invariant started).mp noHead
  rcases drained with
    ⟨rawAge, component, sigmaTop, componentLookup, frontierFree⟩
  exact ⟨rawAge, component, sigmaTop, componentLookup, frontierFree⟩

/-- Consume the reverse direction: a drained active top has no ready head. -/
private theorem consumeDrainedNoReadyHead
    {certificate : Certificate} {state : ReservationState}
    (invariant : SchedulerInvariant certificate state)
    (started : 0 < state.stack.nextAge)
    (drained : ActiveTopDrained state) :
    ¬ Nonempty (ReadyHeadInput state) :=
  (SchedulerInvariant.no_readyHead_iff_activeTopDrained
    invariant started).mpr drained

/-- Consume both branches of the reachable-state residual, including the
exact dispatcher witness and every active-component field. -/
private theorem consumeDispatchOrDrained
    {certificate : Certificate} {state : ReservationState}
    (reachable : ReachableByImplementedDispatcher certificate state)
    (correct : certificate.DeclarativelyCorrect)
    (started : 0 < state.stack.nextAge) :
    let invariant := reachable.schedulerInvariant correct.1
    (∃ result : Figure7DispatchResult,
        dispatch? certificate state invariant = some result) ∨
      (∃ rawAge component,
        state.stack.sigma.getLast? = some rawAge ∧
          state.core.components[rawAge]? = some (some component) ∧
            ∀ vertex, vertex ∈ component.frontier →
              state.core.marks[vertex]? ≠ some none) := by
  rcases
      reachable.dispatch_or_activeTopDrained correct started with
    dispatch | drained
  · left
    rcases dispatch with ⟨result, dispatchEq⟩
    exact ⟨result, dispatchEq⟩
  · right
    rcases drained with
      ⟨rawAge, component, sigmaTop, componentLookup, frontierFree⟩
    exact ⟨rawAge, component, sigmaTop, componentLookup, frontierFree⟩

#print axioms
  SchedulerInvariant.no_readyHead_iff_activeTopDrained
#print axioms
  ReachableByImplementedDispatcher.dispatch_or_activeTopDrained

end SequentialFigure7
end ProofNetIR

def main : IO Unit :=
  IO.println "active-top residual consumer passed"
