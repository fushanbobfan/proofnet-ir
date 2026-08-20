/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7ActiveTopDebtParentTemporalOutcome

/-!
# Active-top debt parent temporal outcome consumer

This runnable consumer reconstructs every endpoint constructor and invokes
both tensor-specific and source-generic normalization theorems. It does not
assume or derive the history tail law or a ready-tail witness.
-/

namespace ProofNetIRActiveTopDebtParentTemporalOutcomeTests

open ProofNetIR
open ProofNetIR.SequentialFigure7
open ProofNetIR.SequentialSchedulerBridge
open ProofNetIR.SequentialSchedulerState

private inductive OutcomeObservation
    (certificate : Certificate) (state : ReservationState)
    (activeRawAge : RawTokenAge) (selected : Vertex) (owned : List Vertex) :
    Prop where
  | raw
      (sibling : Vertex)
      (unmarked : state.core.marks[sibling]? = some none)
      (location : sibling = selected ∨ sibling ∉ owned) :
      OutcomeObservation certificate state activeRawAge selected owned
  | future
      (conclusion : Vertex) (boundary : RawTokenAge)
      (work : FutureWorkAt state boundary conclusion)
      (older : boundary < activeRawAge)
      (outside : conclusion ∉ owned) :
      OutcomeObservation certificate state activeRawAge selected owned
  | marked
      (conclusion : Vertex) (conclusionAge : RawTokenAge)
      (mark : state.core.marks[conclusion]? = some (some conclusionAge))
      (older : state.core.representative conclusionAge < activeRawAge)
      (outside : conclusion ∉ owned) :
      OutcomeObservation certificate state activeRawAge selected owned

private theorem observeOutcome
    {certificate : Certificate} {state : ReservationState}
    {activeRawAge : RawTokenAge} {selected : Vertex} {owned : List Vertex}
    (outcome :
      ActiveCarrierParentTemporalOutcome certificate state activeRawAge selected
        owned) :
    OutcomeObservation certificate state activeRawAge selected owned := by
  cases outcome with
  | rawSibling sibling unmarked location =>
      exact .raw sibling unmarked location
  | olderFuture conclusion boundary work older outside =>
      exact .future conclusion boundary work older outside
  | olderMarked conclusion conclusionAge mark older outside =>
      exact .marked conclusion conclusionAge mark older outside

private theorem roundTripOutcome
    {certificate : Certificate} {state : ReservationState}
    {activeRawAge : RawTokenAge} {selected : Vertex} {owned : List Vertex}
    (outcome :
      ActiveCarrierParentTemporalOutcome certificate state activeRawAge selected
        owned) :
    ∃ rebuilt :
        ActiveCarrierParentTemporalOutcome certificate state activeRawAge selected
          owned,
      rebuilt = outcome ∧
        OutcomeObservation certificate state activeRawAge selected owned := by
  cases outcome with
  | rawSibling sibling unmarked location =>
      let rebuilt :
          ActiveCarrierParentTemporalOutcome certificate state activeRawAge
            selected owned :=
        .rawSibling sibling unmarked location
      exact ⟨rebuilt, rfl, observeOutcome rebuilt⟩
  | olderFuture conclusion boundary work older outside =>
      let rebuilt :
          ActiveCarrierParentTemporalOutcome certificate state activeRawAge
            selected owned :=
        .olderFuture conclusion boundary work older outside
      exact ⟨rebuilt, rfl, observeOutcome rebuilt⟩
  | olderMarked conclusion conclusionAge mark older outside =>
      let rebuilt :
          ActiveCarrierParentTemporalOutcome certificate state activeRawAge
            selected owned :=
        .olderMarked conclusion conclusionAge mark older outside
      exact ⟨rebuilt, rfl, observeOutcome rebuilt⟩

private theorem tensorConsumer
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {owned : List Vertex}
    (residual :
      tagHistory.ActiveCarrierTensorSameBoundaryResidual input component owned)
    (invariant : SchedulerInvariant certificate state)
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component)) :
    OutcomeObservation certificate state input.rawAge input.vertex owned := by
  exact observeOutcome (residual.temporalOutcome invariant componentLookup)

private theorem parentConsumer
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {owned : List Vertex}
    (residual :
      ActiveCarrierParentTemporalResidual tagHistory input component owned)
    (invariant : SchedulerInvariant certificate state)
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component)) :
    ∃ rebuilt :
        ActiveCarrierParentTemporalOutcome certificate state input.rawAge
          input.vertex owned,
      rebuilt = residual.temporalOutcome invariant componentLookup ∧
        OutcomeObservation certificate state input.rawAge input.vertex owned := by
  exact roundTripOutcome (residual.temporalOutcome invariant componentLookup)

#print axioms ActiveCarrierParentTemporalOutcome
#print axioms CanonicalTagHistory.ActiveCarrierTensorSameBoundaryResidual.temporalOutcome
#print axioms ActiveCarrierParentTemporalResidual.temporalOutcome

end ProofNetIRActiveTopDebtParentTemporalOutcomeTests

def main : IO Unit :=
  IO.println "active-top debt parent temporal-outcome consumer: kernel-green"
