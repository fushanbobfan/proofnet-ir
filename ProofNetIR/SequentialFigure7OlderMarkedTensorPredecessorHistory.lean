/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7OlderMarkedTensorPredecessorForwardPreservation
import ProofNetIR.SequentialFigure7OlderMarkedTensorPredecessorNewPreservation
import ProofNetIR.SequentialFigure7OlderMarkedTensorPredecessorUnifyPayloadPreservation
import ProofNetIR.SequentialFigure7OlderMarkedTensorPredecessorWaitPreservation
import ProofNetIR.SequentialFigure7ReadyHeadDispatchResidual

/-!
# Full-history older marked-tensor predecessor invariant

Packages the empty, initial, and six later dispatcher-branch preservation
theorems into one invariant over every exact canonical history. The resulting
invariant eliminates the marked-tensor predecessor residual at an already
supplied reachable ready head and yields an exact successful dispatcher result.

The ready-head theorem retains `ReadyHeadInput` as an explicit argument. This
module does not derive a ready head from semantic nonterminality and proves no
dispatcher progress, later-state totality, pure-worklist completeness,
fallback removal, scheduling, or complexity bound.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerBridge

/-- Every exact canonical tag history carries the older marked-tensor
predecessor invariant.

The `later` case only transports the invariant across an already-successful
priority-aware dispatcher step. It does not assert that such a step exists. -/
theorem CanonicalTagHistory.olderMarkedTensorPredecessorInvariant
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect) :
    OlderMarkedTensorPredecessorInvariant certificate state := by
  induction tagHistory with
  | empty =>
      exact empty_olderMarkedTensorPredecessorInvariant certificate
  | init step =>
      exact
        SequentialFigure7.InitialReservationStep.olderMarkedTensorPredecessorInvariant
          step
  | @later before result history invariant dispatch prior evidence induction =>
      cases dispatch with
      | concl equation =>
          rcases
              (concl?_some_iff invariant.toReservationInvariant).mp equation with
            ⟨step⟩
          exact step.olderMarkedTensorPredecessorInvariant invariant induction
      | nop _ equation =>
          rcases
              (nop?_some_iff invariant.toReservationInvariant).mp equation with
            ⟨step⟩
          exact step.olderMarkedTensorPredecessorInvariant invariant induction
      | new _ _ equation =>
          rcases
              (new?_some_iff invariant.toReservationInvariant).mp equation with
            ⟨step⟩
          exact prior.new_olderMarkedTensorPredecessorInvariant correct invariant
            step induction
      | wait conclNone nopNone newNone equation =>
          rcases
              (wait?_some_iff invariant.toReservationInvariant).mp equation with
            ⟨step⟩
          exact prior.wait_olderMarkedTensorPredecessorInvariant
            (invariant := invariant)
            (dispatch :=
              .wait (invariant := invariant) conclNone nopNone newNone equation)
            correct step induction
      | forward conclNone nopNone newNone waitNone equation =>
          rcases
              (forward?_some_iff invariant.toReservationInvariant).mp equation with
            ⟨step⟩
          exact prior.forward_olderMarkedTensorPredecessorInvariant
            (invariant := invariant)
            (dispatch :=
              .forward (invariant := invariant) conclNone nopNone newNone
                waitNone equation)
            correct step induction
      | unifyPayload conclNone nopNone newNone waitNone forwardNone equation =>
          rcases
              (unifyPayload?_some_iff invariant.toReservationInvariant).mp
                  equation with
            ⟨step⟩
          exact prior.unifyPayload_olderMarkedTensorPredecessorInvariant
            (invariant := invariant)
            (dispatch :=
              .unifyPayload (invariant := invariant) conclNone nopNone newNone
                waitNone forwardNone equation)
            correct step induction

/-- Every exact implemented-dispatcher history carries the predecessor
invariant under declarative correctness. -/
theorem ExecutedHistory.olderMarkedTensorPredecessorInvariant
    {certificate : Certificate} {state : ReservationState}
    (history : ExecutedHistory certificate state)
    (correct : certificate.DeclarativelyCorrect) :
    OlderMarkedTensorPredecessorInvariant certificate state := by
  rcases history.hasCanonicalTagHistory with ⟨tagHistory⟩
  exact tagHistory.olderMarkedTensorPredecessorInvariant correct

/-- A dispatcher-reachable state with an explicitly supplied ready head has
one exact successful canonical dispatcher result.

This theorem is conditional on `ReadyHeadInput`; it neither constructs that
input nor states unconditional progress or totality. -/
theorem ReachableByImplementedDispatcher.readyHead_dispatch
    {certificate : Certificate} {before : ReservationState}
    (reachable : ReachableByImplementedDispatcher certificate before)
    (correct : certificate.DeclarativelyCorrect)
    (head : ReadyHeadInput before) :
    let invariant := reachable.schedulerInvariant correct.1
    ∃ result : Figure7DispatchResult,
      dispatch? certificate before invariant = some result := by
  let invariant := reachable.schedulerInvariant correct.1
  change ∃ result : Figure7DispatchResult,
    dispatch? certificate before invariant = some result
  rcases reachable with ⟨history⟩
  rcases history.hasCanonicalTagHistory with ⟨tagHistory⟩
  have allWork :
      OlderMarkedTensorPredecessorInvariant certificate before :=
    tagHistory.olderMarkedTensorPredecessorInvariant correct
  rcases
      tagHistory.readyHead_priorityEnabled_or_markedTensorPredecessorGap
        correct invariant head with enabled | gap
  · rcases enabled with ⟨kind, enabled⟩
    rcases enabled.exists_dispatchStep with ⟨after, step⟩
    exact ⟨⟨kind, after⟩, (dispatch?_some_iff invariant).mpr step⟩
  · rcases gap with ⟨gap⟩
    exfalso
    apply gap.no_predecessor
    exact allWork.readyHead_predecessor_of_boundary_lt invariant head
      gap.consumer gap.tensor_kind gap.mate_marked gap.mate_boundary
        gap.mate_boundary_lt_active

end SequentialFigure7
end ProofNetIR
