/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7ReadyHeadDispatchResidual

/-!
# Figure-7 ready-head dispatch-residual consumer

Destructures and reconstructs the history-indexed priority dichotomy and its
dispatcher-reachable executable wrapper.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerBridge
open SequentialSchedulerState

#check ReadyHeadMarkedTensorPredecessorGap
#check CanonicalTagHistory.readyHead_priorityEnabled_or_markedTensorPredecessorGap
#check ReachableByImplementedDispatcher.readyHead_dispatch_or_markedTensorPredecessorGap

example
    {certificate : Certificate} {before : ReservationState}
    {history : ExecutedHistory certificate before}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate before)
    (head : ReadyHeadInput before) :
    (∃ kind, PriorityEnabled certificate before invariant kind) ∨
      Nonempty
        (ReadyHeadMarkedTensorPredecessorGap certificate before head) := by
  rcases
      tagHistory.readyHead_priorityEnabled_or_markedTensorPredecessorGap
        correct invariant head with enabled | gap
  · rcases enabled with ⟨kind, enabled⟩
    exact Or.inl ⟨kind, enabled⟩
  · rcases gap with ⟨gap⟩
    exact Or.inr ⟨{
      consumer := gap.consumer
      mateRawAge := gap.mateRawAge
      mateBoundary := gap.mateBoundary
      tensor_kind := gap.tensor_kind
      mate_marked := gap.mate_marked
      mate_boundary := gap.mate_boundary
      mate_boundary_lt_active := gap.mate_boundary_lt_active
      no_predecessor := gap.no_predecessor }⟩

example
    {certificate : Certificate} {before : ReservationState}
    (reachable : ReachableByImplementedDispatcher certificate before)
    (correct : certificate.DeclarativelyCorrect)
    (head : ReadyHeadInput before) :
    let invariant := reachable.schedulerInvariant correct.1
    (∃ result : Figure7DispatchResult,
      dispatch? certificate before invariant = some result) ∨
        Nonempty
          (ReadyHeadMarkedTensorPredecessorGap certificate before head) := by
  let invariant := reachable.schedulerInvariant correct.1
  change
    (∃ result : Figure7DispatchResult,
      dispatch? certificate before invariant = some result) ∨
        Nonempty
          (ReadyHeadMarkedTensorPredecessorGap certificate before head)
  rcases
      reachable.readyHead_dispatch_or_markedTensorPredecessorGap correct head with
    dispatch | gap
  · rcases dispatch with ⟨result, equation⟩
    exact Or.inl ⟨result, equation⟩
  · exact Or.inr gap

end SequentialFigure7
end ProofNetIR

def main : IO Unit :=
  IO.println "Figure-7 ready-head dispatch-residual consumer passed."
