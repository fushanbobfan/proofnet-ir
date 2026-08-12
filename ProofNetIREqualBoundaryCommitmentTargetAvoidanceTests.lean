/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7EqualBoundaryCommitmentTargetAvoidance

/-! # Figure-7 equal-boundary commitment target-avoidance consumer -/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerBridge
open SequentialSchedulerState

#check CanonicalTagHistory.sameRepresentative_conclusionTouch_decomposition
#check CanonicalTagHistory.commitmentEdge_referencePath_avoiding_of_equal_storedRight
#check CanonicalTagHistory.commitmentEdge_equal_boundary_dichotomy

example
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate state)
    (guard : NewGuard certificate state)
    {position : Nat} {parent : RawTokenAge}
    (parentAt : state.stack.sigma[position]? = some parent)
    (childAt :
      state.stack.sigma[position + 1]? = some guard.head.rawAge)
    (storedRight : guard.tensor.side = .storedRight) :
    tagHistory.CommitmentEdgeTargetAvoidingPath parent guard.head.rawAge
      guard.tensor.conclusion :=
  tagHistory.commitmentEdge_referencePath_avoiding_of_equal_storedRight
    correct invariant guard parentAt childAt storedRight

example
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate state)
    (guard : NewGuard certificate state)
    {position : Nat} {parent : RawTokenAge}
    (parentAt : state.stack.sigma[position]? = some parent)
    (childAt :
      state.stack.sigma[position + 1]? = some guard.head.rawAge) :
    tagHistory.CommitmentEdgeTargetAvoidingPath parent guard.head.rawAge
        guard.tensor.conclusion ∨
      ∃ event : ReservationEvent certificate,
        ∃ beforeTrace afterTrace,
          event.rawAge = guard.head.rawAge ∧
            guard.tensor.side = .storedLeft ∧
            event.search.result.trace =
              beforeTrace ++ guard.tensor.conclusion ::
                guard.head.vertex :: afterTrace := by
  rcases tagHistory.commitmentEdge_equal_boundary_dichotomy correct invariant
      guard parentAt childAt with avoiding | obstruction
  · exact Or.inl avoiding
  · rcases obstruction with
      ⟨event, beforeTrace, afterTrace, _membership, rawAge, storedLeft, trace⟩
    exact Or.inr ⟨event, beforeTrace, afterTrace, rawAge, storedLeft, trace⟩

end SequentialFigure7
end ProofNetIR

def main : IO Unit :=
  IO.println "Figure-7 equal-boundary commitment target-avoidance consumer passed."
