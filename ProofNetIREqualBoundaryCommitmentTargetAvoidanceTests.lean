/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7EqualBoundaryCommitmentTargetAvoidance

/-!
# Figure-7 equal-boundary commitment target-avoidance consumer

The consumer exercises tensor and par equal-boundary dichotomies. It also
destructs both exact par trace orientations rather than checking names only.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerBridge
open SequentialSchedulerState

#check CanonicalTagHistory.sameRepresentative_conclusionTouch_decomposition
#check CanonicalTagHistory.commitmentEdge_referencePath_avoiding_of_equal_storedRight
#check CanonicalTagHistory.commitmentEdge_equal_boundary_dichotomy
#check ReservationEvent.touched_parConclusion_decomposition
#check ReservationEvent.touched_parConclusion_cases
#check CanonicalTagHistory.commitmentEdge_parConclusion_dichotomy

example
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    (event : ReservationEvent certificate)
    {selected : Vertex}
    (consumer : ConnectiveBelow certificate selected)
    (parEq : consumer.kind = .par)
    (touched : event.Touched consumer.conclusion) :
    (consumer.side = .storedLeft ∧
      ∃ beforeTrace afterTrace,
        event.search.result.trace =
          beforeTrace ++ consumer.conclusion :: selected :: afterTrace) ∨
    (consumer.side = .storedRight ∧
      ∃ beforeTrace afterTrace,
        event.search.result.trace =
          beforeTrace ++ consumer.conclusion :: consumer.mate ::
            afterTrace) := by
  rcases event.touched_parConclusion_cases structural consumer parEq touched with
    selectedCase | mateCase
  · rcases selectedCase with ⟨side, beforeTrace, afterTrace, trace⟩
    exact Or.inl ⟨side, beforeTrace, afterTrace, trace⟩
  · rcases mateCase with ⟨side, beforeTrace, afterTrace, trace⟩
    exact Or.inr ⟨side, beforeTrace, afterTrace, trace⟩

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

example
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (invariant : SchedulerInvariant certificate state)
    (input : ReadyHeadInput state)
    (consumer : ConnectiveBelow certificate input.vertex)
    (parEq : consumer.kind = .par)
    {position parent : RawTokenAge}
    (parentAt : state.stack.sigma[position]? = some parent)
    (childAt : state.stack.sigma[position + 1]? = some input.rawAge) :
    tagHistory.CommitmentEdgeTargetAvoidingPath parent input.rawAge
        consumer.conclusion ∨
      ∃ event : ReservationEvent certificate,
        event ∈ tagHistory.reservationLedger ∧
          event.rawAge = input.rawAge ∧
          ((consumer.side = .storedLeft ∧
              ∃ beforeTrace afterTrace,
                event.search.result.trace =
                  beforeTrace ++ consumer.conclusion :: input.vertex ::
                    afterTrace) ∨
            (consumer.side = .storedRight ∧
              ∃ beforeTrace afterTrace,
                event.search.result.trace =
                  beforeTrace ++ consumer.conclusion :: consumer.mate ::
                    afterTrace)) := by
  rcases tagHistory.commitmentEdge_parConclusion_dichotomy invariant input
      consumer parEq parentAt childAt with avoiding | touched
  · exact Or.inl avoiding
  · rcases touched with ⟨event, membership, rawAge, selected | mate⟩
    · exact Or.inr ⟨event, membership, rawAge, Or.inl selected⟩
    · exact Or.inr ⟨event, membership, rawAge, Or.inr mate⟩

#print axioms ReservationEvent.touched_parConclusion_decomposition
#print axioms ReservationEvent.touched_parConclusion_cases
#print axioms CanonicalTagHistory.commitmentEdge_parConclusion_dichotomy

end SequentialFigure7
end ProofNetIR

def main : IO Unit :=
  IO.println "Figure-7 equal-boundary commitment target-avoidance consumer passed."
