/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7ActiveTopDebtParentExternalTemporalOutcome
import ProofNetIR.SequentialFigure7CommitmentEdgeReferencePath
import ProofNetIR.SequentialFigure7StrictOlderSigmaSplit

/-!
# Active-top debt external parent commitment outcome

Every strictly older boundary in an external parent temporal outcome lies on
the retained `sigma` stack below the active top. The final adjacent edge of
that interval therefore has the exact canonical commitment reference path.
This attaches occurrence-aware reservation data to the older future-work and
older marked branches while preserving the external raw branch unchanged.

The result is still a failure reduction. It does not construct a path from
the external endpoint to the commitment edge, prove endpoint re-entry, return
a distinct ready-tail witness, derive the history-tail law, or establish
dispatcher progress or completion.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerBridge

namespace SchedulerInvariant

private theorem representative_eq_of_sigmaAt
    {certificate : Certificate} {state : ReservationState}
    (invariant : SchedulerInvariant certificate state)
    {position : Nat} {rawAge : RawTokenAge}
    (sigmaAt : state.stack.sigma[position]? = some rawAge) :
    state.core.representative rawAge = rawAge := by
  have rawAgeMembership : rawAge ∈ state.stack.sigma :=
    List.mem_of_getElem? sigmaAt
  have rawAgeBound : rawAge < state.stack.nextAge :=
    invariant.stack_wellShaped.sigma_partition.boundary_lt rawAge
      rawAgeMembership
  rcases invariant.stack_wellShaped.sigma_partition.boundary_exists
      rawAgeBound with ⟨boundary, boundaryLookup⟩
  have boundaryLeRawAge : boundary ≤ rawAge :=
    sigmaBoundary?_le boundaryLookup
  have rawAgeLeBoundary : rawAge ≤ boundary :=
    sigmaBoundary?_greatest
      invariant.stack_wellShaped.sigma_partition.strictIncreasing
      boundaryLookup rawAge rawAgeMembership (Nat.le_refl _)
  have boundaryEq : boundary = rawAge :=
    Nat.le_antisymm boundaryLeRawAge rawAgeLeBoundary
  subst boundary
  have representativeLookup :=
    invariant.realizesSigma.representative_eq_boundary rawAgeBound
  exact Option.some.inj (representativeLookup.symm.trans boundaryLookup)

/-- Any strictly older retained boundary determines the exact final adjacent
`sigma` edge into the active top boundary. -/
private theorem strictOlderSigmaSplit_to_top
    {certificate : Certificate} {state : ReservationState}
    (invariant : SchedulerInvariant certificate state)
    {first active : RawTokenAge}
    (firstMembership : first ∈ state.stack.sigma)
    (activeTop : state.stack.sigma.getLast? = some active)
    (older : first < active) :
    StrictOlderSigmaSplit state first active := by
  rcases List.getElem_of_mem firstMembership with
    ⟨firstPosition, firstBound, firstValue⟩
  have firstAt :
      state.stack.sigma[firstPosition]? = some first := by
    rw [List.getElem?_eq_getElem firstBound, firstValue]
  have activeMembership : active ∈ state.stack.sigma :=
    List.mem_of_getLast? activeTop
  rcases List.getElem_of_mem activeMembership with
    ⟨activePosition, activeBound, activeValue⟩
  have activeAt :
      state.stack.sigma[activePosition]? = some active := by
    rw [List.getElem?_eq_getElem activeBound, activeValue]
  have firstBeforeActive : firstPosition < activePosition := by
    by_cases activeLeFirst : activePosition ≤ firstPosition
    · rcases Nat.eq_or_lt_of_le activeLeFirst with same | before
      · have sameLookup :
            state.stack.sigma[firstPosition]? = some active := by
          simpa [same] using activeAt
        have agesEq : first = active :=
          Option.some.inj (firstAt.symm.trans sameLookup)
        rw [← agesEq] at older
        exact (Nat.lt_irrefl first older).elim
      · have ordered :=
          (List.pairwise_iff_getElem.mp
            invariant.stack_wellShaped.sigma_partition.strictIncreasing)
            activePosition firstPosition activeBound firstBound before
        rw [activeValue, firstValue] at ordered
        exact ((Nat.not_lt_of_ge (Nat.le_of_lt ordered)) older).elim
    · exact Nat.lt_of_not_ge activeLeFirst
  let edgeCount := activePosition - firstPosition - 1
  have predecessorPositionBound :
      firstPosition + edgeCount < state.stack.sigma.length := by
    dsimp [edgeCount]
    omega
  let predecessor := state.stack.sigma[firstPosition + edgeCount]
  have predecessorAt :
      state.stack.sigma[firstPosition + edgeCount]? = some predecessor := by
    rw [List.getElem?_eq_getElem predecessorPositionBound]
  have activeAtFinal :
      state.stack.sigma[firstPosition + edgeCount + 1]? = some active := by
    have indexEq :
        firstPosition + edgeCount + 1 = activePosition := by
      dsimp [edgeCount]
      omega
    simpa [indexEq] using activeAt
  have predecessorRawOlder : predecessor < active := by
    rcases List.getElem?_eq_some_iff.mp predecessorAt with
      ⟨predecessorBound, predecessorValue⟩
    have indexEq :
        firstPosition + edgeCount + 1 = activePosition := by
      dsimp [edgeCount]
      omega
    have ordered :=
      (List.pairwise_iff_getElem.mp
        invariant.stack_wellShaped.sigma_partition.strictIncreasing)
        (firstPosition + edgeCount) activePosition
        predecessorBound activeBound (by omega)
    rw [predecessorValue, activeValue] at ordered
    exact ordered
  have predecessorRoot :=
    representative_eq_of_sigmaAt invariant predecessorAt
  have activeRoot := representative_eq_of_sigmaAt invariant activeAt
  have representativeOlder :
      state.core.representative predecessor <
        state.core.representative active := by
    rw [predecessorRoot, activeRoot]
    exact predecessorRawOlder
  exact ⟨firstPosition, edgeCount, predecessor, firstAt, predecessorAt,
    activeAtFinal, representativeOlder⟩

end SchedulerInvariant

namespace CanonicalTagHistory

/-- A strictly older retained boundary together with the exact final
commitment edge and its canonical reference path into the active top. -/
def StrictOlderCommitmentSplit
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (first active : RawTokenAge) : Prop :=
  ∃ position edgeCount predecessor,
    state.stack.sigma[position]? = some first ∧
      state.stack.sigma[position + edgeCount]? = some predecessor ∧
      state.stack.sigma[position + edgeCount + 1]? = some active ∧
      state.core.representative predecessor <
        state.core.representative active ∧
      tagHistory.CommitmentEdgeReferencePath predecessor active

/-- Every strictly older retained boundary yields a commitment split whose
final adjacent edge carries the canonical reservation-to-reservation path. -/
theorem strictOlderCommitmentSplit_to_top
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (invariant : SchedulerInvariant certificate state)
    {first active : RawTokenAge}
    (firstMembership : first ∈ state.stack.sigma)
    (activeTop : state.stack.sigma.getLast? = some active)
    (older : first < active) :
    tagHistory.StrictOlderCommitmentSplit first active := by
  rcases SchedulerInvariant.strictOlderSigmaSplit_to_top invariant
      firstMembership activeTop older with
    ⟨position, edgeCount, predecessor, firstAt, predecessorAt, activeAt,
      representativeOlder⟩
  exact ⟨position, edgeCount, predecessor, firstAt, predecessorAt, activeAt,
    representativeOlder,
    tagHistory.commitmentEdge_referencePath invariant predecessorAt activeAt⟩

end CanonicalTagHistory

/-- An external parent temporal outcome whose older branches retain the exact
final canonical commitment edge into the active boundary. -/
inductive ActiveCarrierParentExternalCommitmentOutcome
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (activeRawAge : RawTokenAge) (owned : List Vertex) : Prop where
  | rawOutside
      (sibling : Vertex)
      (unmarked : state.core.marks[sibling]? = some none)
      (outside : sibling ∉ owned) :
      ActiveCarrierParentExternalCommitmentOutcome tagHistory
        activeRawAge owned
  | olderFuture
      (conclusion : Vertex) (boundary : RawTokenAge)
      (work : FutureWorkAt state boundary conclusion)
      (older : boundary < activeRawAge)
      (commitmentSplit :
        tagHistory.StrictOlderCommitmentSplit boundary activeRawAge)
      (outside : conclusion ∉ owned) :
      ActiveCarrierParentExternalCommitmentOutcome tagHistory
        activeRawAge owned
  | olderMarked
      (conclusion : Vertex) (conclusionAge : RawTokenAge)
      (marked : state.core.marks[conclusion]? = some (some conclusionAge))
      (olderRepresentative :
        state.core.representative conclusionAge < activeRawAge)
      (commitmentSplit : tagHistory.StrictOlderCommitmentSplit
        (state.core.representative conclusionAge) activeRawAge)
      (outside : conclusion ∉ owned) :
      ActiveCarrierParentExternalCommitmentOutcome tagHistory
        activeRawAge owned

namespace ActiveCarrierParentExternalTemporalOutcome

/-- Locate both older temporal branches on an exact retained interval and
retain the final canonical commitment edge into the active top boundary. -/
theorem commitmentOutcome
    {certificate : Certificate} {state : ReservationState}
    {activeRawAge : RawTokenAge} {owned : List Vertex}
    (outcome : ActiveCarrierParentExternalTemporalOutcome certificate state
      activeRawAge owned)
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (invariant : SchedulerInvariant certificate state)
    (activeTop : state.stack.sigma.getLast? = some activeRawAge) :
    ActiveCarrierParentExternalCommitmentOutcome tagHistory
      activeRawAge owned := by
  cases outcome with
  | rawOutside sibling unmarked outside =>
      exact .rawOutside sibling unmarked outside
  | olderFuture conclusion boundary work older outside =>
      have firstMembership : boundary ∈ state.stack.sigma :=
        work.rawAge_mem_sigma invariant
      exact .olderFuture conclusion boundary work older
        (tagHistory.strictOlderCommitmentSplit_to_top invariant
          firstMembership activeTop older)
        outside
  | olderMarked conclusion conclusionAge marked older outside =>
      have stackMarked :
          state.stack.marks[conclusion]? = some (some conclusionAge) := by
        rw [← invariant.realizesSigma.marks_eq]
        exact marked
      have ageBound : conclusionAge < state.stack.nextAge :=
        invariant.stack_wellShaped.assigned_age_bound conclusion
          conclusionAge stackMarked
      have boundaryLookup :=
        invariant.realizesSigma.representative_eq_boundary ageBound
      have firstMembership :
          state.core.representative conclusionAge ∈ state.stack.sigma :=
        sigmaBoundary?_mem boundaryLookup
      exact .olderMarked conclusion conclusionAge marked older
        (tagHistory.strictOlderCommitmentSplit_to_top invariant
          firstMembership activeTop older)
        outside

end ActiveCarrierParentExternalTemporalOutcome

end SequentialFigure7
end ProofNetIR
