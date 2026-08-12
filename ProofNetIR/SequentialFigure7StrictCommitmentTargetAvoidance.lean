/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7CommitmentIntervalTargetAvoidance
import ProofNetIR.SequentialFigure7OlderEventFutureWorkTouchSeparation

/-!
# Figure-7 strict commitment target avoidance

Discharges the explicit child-event untouched premise for one retained
commitment edge, or every edge in a positive retained interval, when the
relevant child boundary is strictly older than a supplied future-New
candidate. The proof consumes both existing older-event separation
invariants and the complete current-state scheduler invariant.

The interval theorem uses strict sigma ordering only to propagate strict
oldness backward from its final boundary. It does not cover an equal-boundary
edge, derive either separation invariant globally, establish queue origin or
any raw seam, or prove scheduler progress or completeness.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerBridge

namespace CanonicalTagHistory

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
  rcases
      invariant.stack_wellShaped.sigma_partition.boundary_exists rawAgeBound
    with ⟨boundary, boundaryLookup⟩
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

/-- An adjacent retained commitment edge has a canonical path avoiding a
future-New tensor conclusion when its child boundary is strictly older than
that candidate and both older-event separation invariants are supplied.

This theorem derives the exact child-event untouched callback required by
`commitmentEdge_referencePath_avoiding`. It is not an equal-boundary result
and does not establish either input invariant or its global availability. -/
theorem commitmentEdge_referencePath_avoiding_of_strict
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (invariant : SchedulerInvariant certificate state)
    (regionSeparated : OlderEventTouchSeparated tagHistory)
    (headSeparated : OlderEventFutureWorkTouchSeparated tagHistory)
    (candidate : FutureNewCandidateAt certificate state)
    {position : Nat} {parent child : RawTokenAge}
    (parentAt : state.stack.sigma[position]? = some parent)
    (childAt : state.stack.sigma[position + 1]? = some child)
    (childOlder :
      state.core.representative child <
        state.core.representative candidate.rawAge) :
    tagHistory.CommitmentEdgeTargetAvoidingPath parent child
      candidate.tensor.conclusion := by
  apply tagHistory.commitmentEdge_referencePath_avoiding invariant candidate
    parentAt childAt
  intro event membership eventAge
  apply regionSeparated.strict_candidateConclusion_untouched headSeparated
    invariant.structural membership candidate
  simpa [eventAge] using childOlder

/-- A positive retained commitment interval has a canonical path avoiding a
future-New tensor conclusion when its final boundary is strictly older than
that candidate and both older-event separation invariants are supplied.

Strict sigma ordering and exact first/final lookups make every child inside
the interval no newer than the final boundary, so the adjacent strict theorem
supplies every callback required by interval composition. This does not cover
a zero-length interval, an equal final boundary, arbitrary non-sigma paths,
or global availability of the input invariants. -/
theorem commitmentInterval_referencePath_avoiding_of_lastOlder
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (invariant : SchedulerInvariant certificate state)
    (regionSeparated : OlderEventTouchSeparated tagHistory)
    (headSeparated : OlderEventFutureWorkTouchSeparated tagHistory)
    (candidate : FutureNewCandidateAt certificate state)
    {position edgeCount : Nat} {first last : RawTokenAge}
    (positive : 0 < edgeCount)
    (firstAt : state.stack.sigma[position]? = some first)
    (lastAt : state.stack.sigma[position + edgeCount]? = some last)
    (lastOlder :
      state.core.representative last <
        state.core.representative candidate.rawAge) :
    tagHistory.CommitmentEdgeTargetAvoidingPath first last
      candidate.tensor.conclusion := by
  apply tagHistory.commitmentInterval_referencePath_avoiding positive firstAt
    lastAt
  intro offset parent child offsetLt parentAt childAt
  apply tagHistory.commitmentEdge_referencePath_avoiding_of_strict invariant
    regionSeparated headSeparated candidate parentAt childAt
  rcases List.getElem?_eq_some_iff.mp childAt with
    ⟨childBound, childValue⟩
  rcases List.getElem?_eq_some_iff.mp lastAt with
    ⟨lastBound, lastValue⟩
  have indexLe :
      position + offset + 1 ≤ position + edgeCount := by
    omega
  have childLeLast : child ≤ last := by
    by_cases sameIndex :
        position + offset + 1 = position + edgeCount
    · have lastAtChildIndex :
          state.stack.sigma[position + offset + 1]? = some last := by
        simpa [sameIndex] using lastAt
      exact Nat.le_of_eq
        (Option.some.inj (childAt.symm.trans lastAtChildIndex))
    · have indexLt :
          position + offset + 1 < position + edgeCount := by
        omega
      have ordered :=
        (List.pairwise_iff_getElem.mp
          invariant.stack_wellShaped.sigma_partition.strictIncreasing)
          (position + offset + 1) (position + edgeCount)
          childBound lastBound indexLt
      rw [childValue, lastValue] at ordered
      exact Nat.le_of_lt ordered
  have childRoot := representative_eq_of_sigmaAt invariant childAt
  have lastRoot := representative_eq_of_sigmaAt invariant lastAt
  rw [childRoot]
  rw [lastRoot] at lastOlder
  exact Nat.lt_of_le_of_lt childLeLast lastOlder

end CanonicalTagHistory
end SequentialFigure7
end ProofNetIR
