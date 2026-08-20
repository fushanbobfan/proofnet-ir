/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7CommitmentIntervalTargetAvoidance
import ProofNetIR.SequentialFigure7EqualBoundaryCommitmentTargetAvoidance

/-!
# Figure-7 commitment-interval par-conclusion dichotomy

Classifies a complete positive retained commitment interval against the
conclusion of a supplied ready-head par consumer. Either all local edge paths
compose to one endpoint path avoiding that conclusion, or one exact child edge
has no such local path and an authentic child-age event trace contains the
conclusion-to-selected or conclusion-to-mate step.

The obstruction records whether its child is strictly before or equal to the
interval's final boundary. The outer alternatives remain inclusive: an
independently constructed endpoint path may coexist with the localized failed
edge. This module does not discharge the failed edge, derive a payer or tail
law, or prove progress.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerBridge
open SequentialSchedulerState

namespace CanonicalTagHistory

/-- A positive retained commitment interval either has a composed path that
avoids the current par conclusion or contains one exact local edge with no
avoiding path and an authentic selected/mate trace obstruction.

Strict sigma ordering locates the obstruction's child strictly before or at
the final boundary. The theorem does not eliminate either trace orientation
or make the two outer alternatives disjoint. -/
theorem commitmentInterval_parConclusion_dichotomy
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (invariant : SchedulerInvariant certificate state)
    (input : ReadyHeadInput state)
    (consumer : ConnectiveBelow certificate input.vertex)
    (parEq : consumer.kind = .par)
    {position edgeCount : Nat} {first last : RawTokenAge}
    (positive : 0 < edgeCount)
    (firstAt : state.stack.sigma[position]? = some first)
    (lastAt : state.stack.sigma[position + edgeCount]? = some last) :
    tagHistory.CommitmentEdgeTargetAvoidingPath first last
        consumer.conclusion ∨
      ∃ offset parent child event,
        offset < edgeCount ∧
          state.stack.sigma[position + offset]? = some parent ∧
          state.stack.sigma[position + offset + 1]? = some child ∧
          (child < last ∨ child = last) ∧
          ¬ tagHistory.CommitmentEdgeTargetAvoidingPath parent child
            consumer.conclusion ∧
          event ∈ tagHistory.reservationLedger ∧
          event.rawAge = child ∧
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
  classical
  by_cases edgeAvoids :
      ∀ {offset : Nat} {parent child : RawTokenAge},
        offset < edgeCount →
        state.stack.sigma[position + offset]? = some parent →
        state.stack.sigma[position + offset + 1]? = some child →
        tagHistory.CommitmentEdgeTargetAvoidingPath parent child
          consumer.conclusion
  · exact Or.inl
      (tagHistory.commitmentInterval_referencePath_avoiding positive firstAt
        lastAt edgeAvoids)
  · rcases Classical.not_forall.mp edgeAvoids with ⟨offset, missing⟩
    rcases Classical.not_forall.mp missing with ⟨parent, missing⟩
    rcases Classical.not_forall.mp missing with ⟨child, missing⟩
    rcases Classical.not_imp.mp missing with ⟨offsetLt, missing⟩
    rcases Classical.not_imp.mp missing with ⟨parentAt, missing⟩
    rcases Classical.not_imp.mp missing with ⟨childAt, notAvoiding⟩
    have childOrder : child < last ∨ child = last := by
      by_cases finalIndex :
          position + offset + 1 = position + edgeCount
      · right
        apply Option.some.inj
        exact childAt.symm.trans (by simpa [finalIndex] using lastAt)
      · left
        rcases List.getElem?_eq_some_iff.mp childAt with
          ⟨childBound, childValue⟩
        rcases List.getElem?_eq_some_iff.mp lastAt with
          ⟨lastBound, lastValue⟩
        have indexLt :
            position + offset + 1 < position + edgeCount := by
          omega
        have ordered :=
          (List.pairwise_iff_getElem.mp
            invariant.stack_wellShaped.sigma_partition.strictIncreasing)
            (position + offset + 1) (position + edgeCount)
            childBound lastBound indexLt
        simpa [childValue, lastValue] using ordered
    have missingCallback :
        ¬ ∀ {event : ReservationEvent certificate},
          event ∈ tagHistory.reservationLedger → event.rawAge = child →
            ¬ event.Touched consumer.conclusion := by
      intro callback
      exact notAvoiding
        (tagHistory.commitmentEdge_referencePath_avoiding_parConclusion
          invariant input consumer parEq parentAt childAt callback)
    rcases Classical.not_forall.mp missingCallback with ⟨event, missing⟩
    rcases Classical.not_imp.mp missing with ⟨membership, missing⟩
    rcases Classical.not_imp.mp missing with ⟨rawAge, missing⟩
    have touched : event.Touched consumer.conclusion :=
      Classical.not_not.mp missing
    exact Or.inr ⟨offset, parent, child, event, offsetLt, parentAt, childAt,
      childOrder, notAvoiding, membership, rawAge,
      event.touched_parConclusion_cases invariant.structural consumer parEq
        touched⟩

end CanonicalTagHistory
end SequentialFigure7
end ProofNetIR
