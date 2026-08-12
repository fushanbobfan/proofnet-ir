/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7CommitmentEdgeTargetAvoidance

/-!
# Figure-7 commitment-interval target avoidance

Composes exact target-avoiding paths across any supplied nonempty interval of
adjacent retained sigma commitments. Every local edge witness is an explicit
input; this module does not derive child-event untouchedness, global callback
availability, any raw seam, scheduler progress, or a complexity bound.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerBridge

namespace CanonicalTagHistory

/-- A positive retained-`sigma` interval whose supplied adjacent commitment
paths all avoid one shared target has a loop-erased endpoint path avoiding
that target.

The callback supplies only the adjacent edges inside this interval. It may be
instantiated with `commitmentEdge_referencePath_avoiding`, but this theorem
does not derive its explicit `childUntouched` premise or make that callback
globally available. The result reuses `CommitmentEdgeTargetAvoidingPath` only
as an endpoint-path carrier; it does not say that `first` and `last` are
adjacent. Loop erasure preserves the endpoints and target avoidance, not
stored parallel-edge indices, individual segment decomposition, nonempty
traversal, sigma monotonicity, raw-age uniqueness, or a complexity bound. -/
theorem commitmentInterval_referencePath_avoiding
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    {forbidden : Vertex} {position edgeCount : Nat}
    {first last : RawTokenAge}
    (positive : 0 < edgeCount)
    (firstAt : state.stack.sigma[position]? = some first)
    (lastAt : state.stack.sigma[position + edgeCount]? = some last)
    (edgeAvoids :
      ∀ {offset : Nat} {parent child : RawTokenAge},
        offset < edgeCount →
        state.stack.sigma[position + offset]? = some parent →
        state.stack.sigma[position + offset + 1]? = some child →
        tagHistory.CommitmentEdgeTargetAvoidingPath parent child forbidden) :
    tagHistory.CommitmentEdgeTargetAvoidingPath first last forbidden := by
  induction edgeCount generalizing position first last with
  | zero => omega
  | succ remaining induction =>
      have endBound :
          position + Nat.succ remaining < state.stack.sigma.length :=
        (List.getElem?_eq_some_iff.mp lastAt).choose
      have nextBound : position + 1 < state.stack.sigma.length := by
        omega
      let middle := state.stack.sigma[position + 1]
      have middleAt :
          state.stack.sigma[position + 1]? = some middle :=
        List.getElem?_eq_getElem nextBound
      rcases edgeAvoids (offset := 0) (parent := first) (child := middle)
          (by omega) (by simpa using firstAt) (by simpa using middleAt) with
        ⟨edgeParentEvent, edgeChildEvent, edgePath,
          edgeParentAt, edgeChildAt, edgeStarts, edgeFinishes, edgeOmits⟩
      by_cases noTail : remaining = 0
      · subst remaining
        have sameAge : middle = last := by
          apply Option.some.inj
          exact middleAt.symm.trans (by simpa using lastAt)
        subst last
        exact ⟨edgeParentEvent, edgeChildEvent, edgePath,
          edgeParentAt, edgeChildAt, edgeStarts, edgeFinishes, edgeOmits⟩
      · have indexEq :
            position + Nat.succ remaining = (position + 1) + remaining := by
          omega
        have tailLastAt :
            state.stack.sigma[(position + 1) + remaining]? = some last := by
          rw [← indexEq]
          exact lastAt
        have tailAvoids :
            ∀ {offset : Nat} {parent child : RawTokenAge},
              offset < remaining →
              state.stack.sigma[(position + 1) + offset]? = some parent →
              state.stack.sigma[(position + 1) + offset + 1]? = some child →
              tagHistory.CommitmentEdgeTargetAvoidingPath parent child
                forbidden := by
          intro offset parent child offsetLt parentAt childAt
          apply edgeAvoids (offset := offset + 1) (by omega)
          · have indexEq :
                position + (offset + 1) = (position + 1) + offset := by
              omega
            rw [indexEq]
            exact parentAt
          · have indexEq :
                position + (offset + 1) + 1 =
                  (position + 1) + offset + 1 := by
              omega
            rw [indexEq]
            exact childAt
        rcases induction (Nat.zero_lt_of_ne_zero noTail) middleAt tailLastAt
            tailAvoids with
          ⟨tailFirstEvent, lastEvent, tailPath, tailFirstAt, lastEventAt,
            tailStarts, tailFinishes, tailOmits⟩
        have sameMiddleEvent : edgeChildEvent = tailFirstEvent := by
          apply Option.some.inj
          exact edgeChildAt.symm.trans tailFirstAt
        subst tailFirstEvent
        have meeting : edgePath.finish = tailPath.start :=
          edgeFinishes.trans tailStarts.symm
        rcases edgePath.connectEraseAvoiding tailPath meeting edgeOmits
            tailOmits with
          ⟨path, pathStarts, pathFinishes, pathOmits⟩
        exact ⟨edgeParentEvent, lastEvent, path, edgeParentAt, lastEventAt,
          pathStarts.trans edgeStarts, pathFinishes.trans tailFinishes,
          pathOmits⟩

end CanonicalTagHistory
end SequentialFigure7
end ProofNetIR
