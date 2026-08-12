/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7StrictOlderSigmaSplit
import ProofNetIR.SequentialFigure7StrictCommitmentTargetAvoidance

/-! Runnable API checks for the strict older `sigma` split and prefix use. -/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerBridge

#check StrictOlderSigmaSplit
#check CanonicalTagHistory.strictOlderSigmaSplit

example
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (invariant : SchedulerInvariant certificate state)
    {event : ReservationEvent certificate}
    (eventMembership : event ∈ tagHistory.reservationLedger)
    (candidate : FutureNewCandidateAt certificate state)
    (older :
      state.core.representative event.rawAge <
        state.core.representative candidate.rawAge) :
    StrictOlderSigmaSplit state
      (state.core.representative event.rawAge) candidate.rawAge :=
  tagHistory.strictOlderSigmaSplit invariant eventMembership candidate older

example
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (invariant : SchedulerInvariant certificate state)
    (regionSeparated : OlderEventTouchSeparated tagHistory)
    (headSeparated : OlderEventFutureWorkTouchSeparated tagHistory)
    {event : ReservationEvent certificate}
    (eventMembership : event ∈ tagHistory.reservationLedger)
    (candidate : FutureNewCandidateAt certificate state)
    (older :
      state.core.representative event.rawAge <
        state.core.representative candidate.rawAge) :
    ∃ position edgeCount predecessor,
      state.stack.sigma[position]? =
          some (state.core.representative event.rawAge) ∧
        state.stack.sigma[position + edgeCount]? = some predecessor ∧
        state.stack.sigma[position + edgeCount + 1]? =
          some candidate.rawAge ∧
        state.core.representative predecessor <
          state.core.representative candidate.rawAge ∧
        (edgeCount = 0 ∨
          tagHistory.CommitmentEdgeTargetAvoidingPath
            (state.core.representative event.rawAge) predecessor
            candidate.tensor.conclusion) := by
  rcases tagHistory.strictOlderSigmaSplit invariant eventMembership candidate
      older with
    ⟨position, edgeCount, predecessor, firstAt, predecessorAt,
      candidateAt, predecessorOlder⟩
  refine ⟨position, edgeCount, predecessor, firstAt, predecessorAt,
    candidateAt, predecessorOlder, ?_⟩
  by_cases zero : edgeCount = 0
  · exact Or.inl zero
  · apply Or.inr
    apply
      tagHistory.commitmentInterval_referencePath_avoiding_of_lastOlder
        invariant regionSeparated headSeparated candidate
        (position := position) (edgeCount := edgeCount)
        (first := state.core.representative event.rawAge)
        (last := predecessor)
    · omega
    · exact firstAt
    · exact predecessorAt
    · exact predecessorOlder

end SequentialFigure7
end ProofNetIR

def main : IO Unit :=
  IO.println "Figure-7 strict older sigma-split consumer passed."
