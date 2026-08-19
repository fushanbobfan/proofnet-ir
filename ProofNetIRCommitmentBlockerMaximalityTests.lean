/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7CommitmentBlockerMaximality

/-!
# Figure-7 commitment blocker-maximality consumer

Destructures and reconstructs both public result branches.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerBridge
open SequentialSchedulerState

#check CanonicalTagHistory.strictOlder_commitmentPath_or_equalCallbackFailure

example
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate state)
    (guard : NewGuard certificate state)
    {event : ReservationEvent certificate}
    (membership : event ∈ tagHistory.reservationLedger)
    (older :
      state.core.representative event.rawAge <
        state.core.representative guard.head.rawAge) :
    tagHistory.CommitmentEdgeTargetAvoidingPath
        (state.core.representative event.rawAge) guard.head.rawAge
        guard.tensor.conclusion ∨
      ∃ childEvent : ReservationEvent certificate,
        ∃ beforeTrace afterTrace,
          childEvent ∈ tagHistory.reservationLedger ∧
            childEvent.rawAge = guard.head.rawAge ∧
            guard.tensor.side = .storedLeft ∧
            childEvent.search.result.trace =
              beforeTrace ++ guard.tensor.conclusion ::
                guard.head.vertex :: afterTrace := by
  rcases
      tagHistory.strictOlder_commitmentPath_or_equalCallbackFailure
        correct invariant guard membership older with
    avoiding | callbackFailure
  · rcases avoiding with
      ⟨parentEvent, childEvent, path, parentLookup, childLookup,
        starts, finishes, avoids⟩
    exact Or.inl
      ⟨parentEvent, childEvent, path, parentLookup, childLookup,
        starts, finishes, avoids⟩
  · rcases callbackFailure with
      ⟨childEvent, beforeTrace, afterTrace, childMembership, childAge,
        storedLeft, traceSplit⟩
    exact Or.inr
      ⟨childEvent, beforeTrace, afterTrace, childMembership, childAge,
        storedLeft, traceSplit⟩

end SequentialFigure7
end ProofNetIR

def main : IO Unit :=
  IO.println "Figure-7 commitment blocker-maximality consumer passed."
