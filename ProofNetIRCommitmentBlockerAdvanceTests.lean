/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7CommitmentBlockerAdvance

/-! # Figure-7 commitment blocker-advance consumer -/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerBridge
open SequentialSchedulerState

#check CanonicalTagHistory.strictOlder_commitmentPath_or_advance_or_equalCallbackFailure

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
      (∃ higherEvent : ReservationEvent certificate,
        state.core.representative event.rawAge <
            state.core.representative higherEvent.rawAge ∧
          state.core.representative higherEvent.rawAge <
            state.core.representative guard.head.rawAge ∧
          higherEvent.Touched guard.tensor.mate) ∨
      ∃ childEvent : ReservationEvent certificate,
        ∃ beforeTrace afterTrace,
          childEvent.rawAge = guard.head.rawAge ∧
            guard.tensor.side = .storedLeft ∧
            childEvent.search.result.trace =
              beforeTrace ++ guard.tensor.conclusion ::
                guard.head.vertex :: afterTrace := by
  rcases
      tagHistory.strictOlder_commitmentPath_or_advance_or_equalCallbackFailure
        correct invariant guard membership older with
    avoiding | advanceOrCallbackFailure
  · exact Or.inl avoiding
  · rcases advanceOrCallbackFailure with advance | callbackFailure
    · rcases advance with
        ⟨higherEvent, _higherMembership, oldBelowHigher, higherBelowHead,
          mateTouched⟩
      exact Or.inr (Or.inl
        ⟨higherEvent, oldBelowHigher, higherBelowHead, mateTouched⟩)
    · rcases callbackFailure with
        ⟨childEvent, beforeTrace, afterTrace, _childMembership, childAge,
          storedLeft, callbackFailure⟩
      exact Or.inr (Or.inr
        ⟨childEvent, beforeTrace, afterTrace, childAge, storedLeft,
          callbackFailure⟩)

end SequentialFigure7
end ProofNetIR

def main : IO Unit :=
  IO.println "Figure-7 commitment blocker-advance consumer passed."
