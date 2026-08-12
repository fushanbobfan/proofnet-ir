/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7OlderEventFutureWorkTouchAvailability

/-! Runnable API checks for global older-event future-work touch separation. -/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerBridge

#check CanonicalTagHistory.olderEventFutureWorkTouchSeparated

example
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (structural : certificate.StructurallyWellFormed) :
    OlderEventFutureWorkTouchSeparated tagHistory :=
  tagHistory.olderEventFutureWorkTouchSeparated structural

example
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (structural : certificate.StructurallyWellFormed)
    {event : ReservationEvent certificate}
    (eventMembership : event ∈ tagHistory.reservationLedger)
    (candidate : FutureNewCandidateAt certificate state)
    (older :
      state.core.representative event.rawAge <
        state.core.representative candidate.rawAge) :
    ¬ event.Touched candidate.head :=
  (tagHistory.olderEventFutureWorkTouchSeparated structural)
    |>.event_candidate eventMembership candidate older

end SequentialFigure7
end ProofNetIR

def main : IO Unit :=
  IO.println "Global future-work touch availability consumer passed."
