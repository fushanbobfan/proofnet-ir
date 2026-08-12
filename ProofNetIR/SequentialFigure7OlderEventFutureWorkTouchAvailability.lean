/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7OlderEventFutureWorkTouchNewPreservation
import ProofNetIR.SequentialFigure7OlderEventFutureWorkTouchWaitDischarge
import ProofNetIR.SequentialFigure7OlderEventFutureWorkTouchForwardDischarge
import ProofNetIR.SequentialFigure7OlderEventFutureWorkTouchUnifyPayloadDischarge

/-!
# Global availability of older-event future-work head separation

Every canonical dispatcher history over a structurally well-formed certificate
satisfies strict older-event separation from every queued future-`new` head.
The proof follows the supplied history: empty and initialization establish the
base cases, while the six successful rule families preserve the invariant.

This result classifies already-certified histories only. It does not enlarge
dispatcher reachability, prove that another rule is enabled, supply mate- or
source-region separation, cover equal representative boundaries, or establish
progress, totality, completeness, fallback removal, token-age scheduling, or
complexity.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerBridge

namespace CanonicalTagHistory

/-- Strict older-event future-work head-touch separation is available for
every canonical history over a structurally well-formed certificate.

This theorem classifies an already-supplied history. It does not enlarge
reachability, prove another branch enabled, provide mate/source-region or
raw-mark separation, cover equal-representative boundaries, or establish
progress, totality, completeness, fallback removal, token-age scheduling, or
complexity. -/
theorem olderEventFutureWorkTouchSeparated
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (structural : certificate.StructurallyWellFormed) :
    OlderEventFutureWorkTouchSeparated tagHistory := by
  induction tagHistory with
  | empty =>
      exact empty_olderEventFutureWorkTouchSeparated certificate
  | init step =>
      exact
        SequentialFigure7.InitialReservationStep.olderEventFutureWorkTouchSeparated
          step structural
  | later prior evidence induction =>
      cases evidence with
      | concl step =>
          exact step.olderEventFutureWorkTouchSeparated prior induction
      | nop step =>
          exact step.olderEventFutureWorkTouchSeparated prior induction
      | new step =>
          exact step.olderEventFutureWorkTouchSeparated prior induction
      | wait step =>
          exact step.olderEventFutureWorkTouchSeparated_of_structural
            prior induction structural
      | forward step =>
          exact step.olderEventFutureWorkTouchSeparated_of_structural
            prior induction structural
      | unifyPayload step =>
          exact step.olderEventFutureWorkTouchSeparated_of_structural
            prior induction structural

end CanonicalTagHistory
end SequentialFigure7
end ProofNetIR
