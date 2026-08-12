/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7OlderEventFutureWorkTouchForwardDischarge

/-! Runnable API checks for structural discharge of the `forward` head seam. -/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerBridge

#check ForwardStep.createdHeadTouchSeparated
#check ForwardStep.olderEventFutureWorkTouchSeparated_of_structural

example
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    (step : ForwardStep certificate before after)
    (prior : CanonicalTagHistory certificate history)
    (structural : certificate.StructurallyWellFormed) :
    ForwardCreatedHeadTouchSeparated prior step :=
  step.createdHeadTouchSeparated prior structural

example
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    (step : ForwardStep certificate before after)
    (prior : CanonicalTagHistory certificate history)
    (separated : OlderEventFutureWorkTouchSeparated prior)
    (structural : certificate.StructurallyWellFormed)
    {dispatch :
      DispatchStep certificate before (history.schedulerInvariant structural)
        ⟨.forward, after⟩} :
    OlderEventFutureWorkTouchSeparated
      (CanonicalTagHistory.later (dispatch := dispatch) prior
        (DispatchTagEvidence.forward step)) :=
  step.olderEventFutureWorkTouchSeparated_of_structural prior separated
    structural

example
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    (step : ForwardStep certificate before after)
    (prior : CanonicalTagHistory certificate history)
    (separated : OlderEventFutureWorkTouchSeparated prior)
    (structural : certificate.StructurallyWellFormed)
    {dispatch :
      DispatchStep certificate before (history.schedulerInvariant structural)
        ⟨.forward, after⟩}
    {event : ReservationEvent certificate}
    (eventMembership :
      event ∈ (CanonicalTagHistory.later (dispatch := dispatch) prior
        (DispatchTagEvidence.forward step)).reservationLedger)
    (candidate : FutureNewCandidateAt certificate after)
    (older :
      after.core.representative event.rawAge <
        after.core.representative candidate.rawAge) :
    ¬ event.Touched candidate.head :=
  (step.olderEventFutureWorkTouchSeparated_of_structural prior separated
      structural)
    |>.event_candidate eventMembership candidate older

end SequentialFigure7
end ProofNetIR

def main : IO Unit :=
  IO.println "Figure-7 Forward future-work touch discharge consumer passed."
