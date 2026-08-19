/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7OlderEventFutureWorkTouchUnifyPayloadDischarge

/-! Runnable API checks for structural discharge of the `unifyPayload` head seam. -/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerBridge

#check UnifyPayloadStep.createdConclusionTouchSeparated
#check UnifyPayloadStep.createdHeadTouchSeparated
#check UnifyPayloadStep.olderEventFutureWorkTouchSeparated_of_structural

example
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    (step : UnifyPayloadStep certificate before after)
    (prior : CanonicalTagHistory certificate history)
    (structural : certificate.StructurallyWellFormed)
    (event : ReservationEvent certificate)
    (eventMembership : event ∈ prior.reservationLedger)
    (older :
      step.prepared.after.core.representative event.rawAge <
        step.prepared.after.core.representative step.previousBoundary)
    (touched : event.Touched step.consumer.conclusion) : False :=
  step.createdConclusionTouchSeparated prior structural event
    eventMembership older touched

example
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    (step : UnifyPayloadStep certificate before after)
    (prior : CanonicalTagHistory certificate history)
    (structural : certificate.StructurallyWellFormed) :
    UnifyPayloadCreatedHeadTouchSeparated prior step :=
  step.createdHeadTouchSeparated prior structural

example
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    (step : UnifyPayloadStep certificate before after)
    (prior : CanonicalTagHistory certificate history)
    (separated : OlderEventFutureWorkTouchSeparated prior)
    (structural : certificate.StructurallyWellFormed)
    {dispatch :
      DispatchStep certificate before (history.schedulerInvariant structural)
        ⟨.unifyPayload, after⟩} :
    OlderEventFutureWorkTouchSeparated
      (CanonicalTagHistory.later (dispatch := dispatch) prior
        (DispatchTagEvidence.unifyPayload step)) :=
  step.olderEventFutureWorkTouchSeparated_of_structural prior separated
    structural

example
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    (step : UnifyPayloadStep certificate before after)
    (prior : CanonicalTagHistory certificate history)
    (separated : OlderEventFutureWorkTouchSeparated prior)
    (structural : certificate.StructurallyWellFormed)
    {dispatch :
      DispatchStep certificate before (history.schedulerInvariant structural)
        ⟨.unifyPayload, after⟩}
    {event : ReservationEvent certificate}
    (eventMembership :
      event ∈ (CanonicalTagHistory.later (dispatch := dispatch) prior
        (DispatchTagEvidence.unifyPayload step)).reservationLedger)
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
  IO.println "Figure-7 UnifyPayload future-work touch discharge consumer passed."
