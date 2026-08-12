/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7OlderEventFutureWorkTouchWaitPreservation

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerBridge

#check WaitCreatedHeadTouchSeparated
#check WaitStep.olderEventFutureWorkTouchSeparated

example
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    {invariant : SchedulerInvariant certificate before}
    {dispatch : DispatchStep certificate before invariant ⟨.wait, after⟩}
    (step : WaitStep certificate before after)
    (prior : CanonicalTagHistory certificate history)
    (separated : OlderEventFutureWorkTouchSeparated prior)
    (createdSeparated : WaitCreatedHeadTouchSeparated prior step) :
    OlderEventFutureWorkTouchSeparated
      (CanonicalTagHistory.later (dispatch := dispatch) prior
        (DispatchTagEvidence.wait step)) :=
  step.olderEventFutureWorkTouchSeparated prior separated createdSeparated

example
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    {invariant : SchedulerInvariant certificate before}
    {dispatch : DispatchStep certificate before invariant ⟨.wait, after⟩}
    (step : WaitStep certificate before after)
    (prior : CanonicalTagHistory certificate history)
    (separated : OlderEventFutureWorkTouchSeparated prior)
    (createdSeparated : WaitCreatedHeadTouchSeparated prior step)
    {event : ReservationEvent certificate}
    (eventMembership :
      event ∈ (CanonicalTagHistory.later (dispatch := dispatch) prior
        (DispatchTagEvidence.wait step)).reservationLedger)
    (candidate : FutureNewCandidateAt certificate after)
    (older :
      after.core.representative event.rawAge <
        after.core.representative candidate.rawAge) :
    ¬ event.Touched candidate.head :=
  (step.olderEventFutureWorkTouchSeparated prior separated createdSeparated)
    |>.event_candidate eventMembership candidate older

end SequentialFigure7
end ProofNetIR

def main : IO Unit :=
  IO.println "Figure-7 wait future-work touch preservation consumer passed."
