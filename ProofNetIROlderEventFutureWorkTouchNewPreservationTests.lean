/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7OlderEventFutureWorkTouchNewPreservation

namespace ProofNetIR

open SequentialFigure7
open SequentialSchedulerBridge

#check NewStep.olderEventFutureWorkTouchSeparated

example
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    {invariant : SchedulerInvariant certificate before}
    {dispatch : DispatchStep certificate before invariant ⟨.new, after⟩}
    (step : NewStep certificate before after)
    (prior : CanonicalTagHistory certificate history)
    (separated : OlderEventFutureWorkTouchSeparated prior) :
    OlderEventFutureWorkTouchSeparated
      (CanonicalTagHistory.later (dispatch := dispatch) prior
        (DispatchTagEvidence.new step)) :=
  step.olderEventFutureWorkTouchSeparated prior separated

example
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    {invariant : SchedulerInvariant certificate before}
    {dispatch : DispatchStep certificate before invariant ⟨.new, after⟩}
    (step : NewStep certificate before after)
    (prior : CanonicalTagHistory certificate history)
    (separated : OlderEventFutureWorkTouchSeparated prior)
    {event : ReservationEvent certificate}
    (membership :
      event ∈ (CanonicalTagHistory.later (dispatch := dispatch) prior
        (DispatchTagEvidence.new step)).reservationLedger)
    (candidate : FutureNewCandidateAt certificate after)
    (older :
      after.core.representative event.rawAge <
        after.core.representative candidate.rawAge) :
    ¬ event.Touched candidate.head :=
  (step.olderEventFutureWorkTouchSeparated prior separated).event_candidate
    membership candidate older

end ProofNetIR

/-- Runtime smoke entry point for the Figure-7 `new` future-work touch
separation preservation consumer. -/
def main : IO Unit :=
  IO.println "Figure-7 new future-work touch preservation consumer passed."
