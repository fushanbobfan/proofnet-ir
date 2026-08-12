/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7OlderEventFutureWorkTouchSeparation

namespace ProofNetIR

open SequentialFigure7
open SequentialSchedulerBridge

#check OlderEventFutureWorkTouchSeparated
#check OlderEventFutureWorkTouchSeparated.event_candidate
#check OlderEventTouchSeparated.strict_candidateConclusion_untouched
#check empty_olderEventFutureWorkTouchSeparated
#check InitialReservationStep.olderEventFutureWorkTouchSeparated
#check PreparedStep.olderEventFutureWorkTouchSeparated
#check ConclStep.olderEventFutureWorkTouchSeparated
#check NopStep.olderEventFutureWorkTouchSeparated

example
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (separated :
      ∀ {event : ReservationEvent certificate},
        event ∈ tagHistory.reservationLedger →
        ∀ candidate : FutureNewCandidateAt certificate state,
          state.core.representative event.rawAge <
              state.core.representative candidate.rawAge →
            ¬ event.Touched candidate.head) :
    OlderEventFutureWorkTouchSeparated tagHistory :=
  { event_candidate := separated }

example
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    (separated : OlderEventFutureWorkTouchSeparated tagHistory)
    {event : ReservationEvent certificate}
    (membership : event ∈ tagHistory.reservationLedger)
    (candidate : FutureNewCandidateAt certificate state)
    (older :
      state.core.representative event.rawAge <
        state.core.representative candidate.rawAge) :
    ¬ event.Touched candidate.head :=
  separated.event_candidate membership candidate older

example
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    (regionSeparated : OlderEventTouchSeparated tagHistory)
    (headSeparated : OlderEventFutureWorkTouchSeparated tagHistory)
    (structural : certificate.StructurallyWellFormed)
    {event : ReservationEvent certificate}
    (membership : event ∈ tagHistory.reservationLedger)
    (candidate : FutureNewCandidateAt certificate state)
    (older :
      state.core.representative event.rawAge <
        state.core.representative candidate.rawAge) :
    ¬ event.Touched candidate.tensor.conclusion :=
  regionSeparated.strict_candidateConclusion_untouched headSeparated structural
    membership candidate older

example (certificate : Certificate) :
    OlderEventFutureWorkTouchSeparated
      (CanonicalTagHistory.empty :
        CanonicalTagHistory certificate
          (ExecutedHistory.empty : ExecutedHistory certificate
            (ReservationState.empty certificate))) :=
  empty_olderEventFutureWorkTouchSeparated certificate

example
    {certificate : Certificate} {after : ReservationState} {start : Vertex}
    (step : InitialReservationStep certificate after start)
    (structural : certificate.StructurallyWellFormed) :
    OlderEventFutureWorkTouchSeparated (CanonicalTagHistory.init step) :=
  InitialReservationStep.olderEventFutureWorkTouchSeparated step structural

example
    {certificate : Certificate} {before after : ReservationState}
    (step : PreparedStep before) (outputEquation : after = step.after)
    {beforeHistory : ExecutedHistory certificate before}
    (beforeTags : CanonicalTagHistory certificate beforeHistory)
    (separated : OlderEventFutureWorkTouchSeparated beforeTags)
    {afterHistory : ExecutedHistory certificate after}
    (afterTags : CanonicalTagHistory certificate afterHistory)
    (ledgerEquation :
      afterTags.reservationLedger = beforeTags.reservationLedger) :
    OlderEventFutureWorkTouchSeparated afterTags :=
  step.olderEventFutureWorkTouchSeparated outputEquation beforeTags separated
    afterTags ledgerEquation

example
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    {invariant : SchedulerInvariant certificate before}
    {dispatch : DispatchStep certificate before invariant ⟨.concl, after⟩}
    (step : ConclStep certificate before after)
    (prior : CanonicalTagHistory certificate history)
    (separated : OlderEventFutureWorkTouchSeparated prior) :
    OlderEventFutureWorkTouchSeparated
      (CanonicalTagHistory.later (dispatch := dispatch) prior
        (DispatchTagEvidence.concl step)) :=
  step.olderEventFutureWorkTouchSeparated prior separated

example
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    {invariant : SchedulerInvariant certificate before}
    {dispatch : DispatchStep certificate before invariant ⟨.nop, after⟩}
    (step : NopStep certificate before after)
    (prior : CanonicalTagHistory certificate history)
    (separated : OlderEventFutureWorkTouchSeparated prior) :
    OlderEventFutureWorkTouchSeparated
      (CanonicalTagHistory.later (dispatch := dispatch) prior
        (DispatchTagEvidence.nop step)) :=
  step.olderEventFutureWorkTouchSeparated prior separated

end ProofNetIR

/-- Executable smoke entrypoint for the older-event future-work touch API. -/
def main : IO Unit :=
  IO.println "Figure-7 older-event future-work touch consumer passed."
