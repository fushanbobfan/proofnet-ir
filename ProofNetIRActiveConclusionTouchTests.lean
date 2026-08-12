import ProofNetIR.SequentialFigure7ActiveConclusionTouch

namespace ProofNetIR

open SequentialFigure7
open SequentialSchedulerBridge

/- Both public declarations are consumed below through concrete examples. -/
#check ReservationEvent.touched_candidateConclusion_cases
#check CanonicalTagHistory.active_conclusion_touch_implies_head_touch

example {certificate : Certificate} {state : ReservationState}
    (structural : certificate.StructurallyWellFormed)
    (event : ReservationEvent certificate)
    (candidate : FutureNewCandidateAt certificate state)
    (touched : event.Touched candidate.tensor.conclusion) :
    event.Touched candidate.tensor.mate ∨ event.Touched candidate.head :=
  event.touched_candidateConclusion_cases structural candidate touched

example {certificate : Certificate} {before : ReservationState}
    {history : ExecutedHistory certificate before}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate before)
    (guard : NewGuard certificate before)
    (separated : OlderEventTouchSeparated tagHistory)
    {event : ReservationEvent certificate}
    (membership : event ∈ tagHistory.reservationLedger)
    (conclusionTouched : event.Touched guard.tensor.conclusion) :
    event.Touched guard.head.vertex :=
  tagHistory.active_conclusion_touch_implies_head_touch correct invariant guard
    separated membership conclusionTouched

end ProofNetIR

def main : IO Unit :=
  IO.println "Figure-7 active tensor-conclusion touch API consumer passed."
