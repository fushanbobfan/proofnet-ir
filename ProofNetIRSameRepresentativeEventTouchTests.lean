import ProofNetIR.SequentialFigure7SameRepresentativeEventTouch

namespace ProofNetIR

open SequentialUnification
open SequentialFigure7
open SequentialSchedulerBridge

#check SourceLeftChain.reachable_to_last_of_mem
#check ReservationEvent.leftEndpoint_sourceLeftRegion_of_touched
#check NewGuard.sourceLeftRegion_formulaComplexity_lt_conclusion
#check CanonicalTagHistory.not_event_touch_of_sameRepresentative

example {certificate : Certificate} {before : ReservationState}
    {history : ExecutedHistory certificate before}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate before)
    (guard : NewGuard certificate before)
    {event : ReservationEvent certificate}
    (eventMembership : event ∈ tagHistory.reservationLedger)
    (sameRepresentative :
      before.core.representative event.rawAge =
        before.core.representative guard.head.rawAge)
    {vertex : Vertex}
    (eventTouched : event.Touched vertex)
    (candidateRegion :
      SourceLeftRegionVertex certificate guard.tensor.mate vertex) : False :=
  tagHistory.not_event_touch_of_sameRepresentative correct invariant guard
    eventMembership sameRepresentative eventTouched candidateRegion

end ProofNetIR

def main : IO Unit :=
  IO.println "Figure-7 same-representative event-touch consumers passed"
