import ProofNetIR.SequentialFigure7ActiveRegionTouchOrder

namespace ProofNetIR

open SequentialFigure7
open SequentialSchedulerBridge
open SequentialUnification

#check CanonicalTagHistory.event_touch_active_region_implies_representative_lt
#check CanonicalTagHistory.event_touch_active_region_implies_rawAge_lt
#check
  CanonicalTagHistory.event_touchSeparatedFrom_active_sourceLeftRegion_of_olderEventTouchSeparated
#check CanonicalTagHistory.active_sourceLeftRegion_tagFresh_of_olderEventTouchSeparated
#check CanonicalTagHistory.active_sourceLeftRegion_tagFresh_of_olderSourceRegionSeparated

example {certificate : Certificate} {before : ReservationState}
    {history : ExecutedHistory certificate before}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate before)
    (guard : NewGuard certificate before)
    {event : ReservationEvent certificate}
    (membership : event ∈ tagHistory.reservationLedger)
    {vertex : Vertex}
    (touched : event.Touched vertex)
    (region :
      SourceLeftRegionVertex certificate guard.tensor.mate vertex) :
    before.core.representative event.rawAge <
      before.core.representative guard.head.rawAge :=
  tagHistory.event_touch_active_region_implies_representative_lt
    correct invariant guard membership touched region

example {certificate : Certificate} {before : ReservationState}
    {history : ExecutedHistory certificate before}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate before)
    (guard : NewGuard certificate before)
    {event : ReservationEvent certificate}
    (membership : event ∈ tagHistory.reservationLedger)
    {vertex : Vertex}
    (touched : event.Touched vertex)
    (region :
      SourceLeftRegionVertex certificate guard.tensor.mate vertex) :
    event.rawAge < guard.head.rawAge :=
  tagHistory.event_touch_active_region_implies_rawAge_lt
    correct invariant guard membership touched region

example {certificate : Certificate} {before : ReservationState}
    {history : ExecutedHistory certificate before}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate before)
    (guard : NewGuard certificate before)
    (separated : OlderEventTouchSeparated tagHistory)
    {event : ReservationEvent certificate}
    (membership : event ∈ tagHistory.reservationLedger) :
    event.TouchSeparatedFrom guard.tensor.mate :=
  tagHistory.event_touchSeparatedFrom_active_sourceLeftRegion_of_olderEventTouchSeparated
    correct invariant guard separated membership

example {certificate : Certificate} {before : ReservationState}
    {history : ExecutedHistory certificate before}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate before)
    (guard : NewGuard certificate before)
    (separated : OlderEventTouchSeparated tagHistory)
    {vertex : Vertex}
    (region :
      SourceLeftRegionVertex certificate guard.tensor.mate vertex) :
    before.tags[vertex]? = some false :=
  tagHistory.active_sourceLeftRegion_tagFresh_of_olderEventTouchSeparated
    correct invariant guard separated region

example {certificate : Certificate} {before : ReservationState}
    {history : ExecutedHistory certificate before}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate before)
    (guard : NewGuard certificate before)
    (separated : OlderSourceRegionSeparated tagHistory)
    {vertex : Vertex}
    (region :
      SourceLeftRegionVertex certificate guard.tensor.mate vertex) :
    before.tags[vertex]? = some false :=
  tagHistory.active_sourceLeftRegion_tagFresh_of_olderSourceRegionSeparated
    correct invariant guard separated region

end ProofNetIR

def main : IO Unit :=
  IO.println "Figure-7 active-region touch-order API consumer passed."
