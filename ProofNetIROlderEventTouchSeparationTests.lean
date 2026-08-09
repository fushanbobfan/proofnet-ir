import ProofNetIR.SequentialFigure7OlderEventTouchSeparation

namespace ProofNetIR

open SequentialFigure7
open SequentialSchedulerBridge
open SequentialUnification

#check ReservationEvent.TouchSeparatedFrom
#check SourceLeftRegionsDisjoint.eventTouchSeparated
#check ReservationEvent.TouchSeparatedFrom.sourceLeftRegionsDisjoint
#check SourceLeftRegionsDisjoint.iff_eventTouchSeparated
#check OlderEventTouchSeparated
#check OlderEventTouchSeparated.event_candidate
#check OlderSourceRegionSeparated.olderEventTouchSeparated
#check OlderEventTouchSeparated.olderSourceRegionSeparated
#check OlderEventTouchSeparated.iff_olderSourceRegionSeparated

example {certificate : Certificate} {event : ReservationEvent certificate}
    {otherStart vertex : Vertex}
    (separated : event.TouchSeparatedFrom otherStart)
    (touched : event.Touched vertex)
    (region : SourceLeftRegionVertex certificate otherStart vertex) :
    False :=
  separated touched region

example {certificate : Certificate} {event : ReservationEvent certificate}
    {otherStart : Vertex}
    (disjoint :
      SourceLeftRegionsDisjoint certificate event.start otherStart) :
    event.TouchSeparatedFrom otherStart :=
  SourceLeftRegionsDisjoint.eventTouchSeparated disjoint

example {certificate : Certificate} {event : ReservationEvent certificate}
    {otherStart : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (separated : event.TouchSeparatedFrom otherStart) :
    SourceLeftRegionsDisjoint certificate event.start otherStart :=
  separated.sourceLeftRegionsDisjoint structural

example {certificate : Certificate} (event : ReservationEvent certificate)
    (otherStart : Vertex) (structural : certificate.StructurallyWellFormed) :
    SourceLeftRegionsDisjoint certificate event.start otherStart ↔
      event.TouchSeparatedFrom otherStart :=
  SourceLeftRegionsDisjoint.iff_eventTouchSeparated structural event
    otherStart

example {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    (property :
      ∀ {event : ReservationEvent certificate},
        event ∈ tagHistory.reservationLedger →
        ∀ candidate : FutureNewCandidateAt certificate state,
          state.core.representative event.rawAge <
              state.core.representative candidate.rawAge →
            event.TouchSeparatedFrom candidate.tensor.mate) :
    OlderEventTouchSeparated tagHistory :=
  { event_candidate := property }

example {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    (separated : OlderEventTouchSeparated tagHistory)
    {event : ReservationEvent certificate}
    (membership : event ∈ tagHistory.reservationLedger)
    (candidate : FutureNewCandidateAt certificate state)
    (older :
      state.core.representative event.rawAge <
        state.core.representative candidate.rawAge) :
    event.TouchSeparatedFrom candidate.tensor.mate :=
  separated.event_candidate membership candidate older

example {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    (separated : OlderSourceRegionSeparated tagHistory) :
    OlderEventTouchSeparated tagHistory :=
  separated.olderEventTouchSeparated

example {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    (structural : certificate.StructurallyWellFormed)
    (separated : OlderEventTouchSeparated tagHistory) :
    OlderSourceRegionSeparated tagHistory :=
  separated.olderSourceRegionSeparated structural

example {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    (structural : certificate.StructurallyWellFormed) :
    OlderEventTouchSeparated tagHistory ↔
      OlderSourceRegionSeparated tagHistory :=
  OlderEventTouchSeparated.iff_olderSourceRegionSeparated structural

end ProofNetIR

def main : IO Unit :=
  IO.println "Figure-7 older-event touch-separation API consumer passed"
