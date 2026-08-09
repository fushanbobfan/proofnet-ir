import ProofNetIR.SequentialFigure7CrossRepresentativeInvariant
import ProofNetIR.SequentialFigure7TouchCompleteness

namespace ProofNetIR

/-!
# Figure-7 older-event touch separation

This module restates structural source-left-region separation in the
proof-friendly language of exact historical reservation-event touches.  For
an authentic reservation event, structural disjointness always implies touch
exclusion.  The reverse direction uses structural touch completeness and
therefore requires a structurally well-formed certificate.

The history-level wrapper is exactly equivalent to the existing
`OlderSourceRegionSeparated` invariant under the same structural assumption.
It does not establish either invariant, preserve it through another rule,
construct a fresh source-left run, or prove scheduler progress, totality, or
worklist completeness.
-/

namespace SequentialFigure7

open SequentialSchedulerBridge
open SequentialUnification

/-- One exact reservation event has no touched occurrence in the other
complete source-left region. -/
def ReservationEvent.TouchSeparatedFrom
    {certificate : Certificate}
    (event : ReservationEvent certificate) (otherStart : Vertex) : Prop :=
  ∀ ⦃vertex : Vertex⦄,
    event.Touched vertex →
    SourceLeftRegionVertex certificate otherStart vertex →
    False

namespace SourceLeftRegionsDisjoint

/-- Structural source-region disjointness excludes every exact event touch
from the other region.  This direction needs no structural assumption. -/
theorem eventTouchSeparated
    {certificate : Certificate} {event : ReservationEvent certificate}
    {otherStart : Vertex}
    (disjoint :
      SourceLeftRegionsDisjoint certificate event.start otherStart) :
    event.TouchSeparatedFrom otherStart := by
  intro vertex touched otherRegion
  exact disjoint (event.touched_sourceLeftRegion touched) otherRegion

end SourceLeftRegionsDisjoint

namespace ReservationEvent.TouchSeparatedFrom

/-- Exact event-touch separation recovers structural region disjointness on
a structurally well-formed certificate. -/
theorem sourceLeftRegionsDisjoint
    {certificate : Certificate} {event : ReservationEvent certificate}
    {otherStart : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (separated : event.TouchSeparatedFrom otherStart) :
    SourceLeftRegionsDisjoint certificate event.start otherStart := by
  intro vertex eventRegion otherRegion
  exact separated
    (event.sourceLeftRegion_touched structural eventRegion) otherRegion

end ReservationEvent.TouchSeparatedFrom

namespace SourceLeftRegionsDisjoint

/-- For an authentic reservation event on a structurally well-formed
certificate, structural region disjointness is exactly touch exclusion. -/
theorem iff_eventTouchSeparated
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    (event : ReservationEvent certificate) (otherStart : Vertex) :
    SourceLeftRegionsDisjoint certificate event.start otherStart ↔
      event.TouchSeparatedFrom otherStart :=
  ⟨eventTouchSeparated, fun separated ↦
    separated.sourceLeftRegionsDisjoint structural⟩

end SourceLeftRegionsDisjoint

/-- Every strictly older ledger event is touch-separated from every future
candidate region. -/
structure OlderEventTouchSeparated
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history) : Prop where
  /-- A strictly older ledger event touched no occurrence in the future
  candidate's complete source-left region. -/
  event_candidate :
    ∀ {event : ReservationEvent certificate},
      event ∈ tagHistory.reservationLedger →
      ∀ candidate : FutureNewCandidateAt certificate state,
        state.core.representative event.rawAge <
            state.core.representative candidate.rawAge →
          event.TouchSeparatedFrom candidate.tensor.mate

namespace OlderSourceRegionSeparated

/-- Structural older-region separation always implies older-event touch
separation; this direction needs no structural well-formedness assumption. -/
theorem olderEventTouchSeparated
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    (separated : OlderSourceRegionSeparated tagHistory) :
    OlderEventTouchSeparated tagHistory := by
  refine { event_candidate := ?_ }
  intro event membership candidate older
  exact SourceLeftRegionsDisjoint.eventTouchSeparated
    (separated.event_candidate membership candidate older)

end OlderSourceRegionSeparated

namespace OlderEventTouchSeparated

/-- Touch separation recovers complete structural source-region separation
under structural well-formedness. -/
theorem olderSourceRegionSeparated
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    (structural : certificate.StructurallyWellFormed)
    (separated : OlderEventTouchSeparated tagHistory) :
    OlderSourceRegionSeparated tagHistory := by
  refine { event_candidate := ?_ }
  intro event membership candidate older
  exact
    (separated.event_candidate membership candidate older)
      |>.sourceLeftRegionsDisjoint structural

/-- On a structurally well-formed certificate, the existing structural
invariant and the proof-friendly historical-touch invariant are equivalent. -/
theorem iff_olderSourceRegionSeparated
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    (structural : certificate.StructurallyWellFormed) :
    OlderEventTouchSeparated tagHistory ↔
      OlderSourceRegionSeparated tagHistory :=
  ⟨olderSourceRegionSeparated structural,
    OlderSourceRegionSeparated.olderEventTouchSeparated⟩

end OlderEventTouchSeparated

end SequentialFigure7

end ProofNetIR
