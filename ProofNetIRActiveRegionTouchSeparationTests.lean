/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7ActiveRegionTouchSeparation

/-!
# Figure-7 active-region touch-separation consumer

Checks the public anchor and touch-separation API through two concrete theorem consumers.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerBridge
open SequentialUnification

#check ActiveMateEventAnchor
#check CanonicalTagHistory.no_strictOlder_activeMateEventAnchor
#check CanonicalTagHistory.event_touchSeparatedFrom_active_sourceLeftRegion

/-- A raw-style consumer can construct the public anchor and invoke its strict-old exclusion
without first constructing an event-touch witness. -/
example {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate state)
    (guard : NewGuard certificate state)
    {event : ReservationEvent certificate}
    (eventMembership : event ∈ tagHistory.reservationLedger)
    (eventOlder :
      state.core.representative event.rawAge <
        state.core.representative guard.head.rawAge)
    (anchor : certificate.referenceSwitchingGraph.EdgeSimplePath)
    (anchorStarts : anchor.start = guard.tensor.mate)
    (anchorFinishes : anchor.finish = event.search.result.left)
    (anchorAvoids : guard.tensor.conclusion ∉ anchor.vertices) : False := by
  have eventAnchor : ActiveMateEventAnchor guard event :=
    ⟨anchor, anchorStarts, anchorFinishes, anchorAvoids⟩
  exact tagHistory.no_strictOlder_activeMateEventAnchor
    correct invariant guard eventMembership eventOlder eventAnchor

/-- The high-level theorem's returned `TouchSeparatedFrom` value applies directly to an exact
touch and source-left-region witness. -/
example {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate state)
    (guard : NewGuard certificate state)
    {event : ReservationEvent certificate}
    (eventMembership : event ∈ tagHistory.reservationLedger)
    {vertex : Vertex}
    (touched : event.Touched vertex)
    (region :
      SourceLeftRegionVertex certificate guard.tensor.mate vertex) : False :=
  (tagHistory.event_touchSeparatedFrom_active_sourceLeftRegion
    correct invariant guard eventMembership) touched region

#print axioms CanonicalTagHistory.no_strictOlder_activeMateEventAnchor
#print axioms CanonicalTagHistory.event_touchSeparatedFrom_active_sourceLeftRegion

end SequentialFigure7
end ProofNetIR

/- Run the standalone active-region touch-separation API consumer. -/
def main : IO Unit :=
  IO.println "Figure-7 active-region touch-separation API consumer passed."
