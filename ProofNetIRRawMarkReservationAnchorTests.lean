import ProofNetIR.SequentialFigure7RawMarkReservationAnchor

namespace ProofNetIR

/-!
# Figure-7 raw-mark reservation-anchor consumer

This consumer exercises the single public anchor theorem.  It recovers local
same-component reference paths only; no cross-component composition, target
avoidance, raw seam, or progress result is consumed.
-/

open SequentialFigure7
open SequentialSchedulerBridge
open SequentialSchedulerState

#check CanonicalTagHistory.rawMarked_reservationEvent_referenceAnchors

/- Consume the exact event, common owned carrier, and both local paths. -/
example {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (invariant : SchedulerInvariant certificate state)
    {vertex : Vertex} {rawAge : RawTokenAge}
    (marked : state.core.marks[vertex]? = some (some rawAge)) :
    ∃ (event : ReservationEvent certificate) (component : UnificationComponent)
        (owned : List Nat)
        (leftPath rightPath : certificate.referenceSwitchingGraph.EdgeSimplePath),
      tagHistory.reservationLedger[rawAge]? = some event ∧
        event.rawAge = rawAge ∧
        state.core.components[state.core.representative rawAge]? =
          some (some component) ∧
        vertex ∈ owned ∧
        event.search.result.left ∈ owned ∧
        event.search.result.right ∈ owned ∧
        leftPath.start = vertex ∧
        leftPath.finish = event.search.result.left ∧
        (∀ current ∈ leftPath.vertices, current ∈ owned) ∧
        rightPath.start = vertex ∧
        rightPath.finish = event.search.result.right ∧
        ∀ current ∈ rightPath.vertices, current ∈ owned := by
  rcases tagHistory.rawMarked_reservationEvent_referenceAnchors
      invariant marked with
    ⟨event, component, _eventUsed, _forestUsed, owned, leftPath,
      rightPath, eventLookup, eventRawAge, componentLookup,
      _eventDerivation, _eventLink, _eventWitness, _accounted, vertexOwned,
      leftOwned, rightOwned, leftStarts, leftFinishes, leftContained,
      rightStarts, rightFinishes, rightContained⟩
  exact ⟨event, component, owned, leftPath, rightPath, eventLookup,
    eventRawAge, componentLookup, vertexOwned, leftOwned, rightOwned,
    leftStarts, leftFinishes, leftContained, rightStarts, rightFinishes,
    rightContained⟩

end ProofNetIR

/-- Run the standalone raw-mark reservation-anchor API smoke consumer. -/
def main : IO Unit :=
  IO.println "Figure-7 raw-mark reservation-anchor API consumer passed."
