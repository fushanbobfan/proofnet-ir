/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialComponentReferenceGeometry
import ProofNetIR.SequentialFigure7BlockerHistory
import ProofNetIR.SequentialFigure7ReservationRealization

namespace ProofNetIR

/-!
# Figure-7 raw-mark reservation anchors

Every concrete raw mark in a canonical dispatcher history is anchored to the
exact chronological reservation event at that immutable raw age.  Final
component provenance then places the marked occurrence and both endpoints of
the event's submitted axiom in one exact owned-occurrence carrier.  The
reference switching supplies paths from the marked occurrence to both
endpoints that remain inside that carrier.

This is local same-component geometry only.  It assumes neither declarative
correctness nor reference-switching acyclicity, and it does not compose paths
across commitment-spine components, prove target avoidance or a raw seam,
establish dispatcher progress, or remove the recursive fallback.
-/

namespace SequentialFigure7

open SequentialSchedulerBridge
open SequentialSchedulerState

namespace CanonicalTagHistory

/-- Anchor one concrete raw mark to its exact reservation event, final live
component, and owned-contained reference paths to both submitted axiom
endpoints.

This theorem supplies only local same-component anchors.  It does not assume
`DeclarativelyCorrect` or acyclicity, compose paths across components, prove
target avoidance or a raw seam, or establish progress. -/
theorem rawMarked_reservationEvent_referenceAnchors
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (invariant : SchedulerInvariant certificate state)
    {vertex : Vertex} {rawAge : RawTokenAge}
    (marked : state.core.marks[vertex]? = some (some rawAge)) :
    ∃ (event : ReservationEvent certificate)
        (component : UnificationComponent) (eventUsed forestUsed owned : List Nat)
        (leftPath rightPath : certificate.referenceSwitchingGraph.EdgeSimplePath),
      tagHistory.reservationLedger[rawAge]? = some event ∧
        event.rawAge = rawAge ∧
        state.core.components[state.core.representative rawAge]? =
          some (some component) ∧
        certificate.OccurrenceDerivation component.tree component.frontier
          eventUsed owned ∧
        event.linkIndex ∈ eventUsed ∧
        certificate.ComponentOccurrenceWitness component forestUsed owned ∧
        Certificate.OwnedOccurrenceAccounted state.core
          (state.core.representative rawAge) component owned ∧
        vertex ∈ owned ∧
        event.search.result.left ∈ owned ∧
        event.search.result.right ∈ owned ∧
        leftPath.start = vertex ∧
        leftPath.finish = event.search.result.left ∧
        (∀ current ∈ leftPath.vertices, current ∈ owned) ∧
        rightPath.start = vertex ∧
        rightPath.finish = event.search.result.right ∧
        ∀ current ∈ rightPath.vertices, current ∈ owned := by
  have stackMarked : state.stack.marks[vertex]? = some (some rawAge) := by
    rw [← invariant.realizesSigma.marks_eq]
    exact marked
  have rawAgeBound : rawAge < state.stack.nextAge :=
    invariant.stack_wellShaped.assigned_age_bound vertex rawAge stackMarked
  rcases tagHistory.reservationLedger_eventAtRawAge rawAge rawAgeBound with
    ⟨event, eventLookup, eventRawAge⟩
  have eventMembership : event ∈ tagHistory.reservationLedger :=
    List.mem_of_getElem? eventLookup
  rcases tagHistory.reservationLedger_axiomEndpoints_accounted
      invariant.structural eventMembership with
    ⟨eventComponent, eventUsed, eventForestUsed, eventOwned,
      eventComponentLookup, eventDerivation, eventLink, eventWitness,
      eventAccounted, eventLeftOwned, eventRightOwned⟩
  rcases SchedulerInvariant.exactMarkedOccurrenceOwner invariant marked with
    ⟨ownerRawAge, ownerIndex, ownerComponent, ownerUsed, ownerOwned,
      ownerMarked, ownerRepresentative, ownerLookup, ownerWitness,
      _ownerAccounted, vertexOwnerOwned⟩
  have ownerRawAgeEq : ownerRawAge = rawAge := by
    exact Option.some.inj (Option.some.inj (ownerMarked.symm.trans marked))
  subst ownerRawAge
  have eventComponentLookupAtRawAge :
      state.core.components[state.core.representative rawAge]? =
        some (some eventComponent) := by
    simpa [eventRawAge] using eventComponentLookup
  have ownerLookupAtRawAge :
      state.core.components[state.core.representative rawAge]? =
        some (some ownerComponent) := by
    simpa [ownerRepresentative] using ownerLookup
  have componentEq : ownerComponent = eventComponent := by
    exact Option.some.inj
      (Option.some.inj
        (ownerLookupAtRawAge.symm.trans eventComponentLookupAtRawAge))
  subst ownerComponent
  have ownedEq : ownerOwned = eventOwned :=
    Certificate.OccurrenceDerivation.owned_unique invariant.structural
      ownerWitness.derivation eventDerivation
  have vertexEventOwned : vertex ∈ eventOwned := by
    rw [← ownedEq]
    exact vertexOwnerOwned
  rcases eventWitness.referencePath_within_owned
      vertexEventOwned eventLeftOwned with
    ⟨leftPath, leftStarts, leftFinishes, leftOwned⟩
  rcases eventWitness.referencePath_within_owned
      vertexEventOwned eventRightOwned with
    ⟨rightPath, rightStarts, rightFinishes, rightOwned⟩
  exact ⟨event, eventComponent, eventUsed, eventForestUsed, eventOwned,
    leftPath, rightPath, eventLookup, eventRawAge,
    eventComponentLookupAtRawAge, eventDerivation, eventLink, eventWitness,
    by simpa [eventRawAge] using eventAccounted, vertexEventOwned,
    eventLeftOwned, eventRightOwned, leftStarts, leftFinishes, leftOwned,
    rightStarts, rightFinishes, rightOwned⟩

end CanonicalTagHistory
end SequentialFigure7
end ProofNetIR
