/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7CommitmentIntervalParConclusionDichotomy
import ProofNetIR.SequentialComponentSourceLeftGeometry

/-!
# Figure-7 commitment-interval par-trace localization

Sharpens the failed-edge branch of the positive commitment-interval
par-conclusion dichotomy relative to the active occurrence carrier. A failed
edge at the active boundary retains the exact selected/mate trace split. A
strictly older failed edge cannot trace into the selected head, and it cannot
trace into an active-owned mate; exact live-carrier disjointness would put the
event's axiom endpoint in two different component carriers. The only older
trace obstruction is therefore stored-right and ends at a mate outside the
active owned carrier.

The outer alternatives remain inclusive. This module does not eliminate the
equal-boundary trace, localize the external mate further, derive a payer or
tail law, or prove progress.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerBridge
open SequentialSchedulerState
open SequentialUnification

namespace CanonicalTagHistory

private theorem representative_eq_of_sigmaAt
    {certificate : Certificate} {state : ReservationState}
    (invariant : SchedulerInvariant certificate state)
    {position : Nat} {rawAge : RawTokenAge}
    (sigmaAt : state.stack.sigma[position]? = some rawAge) :
    state.core.representative rawAge = rawAge := by
  have rawAgeMembership : rawAge ∈ state.stack.sigma :=
    List.mem_of_getElem? sigmaAt
  have rawAgeBound : rawAge < state.stack.nextAge :=
    invariant.stack_wellShaped.sigma_partition.boundary_lt rawAge
      rawAgeMembership
  rcases invariant.stack_wellShaped.sigma_partition.boundary_exists rawAgeBound
      with ⟨boundary, boundaryLookup⟩
  have boundaryLeRawAge : boundary ≤ rawAge :=
    sigmaBoundary?_le boundaryLookup
  have rawAgeLeBoundary : rawAge ≤ boundary :=
    sigmaBoundary?_greatest
      invariant.stack_wellShaped.sigma_partition.strictIncreasing
      boundaryLookup rawAge rawAgeMembership (Nat.le_refl _)
  have boundaryEq : boundary = rawAge :=
    Nat.le_antisymm boundaryLeRawAge rawAgeLeBoundary
  subst boundary
  have representativeLookup :=
    invariant.realizesSigma.representative_eq_boundary rawAgeBound
  exact Option.some.inj (representativeLookup.symm.trans boundaryLookup)

private theorem selected_frontier_of_component
    {certificate : Certificate} {state : ReservationState}
    (input : ReadyHeadInput state)
    (invariant : SchedulerInvariant certificate state)
    {component : UnificationComponent}
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component)) :
    input.vertex ∈ component.frontier := by
  rcases List.getLast?_eq_some_iff.mp input.top_ready with
    ⟨readyPrefix, readyDecomposition⟩
  rcases List.getLast?_eq_some_iff.mp input.sigma_top with
    ⟨sigmaPrefix, sigmaDecomposition⟩
  have prefixLengths : readyPrefix.length = sigmaPrefix.length := by
    have aligned := invariant.stack_wellShaped.ready_aligned
    rw [readyDecomposition, sigmaDecomposition] at aligned
    simp at aligned
    omega
  have sigmaLookup :
      state.stack.sigma[readyPrefix.length]? = some input.rawAge := by
    rw [sigmaDecomposition, prefixLengths]
    simp
  have readyLookup :
      state.stack.ready[readyPrefix.length]? =
        some (input.vertex :: input.readyTail) := by
    rw [readyDecomposition]
    simp
  rcases invariant.ready_bucket_frontier_exact sigmaLookup readyLookup with
    ⟨actual, actualLookup, exactMembership⟩
  have actualEq : actual = component :=
    Option.some.inj
      (Option.some.inj (actualLookup.symm.trans componentLookup))
  subst actual
  exact ((exactMembership input.vertex).mp (by simp)).1

private theorem trace_vertex_touched
    {certificate : Certificate} (event : ReservationEvent certificate)
    {beforeTrace afterTrace : List Vertex} {first second : Vertex}
    (trace : event.search.result.trace =
      beforeTrace ++ first :: second :: afterTrace) :
    event.Touched second := by
  left
  rw [trace]
  simp

private theorem older_event_trace_not_activeOwned
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (invariant : SchedulerInvariant certificate state)
    (input : ReadyHeadInput state)
    {component : UnificationComponent} {usedLinks owned : List Nat}
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component
        usedLinks owned)
    {event : ReservationEvent certificate} {child : RawTokenAge}
    (membership : event ∈ tagHistory.reservationLedger)
    (eventAge : event.rawAge = child)
    {position : Nat}
    (childAt : state.stack.sigma[position]? = some child)
    (childOlder : child < input.rawAge)
    {vertex : Vertex}
    (vertexOwned : vertex ∈ owned)
    (touched : event.Touched vertex) : False := by
  rcases tagHistory.reservationLedger_axiomEndpoints_accounted
      invariant.structural membership with
    ⟨eventComponent, eventUsed, eventForestUsed, eventOwned, eventLookup,
      eventDerivation, eventLink, eventWitness, eventAccounted,
      eventLeftOwned, eventRightOwned⟩
  rcases invariant.component_forest_provenance with
    ⟨usedAt, ownedAt, live, separated, markedOwned⟩
  have childRoot : state.core.representative child = child :=
    representative_eq_of_sigmaAt invariant childAt
  have eventLookupAtChild :
      state.core.components[child]? = some (some eventComponent) := by
    simpa [eventAge, childRoot] using eventLookup
  have eventFacts := live eventLookupAtChild
  have eventOwnedEq : eventOwned = ownedAt child :=
    Certificate.OccurrenceDerivation.owned_unique invariant.structural
      eventDerivation eventFacts.1.derivation
  have eventLeftForestOwned : event.search.result.left ∈ ownedAt child := by
    rw [← eventOwnedEq]
    exact eventLeftOwned
  have activeFacts := live componentLookup
  have activeOwnedEq : owned = ownedAt input.rawAge :=
    Certificate.OccurrenceDerivation.owned_unique invariant.structural
      occurrence.derivation activeFacts.1.derivation
  have eventLeftRegion :
      SourceLeftRegionVertex certificate vertex event.search.result.left :=
    event.leftEndpoint_sourceLeftRegion_of_touched touched
  have eventLeftActiveOwned :
      event.search.result.left ∈ ownedAt input.rawAge := by
    rw [← activeOwnedEq]
    exact occurrence.derivation.sourceLeftRegion_owned invariant.structural
      vertexOwned eventLeftRegion
  have differentSlots : child ≠ input.rawAge := Nat.ne_of_lt childOlder
  have disjoint :=
    (separated eventLookupAtChild componentLookup differentSlots).2
  exact disjoint event.search.result.left eventLeftForestOwned
    eventLeftActiveOwned

/-- A complete positive retained interval ending at the active ready boundary
either has a par-conclusion-avoiding endpoint path, has an exact failed edge at
the active boundary with either trace orientation, or has a strictly older
failed edge whose stored-right trace reaches a mate outside the active owned
carrier.

The alternatives remain inclusive. The theorem does not eliminate the active
trace or the external older mate. -/
theorem commitmentInterval_parConclusion_localizedDichotomy
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (invariant : SchedulerInvariant certificate state)
    (input : ReadyHeadInput state)
    (consumer : ConnectiveBelow certificate input.vertex)
    (parEq : consumer.kind = .par)
    {component : UnificationComponent} {usedLinks owned : List Nat}
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component
        usedLinks owned)
    {position edgeCount : Nat} {first : RawTokenAge}
    (positive : 0 < edgeCount)
    (firstAt : state.stack.sigma[position]? = some first)
    (lastAt :
      state.stack.sigma[position + edgeCount]? = some input.rawAge) :
    tagHistory.CommitmentEdgeTargetAvoidingPath first input.rawAge
        consumer.conclusion ∨
      ∃ offset parent child event,
        offset < edgeCount ∧
          state.stack.sigma[position + offset]? = some parent ∧
          state.stack.sigma[position + offset + 1]? = some child ∧
          ¬ tagHistory.CommitmentEdgeTargetAvoidingPath parent child
            consumer.conclusion ∧
          event ∈ tagHistory.reservationLedger ∧
          event.rawAge = child ∧
          ((child = input.rawAge ∧
              ((consumer.side = .storedLeft ∧
                  ∃ beforeTrace afterTrace,
                    event.search.result.trace =
                      beforeTrace ++ consumer.conclusion :: input.vertex ::
                        afterTrace) ∨
                (consumer.side = .storedRight ∧
                  ∃ beforeTrace afterTrace,
                    event.search.result.trace =
                      beforeTrace ++ consumer.conclusion :: consumer.mate ::
                        afterTrace))) ∨
            (child < input.rawAge ∧
              consumer.side = .storedRight ∧
              consumer.mate ∉ owned ∧
              ∃ beforeTrace afterTrace,
                event.search.result.trace =
                  beforeTrace ++ consumer.conclusion :: consumer.mate ::
                    afterTrace)) := by
  rcases tagHistory.commitmentInterval_parConclusion_dichotomy invariant input
      consumer parEq positive firstAt lastAt with avoiding | obstruction
  · exact Or.inl avoiding
  · rcases obstruction with
      ⟨offset, parent, child, event, offsetLt, parentAt, childAt, childOrder,
        notAvoiding, membership, eventAge, selectedTrace | mateTrace⟩
    have selectedFrontier :=
      selected_frontier_of_component input invariant componentLookup
    have selectedOwned :=
      occurrence.derivation.frontier_subset_owned input.vertex
        selectedFrontier
    rcases childOrder with childOlder | childEq
    · rcases selectedTrace with
        ⟨side, beforeTrace, afterTrace, trace⟩
      exact False.elim
        (older_event_trace_not_activeOwned tagHistory invariant input
          componentLookup occurrence membership eventAge childAt childOlder
          selectedOwned (trace_vertex_touched event trace))
    · exact Or.inr ⟨offset, parent, child, event, offsetLt, parentAt, childAt,
        notAvoiding, membership, eventAge, Or.inl ⟨childEq, Or.inl selectedTrace⟩⟩
    · rcases mateTrace with ⟨side, beforeTrace, afterTrace, trace⟩
      by_cases childEq : child = input.rawAge
      · exact Or.inr ⟨offset, parent, child, event, offsetLt, parentAt, childAt,
          notAvoiding, membership, eventAge, Or.inl ⟨childEq, Or.inr
            ⟨side, beforeTrace, afterTrace, trace⟩⟩⟩
      · have childOlder : child < input.rawAge :=
          childOrder.resolve_right childEq
        have mateOutside : consumer.mate ∉ owned := by
          intro mateOwned
          exact older_event_trace_not_activeOwned tagHistory invariant input
            componentLookup occurrence membership eventAge childAt childOlder
            mateOwned (trace_vertex_touched event trace)
        exact Or.inr ⟨offset, parent, child, event, offsetLt, parentAt, childAt,
          notAvoiding, membership, eventAge, Or.inr ⟨childOlder, side,
            mateOutside, beforeTrace, afterTrace, trace⟩⟩

end CanonicalTagHistory
end SequentialFigure7
end ProofNetIR
