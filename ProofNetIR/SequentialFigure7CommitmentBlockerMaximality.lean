/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7CommitmentBlockerAdvance

/-!
# Figure-7 commitment blocker maximality

Eliminates the strict current-representative advance branch from the preceding
commitment-blocker trichotomy by choosing a finite maximum among authentic
mate-touching ledger blockers. A further advance contradicts maximality, while
a commitment path at the maximum contradicts reference-switching acyclicity.

The public result is an inclusive two-way reduction: a commitment-edge path
that avoids the active tensor conclusion, or an equal-boundary stored-left
callback-failure trace. The callback-failure branch does not assert that an
avoiding path is absent.

This module adds no raw-mark seam, NewEnabled, progress, totality, worklist
completeness, fallback removal, token-age scheduling, or whole-program
linearity result.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerBridge
open SequentialUnification

namespace CanonicalTagHistory

private theorem event_rawAge_lt_nextAge
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    {event : ReservationEvent certificate}
    (membership : event ∈ tagHistory.reservationLedger) :
    event.rawAge < state.stack.nextAge := by
  have mapped :
      event.rawAge ∈
        tagHistory.reservationLedger.map ReservationEvent.rawAge :=
    List.mem_map.mpr ⟨event, membership, rfl⟩
  rw [tagHistory.reservationLedger_rawAges] at mapped
  simpa using mapped

private theorem event_rawAge_eq_of_lookup
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    {rawAge : RawTokenAge} {event : ReservationEvent certificate}
    (lookup : tagHistory.reservationLedger[rawAge]? = some event) :
    event.rawAge = rawAge := by
  have bound : rawAge < state.stack.nextAge := by
    rw [← tagHistory.reservationLedger_length]
    exact (List.getElem?_eq_some_iff.mp lookup).1
  have exactRawAge :=
    tagHistory.reservationLedger_getElem?_rawAge rawAge bound
  simpa [lookup] using exactRawAge

private theorem mateTouch_forbids_representativeCommitmentPath
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate state)
    (guard : NewGuard certificate state)
    {event : ReservationEvent certificate}
    (membership : event ∈ tagHistory.reservationLedger)
    (mateTouched : event.Touched guard.tensor.mate)
    (commitment : tagHistory.CommitmentEdgeTargetAvoidingPath
      (state.core.representative event.rawAge) guard.head.rawAge
        guard.tensor.conclusion) :
    False := by
  rcases commitment with
    ⟨parentEvent, childEvent, commitmentPath, parentLookup, childLookup,
      commitmentStarts, commitmentFinishes, commitmentAvoids⟩
  have parentMembership : parentEvent ∈ tagHistory.reservationLedger :=
    List.mem_of_getElem? parentLookup
  have childMembership : childEvent ∈ tagHistory.reservationLedger :=
    List.mem_of_getElem? childLookup
  have parentRawAge :
      parentEvent.rawAge = state.core.representative event.rawAge :=
    tagHistory.event_rawAge_eq_of_lookup parentLookup
  have childRawAge : childEvent.rawAge = guard.head.rawAge :=
    tagHistory.event_rawAge_eq_of_lookup childLookup
  have eventRawAgeBound : event.rawAge < state.core.parents.size := by
    rw [invariant.realizesSigma.horizon_eq]
    exact tagHistory.event_rawAge_lt_nextAge membership
  have representativeRoot :
      state.core.representative (state.core.representative event.rawAge) =
        state.core.representative event.rawAge :=
    UnificationState.OrderedParents.representative_idempotent
      invariant.core_orderedParents eventRawAgeBound
  have parentRepresentative :
      state.core.representative parentEvent.rawAge =
        state.core.representative event.rawAge := by
    rw [parentRawAge, representativeRoot]
  have childRepresentative :
      state.core.representative childEvent.rawAge = guard.head.rawAge := by
    rw [childRawAge]
    exact (guard.head.futureWorkAt invariant).representative_eq_rawAge invariant
  rcases tagHistory.reservationLedger_axiomEndpoints_accounted correct.1 membership with
    ⟨eventComponent, _eventUsed, _eventForest, eventOwned,
      eventComponentLookup, eventDerivation, _eventLink, eventWitness,
      eventAccounted, eventLeftOwned, _eventRightOwned⟩
  rcases tagHistory.reservationLedger_axiomEndpoints_accounted correct.1
      parentMembership with
    ⟨parentComponent, _parentUsed, _parentForest, parentOwned,
      parentComponentLookup, parentDerivation, _parentLink, _parentWitness,
      _parentAccounted, parentLeftOwned, _parentRightOwned⟩
  have parentComponentLookupAtEvent :
      state.core.components[state.core.representative event.rawAge]? =
        some (some parentComponent) := by
    simpa [parentRepresentative] using parentComponentLookup
  have blockerComponentEq : parentComponent = eventComponent := by
    exact Option.some.inj
      (Option.some.inj
        (parentComponentLookupAtEvent.symm.trans eventComponentLookup))
  subst parentComponent
  have blockerOwnedEq : parentOwned = eventOwned :=
    Certificate.OccurrenceDerivation.owned_unique correct.1
      parentDerivation eventDerivation
  have parentLeftEventOwned : parentEvent.search.result.left ∈ eventOwned := by
    rw [← blockerOwnedEq]
    exact parentLeftOwned
  rcases eventWitness.referencePath_within_owned eventLeftOwned
      parentLeftEventOwned with
    ⟨blockerComponentPath, blockerComponentStarts,
      blockerComponentFinishes, blockerComponentWithin⟩
  have conclusionNotEventOwned : guard.tensor.conclusion ∉ eventOwned :=
    guard.tensorConclusion_not_owned invariant eventComponentLookup
      eventAccounted
  have blockerComponentAvoids :
      guard.tensor.conclusion ∉ blockerComponentPath.vertices := by
    intro inPath
    exact conclusionNotEventOwned
      (blockerComponentWithin guard.tensor.conclusion inPath)
  rcases guard.head.activeComponent invariant with
    ⟨activeComponent, _activeUsed, activeOwned, activeLookup,
      activeWitness, activeAccounted, headOwned, activeRoot⟩
  rcases tagHistory.reservationLedger_axiomEndpoints_accounted correct.1
      childMembership with
    ⟨childComponent, _childUsed, _childForest, childOwned,
      childComponentLookup, childDerivation, _childLink, _childWitness,
      _childAccounted, childLeftOwned, _childRightOwned⟩
  have childComponentLookupAtActive :
      state.core.components[guard.head.rawAge]? =
        some (some childComponent) := by
    simpa [childRepresentative] using childComponentLookup
  have childComponentEq : childComponent = activeComponent := by
    exact Option.some.inj
      (Option.some.inj (childComponentLookupAtActive.symm.trans activeLookup))
  subst childComponent
  have childOwnedEq : childOwned = activeOwned :=
    Certificate.OccurrenceDerivation.owned_unique correct.1
      childDerivation activeWitness.derivation
  have childLeftActiveOwned : childEvent.search.result.left ∈ activeOwned := by
    rw [← childOwnedEq]
    exact childLeftOwned
  rcases activeWitness.referencePath_within_owned childLeftActiveOwned
      headOwned with
    ⟨activePath, activeStarts, activeFinishes, activeWithin⟩
  have conclusionNotActiveOwned : guard.tensor.conclusion ∉ activeOwned :=
    guard.tensorConclusion_not_owned invariant activeLookup activeAccounted
  have activeAvoids : guard.tensor.conclusion ∉ activePath.vertices := by
    intro inPath
    exact conclusionNotActiveOwned
      (activeWithin guard.tensor.conclusion inPath)
  have historicalRegion :
      SourceLeftRegionVertex certificate guard.tensor.mate
        event.search.result.left :=
    event.leftEndpoint_sourceLeftRegion_of_touched mateTouched
  have mateBelowConclusion :
      certificate.formulaComplexityAt guard.tensor.mate <
        certificate.formulaComplexityAt guard.tensor.conclusion :=
    guard.sourceLeftRegion_formulaComplexity_lt_conclusion correct.1
      (.visited (.refl _))
  have eventLeftBelowConclusion :
      certificate.formulaComplexityAt event.search.result.left <
        certificate.formulaComplexityAt guard.tensor.conclusion :=
    guard.sourceLeftRegion_formulaComplexity_lt_conclusion correct.1
      historicalRegion
  have eventLeftNeConclusion :
      event.search.result.left ≠ guard.tensor.conclusion := by
    intro same
    rw [same] at eventLeftBelowConclusion
    omega
  rcases sourceLeftRegionVertex_referencePath_avoiding correct.1
      historicalRegion mateBelowConclusion eventLeftNeConclusion with
    ⟨historicalPath, historicalStarts, historicalFinishes,
      historicalAvoids⟩
  rcases historicalPath.connectEraseAvoiding blockerComponentPath
      (historicalFinishes.trans blockerComponentStarts.symm)
      historicalAvoids blockerComponentAvoids with
    ⟨prefixPath, prefixStarts, prefixFinishes, prefixAvoids⟩
  rcases prefixPath.connectEraseAvoiding commitmentPath
      (prefixFinishes.trans
        (blockerComponentFinishes.trans commitmentStarts.symm))
      prefixAvoids commitmentAvoids with
    ⟨middlePath, middleStarts, middleFinishes, middleAvoids⟩
  rcases middlePath.connectEraseAvoiding activePath
      (middleFinishes.trans (commitmentFinishes.trans activeStarts.symm))
      middleAvoids activeAvoids with
    ⟨bypass, bypassStarts, bypassFinishes, bypassAvoids⟩
  have tensorMembership :
      Link.tensor guard.tensor.storedLeft guard.tensor.storedRight
          guard.tensor.conclusion ∈ certificate.links :=
    List.mem_of_getElem? guard.tensor_valid.2.1
  have combinedStarts : bypass.start = guard.tensor.mate :=
    bypassStarts.trans (middleStarts.trans (prefixStarts.trans historicalStarts))
  have combinedFinishes : bypass.finish = guard.head.vertex :=
    bypassFinishes.trans activeFinishes
  have headEquation := guard.tensor_valid.2.2.2
  cases sideEquation : guard.tensor.side with
  | storedLeft =>
      have headIsLeft : guard.head.vertex = guard.tensor.storedLeft := by
        simpa [TensorBelow.premise, TensorPremiseSide.premise,
          sideEquation] using headEquation
      have mateIsRight : guard.tensor.mate = guard.tensor.storedRight := by
        simp [TensorBelow.mate, TensorPremiseSide.mate, sideEquation]
      apply referenceAcyclic_no_tensorBypass correct.1
        correct.referenceSwitchingTree.acyclic tensorMembership bypass.reverse
      · exact combinedFinishes.trans headIsLeft
      · exact combinedStarts.trans mateIsRight
      · simpa using bypassAvoids
  | storedRight =>
      have headIsRight : guard.head.vertex = guard.tensor.storedRight := by
        simpa [TensorBelow.premise, TensorPremiseSide.premise,
          sideEquation] using headEquation
      have mateIsLeft : guard.tensor.mate = guard.tensor.storedLeft := by
        simp [TensorBelow.mate, TensorPremiseSide.mate, sideEquation]
      apply referenceAcyclic_no_tensorBypass correct.1
        correct.referenceSwitchingTree.acyclic tensorMembership bypass
      · exact combinedStarts.trans mateIsLeft
      · exact combinedFinishes.trans headIsRight
      · exact bypassAvoids

/-- Given a canonical tag history, declarative correctness, the complete
scheduler invariant, a `NewGuard`, authentic ledger membership for one event,
and strict order from that event's current representative to the active head
representative, finite maximality removes the current-representative advance
alternative. The result is an inclusive disjunction between a
conclusion-avoiding commitment path and an equal-boundary stored-left
callback-failure trace. Callback failure does not deny the existence of an
avoiding path. This theorem does not derive queue origin or the remaining
mate-region/global raw-mark invariants, close a created-candidate raw seam, or
prove `NewEnabled`, progress, totality, worklist completeness, fallback
removal, token-age scheduling, or whole-program linearity. -/
theorem strictOlder_commitmentPath_or_equalCallbackFailure
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate state)
    (guard : NewGuard certificate state)
    {event : ReservationEvent certificate}
    (membership : event ∈ tagHistory.reservationLedger)
    (older :
      state.core.representative event.rawAge <
        state.core.representative guard.head.rawAge) :
    tagHistory.CommitmentEdgeTargetAvoidingPath
        (state.core.representative event.rawAge) guard.head.rawAge
        guard.tensor.conclusion ∨
      ∃ childEvent : ReservationEvent certificate,
        ∃ beforeTrace afterTrace,
          childEvent ∈ tagHistory.reservationLedger ∧
            childEvent.rawAge = guard.head.rawAge ∧
            guard.tensor.side = .storedLeft ∧
            childEvent.search.result.trace =
              beforeTrace ++ guard.tensor.conclusion ::
                guard.head.vertex :: afterTrace := by
  classical
  rcases
      tagHistory.strictOlder_commitmentPath_or_advance_or_equalCallbackFailure
        correct invariant guard membership older with
    path | advanceOrCallback
  · exact Or.inl path
  rcases advanceOrCallback with advance | callbackFailure
  · rcases advance with
      ⟨higherEvent, higherMembership, firstBeforeHigher, higherOlder,
        higherTouched⟩
    let blockers := tagHistory.reservationLedger.filter fun candidate ↦
      state.core.representative event.rawAge <
          state.core.representative candidate.rawAge ∧
        state.core.representative candidate.rawAge <
          state.core.representative guard.head.rawAge ∧
        candidate.Touched guard.tensor.mate
    let blockerRepresentatives := blockers.map fun candidate ↦
      state.core.representative candidate.rawAge
    have higherInBlockers : higherEvent ∈ blockers := by
      simp [blockers, higherMembership, firstBeforeHigher, higherOlder,
        higherTouched]
    have higherRepresentativeIn :
        state.core.representative higherEvent.rawAge ∈
          blockerRepresentatives :=
      List.mem_map.mpr ⟨higherEvent, higherInBlockers, rfl⟩
    cases maxEquation : blockerRepresentatives.max? with
    | none =>
        have empty : blockerRepresentatives = [] :=
          List.max?_eq_none_iff.mp maxEquation
        rw [empty] at higherRepresentativeIn
        contradiction
    | some maxRepresentative =>
        have maxFacts := List.max?_eq_some_iff.mp maxEquation
        rcases List.mem_map.mp maxFacts.1 with
          ⟨maxEvent, maxInBlockers, maxRepresentativeEquation⟩
        subst maxRepresentative
        have maxData :
            maxEvent ∈ tagHistory.reservationLedger ∧
              state.core.representative event.rawAge <
                state.core.representative maxEvent.rawAge ∧
              state.core.representative maxEvent.rawAge <
                state.core.representative guard.head.rawAge ∧
              maxEvent.Touched guard.tensor.mate := by
          simpa [blockers] using maxInBlockers
        rcases maxData with
          ⟨maxMembership, firstBeforeMax, maxOlder, maxTouched⟩
        rcases
            tagHistory.strictOlder_commitmentPath_or_advance_or_equalCallbackFailure
              correct invariant guard maxMembership maxOlder with
          maxPath | maxAdvanceOrCallback
        · exact (tagHistory.mateTouch_forbids_representativeCommitmentPath
            correct invariant guard maxMembership maxTouched maxPath).elim
        rcases maxAdvanceOrCallback with maxAdvance | callbackFailure
        · rcases maxAdvance with
            ⟨higherAgain, higherAgainMembership, maxBeforeHigherAgain,
              higherAgainOlder, higherAgainTouched⟩
          have higherAgainInBlockers : higherAgain ∈ blockers := by
            simp [blockers, higherAgainMembership,
              Nat.lt_trans firstBeforeMax maxBeforeHigherAgain,
              higherAgainOlder, higherAgainTouched]
          have higherAgainRepresentativeIn :
              state.core.representative higherAgain.rawAge ∈
                blockerRepresentatives :=
            List.mem_map.mpr
              ⟨higherAgain, higherAgainInBlockers, rfl⟩
          have maximal := maxFacts.2 _ higherAgainRepresentativeIn
          omega
        · exact Or.inr callbackFailure
  · exact Or.inr callbackFailure

end CanonicalTagHistory
end SequentialFigure7
end ProofNetIR
