/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7ActiveTopDebtParentEscapeTemporal

/-!
# Active-top debt parent temporal outcome

The par residual already exposes a raw sibling or a strictly older queued or
marked parent conclusion. This module consumes canonical continuation credit
for the tensor same-boundary residual and exposes the same endpoint-level
trichotomy. The result is still a residual: it does not produce a ready-tail
witness, establish the history tail law, or prove progress.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge

/-- Endpoint-level temporal normal form shared by par and tensor parent
escapes. A raw endpoint is the selected head or lies outside the active
carrier; every scheduled or marked parent endpoint is strictly older than the
active raw boundary. -/
inductive ActiveCarrierParentTemporalOutcome
    (certificate : Certificate) (state : ReservationState)
    (activeRawAge : RawTokenAge) (selected : Vertex) (owned : List Vertex) :
    Prop where
  | rawSibling
      (sibling : Vertex)
      (unmarked : state.core.marks[sibling]? = some none)
      (location : sibling = selected ∨ sibling ∉ owned) :
      ActiveCarrierParentTemporalOutcome certificate state activeRawAge selected owned
  | olderFuture
      (conclusion : Vertex) (boundary : RawTokenAge)
      (work : FutureWorkAt state boundary conclusion)
      (older : boundary < activeRawAge)
      (outside : conclusion ∉ owned) :
      ActiveCarrierParentTemporalOutcome certificate state activeRawAge selected owned
  | olderMarked
      (conclusion : Vertex) (conclusionAge : RawTokenAge)
      (marked : state.core.marks[conclusion]? = some (some conclusionAge))
      (olderRepresentative :
        state.core.representative conclusionAge < activeRawAge)
      (outside : conclusion ∉ owned) :
      ActiveCarrierParentTemporalOutcome certificate state activeRawAge selected owned

private theorem ActiveParParentContinuation.temporalOutcome
    {certificate : Certificate} {state : ReservationState}
    {activeRawAge : RawTokenAge} {selected : Vertex} {owned : List Vertex}
    {premise linkIndex conclusion : Vertex}
    (continuation :
      ActiveParParentContinuation certificate state activeRawAge selected owned
        premise linkIndex conclusion)
    (outside : conclusion ∉ owned) :
    ActiveCarrierParentTemporalOutcome certificate state activeRawAge selected owned := by
  cases continuation with
  | rawSibling consumer _sameIndex _sameConclusion unmarked location =>
      exact .rawSibling consumer.mate unmarked location
  | olderFuture boundary work older =>
      exact .olderFuture conclusion boundary work older outside
  | olderMarked conclusionAge marked older =>
      exact .olderMarked conclusion conclusionAge marked older outside

private theorem submittedTensorPremise_bound
    {certificate : Certificate} (structural : certificate.StructurallyWellFormed)
    {linkIndex left right conclusion premise : Vertex}
    (lookup :
      certificate.links[linkIndex]? = some (.tensor left right conclusion))
    (membership : premise ∈ (Link.tensor left right conclusion).premises) :
    premise < certificate.formulas.size := by
  have wellFormed := structural.2.2.2.2.1 _ (List.mem_of_getElem? lookup)
  simp [Link.premises] at membership
  rcases membership with rfl | rfl
  · exact wellFormed.2.2.2.1
  · exact wellFormed.2.2.2.2.1

private theorem connectiveBelow_matches_tensor_parent
    {certificate : Certificate} (structural : certificate.StructurallyWellFormed)
    {premise linkIndex left right conclusion sibling : Vertex}
    (consumer : ConnectiveBelow certificate premise)
    (lookup :
      certificate.links[linkIndex]? = some (.tensor left right conclusion))
    (membership : premise ∈ (Link.tensor left right conclusion).premises)
    (orientation :
      (premise = left ∧ sibling = right) ∨
        (premise = right ∧ sibling = left)) :
    consumer.linkIndex = linkIndex ∧
      consumer.conclusion = conclusion ∧ consumer.mate = sibling := by
  have premiseBound := submittedTensorPremise_bound structural lookup membership
  have escapeIndex :
      certificate.consumerIndex.uniqueConsumer? premise = some linkIndex := by
    simpa [Certificate.consumerIndex] using
      ConsumerIndex.build_uniqueConsumer?_eq_some structural lookup premiseBound
        membership
  have sameIndex : consumer.linkIndex = linkIndex :=
    Option.some.inj (consumer.consumer_eq.symm.trans escapeIndex)
  have consumerLookup := consumer.link_eq
  rw [sameIndex] at consumerLookup
  have sameLink :
      consumer.kind.asLink consumer.storedLeft consumer.storedRight
          consumer.conclusion =
        .tensor left right conclusion :=
    Option.some.inj (consumerLookup.symm.trans lookup)
  have premiseEquation := consumer.premise_eq
  rcases orientation with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    cases kindEquation : consumer.kind <;>
      cases sideEquation : consumer.side <;>
        simp_all [SequentialConnectiveKind.asLink, ConnectiveBelow.mate,
          TensorPremiseSide.mate, TensorPremiseSide.premise]

private theorem ReadyHeadInput.markedRepresentative_le_active
    {certificate : Certificate} {state : ReservationState}
    (input : ReadyHeadInput state)
    (invariant : SchedulerInvariant certificate state)
    {vertex : Vertex} {rawAge : RawTokenAge}
    (marked : state.core.marks[vertex]? = some (some rawAge)) :
    state.core.representative rawAge ≤ input.rawAge := by
  have stackMarked : state.stack.marks[vertex]? = some (some rawAge) := by
    rw [← invariant.realizesSigma.marks_eq]
    exact marked
  have rawAgeBound : rawAge < state.stack.nextAge :=
    invariant.stack_wellShaped.assigned_age_bound vertex rawAge stackMarked
  have realized := invariant.realizesSigma.representative_eq_boundary rawAgeBound
  by_cases rawLtActive : rawAge < input.rawAge
  · exact Nat.le_trans
      (UnificationState.OrderedParents.representative_le
        invariant.core_orderedParents rawAge)
      (Nat.le_of_lt rawLtActive)
  · have activeLeRaw : input.rawAge ≤ rawAge := Nat.le_of_not_gt rawLtActive
    have topLookup := invariant.stack_wellShaped.sigma_partition
      |>.sigmaBoundary?_eq_top_of_le input.sigma_top activeLeRaw rawAgeBound
    exact Nat.le_of_eq (Option.some.inj (realized.symm.trans topLookup))

private theorem markedOutsideActiveOwned_representative_lt
    {certificate : Certificate} {state : ReservationState}
    (input : ReadyHeadInput state)
    (invariant : SchedulerInvariant certificate state)
    {component : UnificationComponent} {usedLinks owned : List Nat}
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component usedLinks owned)
    {vertex : Vertex} {rawAge : RawTokenAge}
    (marked : state.core.marks[vertex]? = some (some rawAge))
    (notOwned : vertex ∉ owned) :
    state.core.representative rawAge < input.rawAge := by
  have representativeLe := input.markedRepresentative_le_active invariant marked
  have representativeNe : state.core.representative rawAge ≠ input.rawAge := by
    intro sameRepresentative
    rcases SchedulerInvariant.exactMarkedOccurrenceOwner invariant marked with
      ⟨ownerRawAge, ownerIndex, ownerComponent, ownerUsed, ownerOwned,
        ownerMarked, ownerRepresentative, ownerLookup, ownerOccurrence,
        _ownerAccounted, ownerMembership⟩
    have ownerRawAgeEq : ownerRawAge = rawAge := by
      exact Option.some.inj (Option.some.inj (ownerMarked.symm.trans marked))
    subst ownerRawAge
    have ownerIndexEq : ownerIndex = input.rawAge :=
      ownerRepresentative.symm.trans sameRepresentative
    have ownerLookupAtActive :
        state.core.components[input.rawAge]? = some (some ownerComponent) := by
      simpa [ownerIndexEq] using ownerLookup
    have componentEq : ownerComponent = component := by
      exact Option.some.inj
        (Option.some.inj (ownerLookupAtActive.symm.trans componentLookup))
    subst ownerComponent
    have ownedEq : ownerOwned = owned :=
      Certificate.OccurrenceDerivation.owned_unique invariant.structural
        ownerOccurrence.derivation occurrence.derivation
    exact notOwned (by simpa [ownedEq] using ownerMembership)
  exact Nat.lt_of_le_of_ne representativeLe representativeNe

private theorem FutureWorkAt.boundary_lt_active_of_not_owned
    {certificate : Certificate} {state : ReservationState}
    (input : ReadyHeadInput state)
    (invariant : SchedulerInvariant certificate state)
    {component : UnificationComponent} {usedLinks owned : List Nat}
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component usedLinks owned)
    {boundary : RawTokenAge} {vertex : Vertex}
    (work : FutureWorkAt state boundary vertex)
    (notOwned : vertex ∉ owned) :
    boundary < input.rawAge := by
  have boundaryNeActive : boundary ≠ input.rawAge := by
    intro sameBoundary
    subst boundary
    cases work with
    | ready sigmaAt readyAt member =>
        rcases invariant.ready_bucket_frontier_exact sigmaAt readyAt with
          ⟨readyComponent, readyLookup, exactMembership⟩
        have componentEq : readyComponent = component := by
          exact Option.some.inj
            (Option.some.inj (readyLookup.symm.trans componentLookup))
        subst readyComponent
        have vertexFrontier : vertex ∈ component.frontier :=
          ((exactMembership vertex).mp member).1
        exact notOwned
          (occurrence.derivation.frontier_subset_owned vertex vertexFrontier)
    | waiting waitingAt _member =>
        have activeUndefined :
            state.stack.waiting[input.rawAge]? = some .undefined :=
          invariant.stack_operationalWaitingDomain.active_undefined
            invariant.stack_wellShaped input.sigma_top
        rw [activeUndefined] at waitingAt
        simp at waitingAt
  have boundaryMembership : boundary ∈ state.stack.sigma :=
    work.rawAge_mem_sigma invariant
  rcases List.getLast?_eq_some_iff.mp input.sigma_top with
    ⟨sigmaPrefix, sigmaEq⟩
  have increasing := invariant.stack_wellShaped.sigma_partition.strictIncreasing
  rw [sigmaEq] at boundaryMembership increasing
  simp only [List.mem_append, List.mem_singleton] at boundaryMembership
  rcases boundaryMembership with inPrefix | same
  · exact (List.pairwise_append.mp increasing).2.2 boundary inPrefix
      input.rawAge (by simp)
  · exact False.elim (boundaryNeActive same)

/-- Canonical continuation credit turns a tensor same-boundary escape into the
same endpoint-level temporal trichotomy already available for par. -/
theorem CanonicalTagHistory.ActiveCarrierTensorSameBoundaryResidual.temporalOutcome
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {owned : List Vertex}
    (residual :
      tagHistory.ActiveCarrierTensorSameBoundaryResidual input component owned)
    (invariant : SchedulerInvariant certificate state)
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component)) :
    ActiveCarrierParentTemporalOutcome certificate state input.rawAge input.vertex owned := by
  rcases residual with
    ⟨premise, markedAge, linkIndex, storedLeft, storedRight, conclusion,
      sibling, _event, _eventUsed, forestUsed, _leftPath, _rightPath,
      _premiseNeSelected, _premiseFrontier, premiseMarked, _authentic,
      premiseNotGlobal, linkLookup, premiseMembership, conclusionNotOwned,
      _premiseOwned, _representativeEq, _boundaryEq, orientation,
      siblingNotOwned, _eventLookup, _eventRawAge, _eventDerivation,
      _eventLinkUsed, occurrence, _accounted, _eventLeftOwned,
      _eventRightOwned, _leftStarts, _leftFinishes, _leftWithin,
      _rightStarts, _rightFinishes, _rightWithin⟩
  have credit : ContinuationCredit certificate state premise :=
    tagHistory.markedNonconclusionContinuation premiseMarked premiseNotGlobal
  cases credit with
  | rawMate consumer mateUnmarked =>
      have same := connectiveBelow_matches_tensor_parent invariant.structural
        consumer linkLookup premiseMembership orientation
      have siblingUnmarked : state.core.marks[sibling]? = some none := by
        rw [← same.2.2]
        exact mateUnmarked
      exact .rawSibling sibling siblingUnmarked (Or.inr siblingNotOwned)
  | futureConclusion consumer boundary work =>
      have same := connectiveBelow_matches_tensor_parent invariant.structural
        consumer linkLookup premiseMembership orientation
      have workAtConclusion : FutureWorkAt state boundary conclusion := by
        rw [← same.2.1]
        exact work
      have older : boundary < input.rawAge :=
        workAtConclusion.boundary_lt_active_of_not_owned input invariant
          componentLookup occurrence conclusionNotOwned
      exact .olderFuture conclusion boundary workAtConclusion older
        conclusionNotOwned
  | markedConclusion consumer conclusionAge marked =>
      have same := connectiveBelow_matches_tensor_parent invariant.structural
        consumer linkLookup premiseMembership orientation
      have markedConclusion :
          state.core.marks[conclusion]? = some (some conclusionAge) := by
        rw [← same.2.1]
        exact marked
      have older : state.core.representative conclusionAge < input.rawAge :=
        markedOutsideActiveOwned_representative_lt input invariant
          componentLookup occurrence markedConclusion conclusionNotOwned
      exact .olderMarked conclusion conclusionAge markedConclusion older
        conclusionNotOwned

/-- Both source branches of a normalized parent escape expose one common
temporal endpoint. This remains a reduction, not an endpoint-locality or
ready-tail theorem. -/
theorem ActiveCarrierParentTemporalResidual.temporalOutcome
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {owned : List Vertex}
    (residual : ActiveCarrierParentTemporalResidual tagHistory input component owned)
    (invariant : SchedulerInvariant certificate state)
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component)) :
    ActiveCarrierParentTemporalOutcome certificate state input.rawAge input.vertex owned := by
  cases residual with
  | par parResidual =>
      rcases parResidual with
        ⟨_premise, _markedAge, _linkIndex, _storedLeft, _storedRight,
          _conclusion, _premiseNeSelected, _premiseFrontier, _premiseOwned,
          _premiseMarked, _authentic, _representativeEq, _premiseNotGlobal,
          _linkLookup, _premiseMembership, conclusionNotOwned,
          _reservationAnchor, continuation⟩
      exact continuation.temporalOutcome conclusionNotOwned
  | tensor tensorResidual _olderMarkedTensor =>
      exact tensorResidual.temporalOutcome invariant componentLookup

end SequentialFigure7
end ProofNetIR
