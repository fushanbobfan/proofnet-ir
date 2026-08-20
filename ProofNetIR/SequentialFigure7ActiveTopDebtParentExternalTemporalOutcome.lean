/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7ActiveTopDebtParentTemporalOutcome

/-!
# Active-top debt external parent temporal outcome

For an actual Nop or Wait whose non-global ready-tail obligation fails, the
raw endpoint of the normalized parent escape cannot be the selected head.
Nop excludes that case with its unmarked-mate guard; Wait excludes it with
the strict raw-age order of its concretely marked mate. Tensor-source raw
siblings were already outside the active occurrence carrier.

The resulting carrier has only an external raw endpoint, external queued work
at a strictly older boundary, or an external marked conclusion with a strictly
older representative. This remains a failure reduction. It does not return a
ready-tail witness, prove re-entry, derive the history-tail law, or establish
progress.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge

/-- A parent temporal outcome whose raw endpoint is known to lie outside the
active occurrence carrier. -/
inductive ActiveCarrierParentExternalTemporalOutcome
    (certificate : Certificate) (state : ReservationState)
    (activeRawAge : RawTokenAge) (owned : List Vertex) : Prop where
  | rawOutside
      (sibling : Vertex)
      (unmarked : state.core.marks[sibling]? = some none)
      (outside : sibling ∉ owned) :
      ActiveCarrierParentExternalTemporalOutcome certificate state
        activeRawAge owned
  | olderFuture
      (conclusion : Vertex) (boundary : RawTokenAge)
      (work : FutureWorkAt state boundary conclusion)
      (older : boundary < activeRawAge)
      (outside : conclusion ∉ owned) :
      ActiveCarrierParentExternalTemporalOutcome certificate state
        activeRawAge owned
  | olderMarked
      (conclusion : Vertex) (conclusionAge : RawTokenAge)
      (marked : state.core.marks[conclusion]? = some (some conclusionAge))
      (olderRepresentative :
        state.core.representative conclusionAge < activeRawAge)
      (outside : conclusion ∉ owned) :
      ActiveCarrierParentExternalTemporalOutcome certificate state
        activeRawAge owned

/-- Forget the strengthened external-raw conclusion while retaining the
endpoint-level temporal trichotomy. -/
theorem ActiveCarrierParentExternalTemporalOutcome.temporalOutcome
    {certificate : Certificate} {state : ReservationState}
    {activeRawAge : RawTokenAge} {owned : List Vertex}
    (outcome : ActiveCarrierParentExternalTemporalOutcome certificate state
      activeRawAge owned)
    (selected : Vertex) :
    ActiveCarrierParentTemporalOutcome certificate state activeRawAge
      selected owned := by
  cases outcome with
  | rawOutside sibling unmarked outside =>
      exact .rawSibling sibling unmarked (Or.inr outside)
  | olderFuture conclusion boundary work older outside =>
      exact .olderFuture conclusion boundary work older outside
  | olderMarked conclusion conclusionAge marked older outside =>
      exact .olderMarked conclusion conclusionAge marked older outside

private theorem connectiveMateMembership
    {certificate : Certificate} {vertex : Vertex}
    (consumer : ConnectiveBelow certificate vertex) :
    consumer.mate ∈ consumer.submittedLink.premises := by
  cases kindEq : consumer.kind <;> cases sideEq : consumer.side <;>
    simp [ConnectiveBelow.mate, ConnectiveBelow.submittedLink,
      SequentialConnectiveKind.asLink, Link.premises,
      TensorPremiseSide.mate, kindEq, sideEq]

private theorem connectiveBelow_mate_eq_of_mate_eq
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {leftVertex rightVertex : Vertex}
    (left : ConnectiveBelow certificate leftVertex)
    (right : ConnectiveBelow certificate rightVertex)
    (leftMate : left.mate = rightVertex) :
    right.mate = leftVertex := by
  have mateIndex :
      certificate.consumerIndex.uniqueConsumer? left.mate =
        some left.linkIndex := by
    simpa [Certificate.consumerIndex] using
      ConsumerIndex.build_uniqueConsumer?_eq_some structural left.link_eq
        left.mate_bound (connectiveMateMembership left)
  have rightIndex :
      certificate.consumerIndex.uniqueConsumer? rightVertex =
        some left.linkIndex := by
    simpa [leftMate] using mateIndex
  have sameIndex : right.linkIndex = left.linkIndex :=
    Option.some.inj (right.consumer_eq.symm.trans rightIndex)
  have rightLookup := right.link_eq
  rw [sameIndex] at rightLookup
  have sameLink :
      right.kind.asLink right.storedLeft right.storedRight right.conclusion =
        left.kind.asLink left.storedLeft left.storedRight left.conclusion :=
    Option.some.inj (rightLookup.symm.trans left.link_eq)
  have leftPremise := left.premise_eq
  have rightPremise := right.premise_eq
  cases leftKind : left.kind <;> cases rightKind : right.kind <;>
    cases leftSide : left.side <;> cases rightSide : right.side <;>
      simp_all [SequentialConnectiveKind.asLink, ConnectiveBelow.mate,
        TensorPremiseSide.mate, TensorPremiseSide.premise]

/-- Once the currently selected consumer cannot have a concretely marked mate
at the active representative, the par-source raw endpoint cannot be the
selected head. -/
private theorem ActiveParCarrierTemporalResidual.externalTemporalOutcome
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {owned : List Vertex}
    (residual : ActiveParCarrierTemporalResidual tagHistory input component owned)
    (structural : certificate.StructurallyWellFormed)
    (current : ConnectiveBelow certificate input.vertex)
    (mateNotActive :
      ∀ {rawAge : RawTokenAge},
        state.core.marks[current.mate]? = some (some rawAge) →
          state.core.representative rawAge ≠ input.rawAge) :
    ActiveCarrierParentExternalTemporalOutcome certificate state
      input.rawAge owned := by
  rcases residual with
    ⟨premise, markedAge, linkIndex, storedLeft, storedRight, conclusion,
      _premiseNeSelected, _premiseFrontier, _premiseOwned, premiseMarked,
      _authentic, premiseRepresentative, _premiseNotGlobal, _parLookup,
      _premiseMembership, conclusionNotOwned, _reservationAnchor,
      continuation⟩
  cases continuation with
  | rawSibling consumer _sameIndex _sameConclusion mateUnmarked location =>
      rcases location with selected | outside
      · have currentMateEq : current.mate = premise :=
          connectiveBelow_mate_eq_of_mate_eq structural consumer current selected
        have currentMateMarked :
            state.core.marks[current.mate]? = some (some markedAge) := by
          simpa [currentMateEq] using premiseMarked
        exact False.elim
          ((mateNotActive currentMateMarked) premiseRepresentative)
      · exact .rawOutside consumer.mate mateUnmarked outside
  | olderFuture boundary work older =>
      exact .olderFuture conclusion boundary work older conclusionNotOwned
  | olderMarked conclusionAge marked older =>
      exact .olderMarked conclusion conclusionAge marked older
        conclusionNotOwned

/-- A successful Nop guard rules out an active-representative concrete mark on
its current mate. -/
private theorem NopStep.mateNotActiveMarked
    {certificate : Certificate} {before after : ReservationState}
    (step : NopStep certificate before after) :
    ∀ {rawAge : RawTokenAge},
      before.core.marks[step.consumer.mate]? = some (some rawAge) →
        before.core.representative rawAge ≠ step.prepared.stackResult.rawAge := by
  intro rawAge marked
  rw [step.mate_unmarked_before] at marked
  simp at marked

/-- A successful Wait guard places its concretely marked current mate strictly
below the active raw boundary. -/
private theorem WaitStep.mateNotActiveMarked
    {certificate : Certificate} {before after : ReservationState}
    (step : WaitStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    ∀ {rawAge : RawTokenAge},
      before.core.marks[step.consumer.mate]? = some (some rawAge) →
        before.core.representative rawAge ≠ step.prepared.stackResult.rawAge := by
  intro rawAge marked
  have rawAgeEq : rawAge = step.mateRawAge :=
    Option.some.inj (Option.some.inj (marked.symm.trans step.mate_marked_before))
  subst rawAge
  have representativeLe :
      before.core.representative step.mateRawAge ≤ step.mateRawAge :=
    UnificationState.OrderedParents.representative_le
      invariant.core_orderedParents step.mateRawAge
  exact Nat.ne_of_lt (Nat.lt_of_le_of_lt representativeLe step.younger)

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

private theorem CanonicalTagHistory.ActiveCarrierTensorSameBoundaryResidual.externalTemporalOutcome
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
    ActiveCarrierParentExternalTemporalOutcome certificate state
      input.rawAge owned := by
  rcases residual with
    ⟨premise, markedAge, linkIndex, storedLeft, storedRight, conclusion,
      sibling, _event, _eventUsed, forestUsed, _leftPath, _rightPath,
      _premiseNeSelected, _premiseFrontier, premiseMarked, _authentic,
      premiseNotGlobal, linkLookup, premiseMembership, conclusionNotOwned,
      _premiseOwned, _representativeEq, _boundaryEq, orientation,
      siblingNotOwned, _eventLookup, _eventRawAge, _eventDerivation,
      _eventLinkUsed, occurrenceStored, _accounted, _eventLeftOwned,
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
      exact .rawOutside sibling siblingUnmarked siblingNotOwned
  | futureConclusion consumer boundary work =>
      have same := connectiveBelow_matches_tensor_parent invariant.structural
        consumer linkLookup premiseMembership orientation
      have workAtConclusion : FutureWorkAt state boundary conclusion := by
        rw [← same.2.1]
        exact work
      have older : boundary < input.rawAge :=
        workAtConclusion.boundary_lt_active_of_not_owned input invariant
          componentLookup occurrenceStored conclusionNotOwned
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
          componentLookup occurrenceStored markedConclusion conclusionNotOwned
      exact .olderMarked conclusion conclusionAge markedConclusion older
        conclusionNotOwned

private theorem ActiveCarrierParentTemporalResidual.externalTemporalOutcome
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {owned : List Vertex}
    (residual : ActiveCarrierParentTemporalResidual tagHistory input component owned)
    (invariant : SchedulerInvariant certificate state)
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (current : ConnectiveBelow certificate input.vertex)
    (mateNotActive :
      ∀ {rawAge : RawTokenAge},
        state.core.marks[current.mate]? = some (some rawAge) →
          state.core.representative rawAge ≠ input.rawAge) :
    ActiveCarrierParentExternalTemporalOutcome certificate state
      input.rawAge owned := by
  cases residual with
  | par parResidual =>
      exact parResidual.externalTemporalOutcome invariant.structural current
        mateNotActive
  | tensor tensorResidual _olderMarkedTensor =>
      exact tensorResidual.externalTemporalOutcome invariant componentLookup

/-- A failed Nop ready-tail obligation reduces to an external temporal parent
endpoint; its raw case cannot be the selected head. -/
theorem NopStep.externalParentTemporalOutcome_of_no_readyTail
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (step : NopStep certificate before after)
    (invariant : SchedulerInvariant certificate before)
    (noTail :
      ¬ ∃ pending,
        pending ∈ step.prepared.stackResult.remainingTop ∧
          pending ∉ certificate.conclusions) :
    ∃ (component : UnificationComponent) (usedLinks owned : List Nat),
      before.core.components[step.prepared.stackResult.rawAge]? =
          some (some component) ∧
        Certificate.ComponentOccurrenceWitness certificate component
          usedLinks owned ∧
        Certificate.OwnedOccurrenceAccounted before.core
          step.prepared.stackResult.rawAge component owned ∧
        ActiveCarrierParentExternalTemporalOutcome certificate before
          step.prepared.stackResult.rawAge owned := by
  let input := step.prepared.readyHeadInput
  rcases input.parentEscape_of_no_readyTail correct invariant step.consumer
      step.par_eq noTail with
    ⟨component, usedLinks, owned, componentLookup, occurrence, accounted,
      escape⟩
  have residual := escape.temporalResidual_of_no_readyTail tagHistory correct
    input invariant componentLookup occurrence accounted noTail
  exact ⟨component, usedLinks, owned, componentLookup, occurrence, accounted,
    residual.externalTemporalOutcome invariant componentLookup
      step.consumer step.mateNotActiveMarked⟩

/-- A failed Wait ready-tail obligation reduces to an external temporal parent
endpoint; its raw case cannot be the selected head. -/
theorem WaitStep.externalParentTemporalOutcome_of_no_readyTail
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (step : WaitStep certificate before after)
    (invariant : SchedulerInvariant certificate before)
    (noTail :
      ¬ ∃ pending,
        pending ∈ step.prepared.stackResult.remainingTop ∧
          pending ∉ certificate.conclusions) :
    ∃ (component : UnificationComponent) (usedLinks owned : List Nat),
      before.core.components[step.prepared.stackResult.rawAge]? =
          some (some component) ∧
        Certificate.ComponentOccurrenceWitness certificate component
          usedLinks owned ∧
        Certificate.OwnedOccurrenceAccounted before.core
          step.prepared.stackResult.rawAge component owned ∧
        ActiveCarrierParentExternalTemporalOutcome certificate before
          step.prepared.stackResult.rawAge owned := by
  let input := step.prepared.readyHeadInput
  rcases input.parentEscape_of_no_readyTail correct invariant step.consumer
      step.par_eq noTail with
    ⟨component, usedLinks, owned, componentLookup, occurrence, accounted,
      escape⟩
  have residual := escape.temporalResidual_of_no_readyTail tagHistory correct
    input invariant componentLookup occurrence accounted noTail
  exact ⟨component, usedLinks, owned, componentLookup, occurrence, accounted,
    residual.externalTemporalOutcome invariant componentLookup
      step.consumer (step.mateNotActiveMarked invariant)⟩

end SequentialFigure7
end ProofNetIR
