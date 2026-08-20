/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7ActiveTopDebtParentEscape
import ProofNetIR.SequentialFigure7ContinuationCreditPreservation
import ProofNetIR.SequentialFigure7RawMarkReservationAnchor
import ProofNetIR.SequentialFigure7OlderMarkedTensorPredecessorHistory

/-!
# Active-top debt parent-escape temporal residual

A failure-conditioned active-carrier parent escape has one of two exact
source shapes. A par source has an authentic reservation anchor and a raw,
strictly older queued, or strictly older marked continuation. A tensor
source's concrete mark resolves to the active representative while its sibling
and parent conclusion lie outside the active carrier.

This module does not derive a non-global ready-tail witness, rule out either
residual, assume or derive the history tail law, or prove progress. It only
normalizes the obstruction already forced when the ready tail is absent.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge


private def ActiveParCarrierParentEscape
    (certificate : Certificate) (state : ReservationState)
    (component : UnificationComponent) (owned : List Vertex)
    (selected : Vertex) : Prop :=
  ∃ (premise : Vertex) (markedAge : RawTokenAge) (linkIndex : Nat)
      (storedLeft storedRight conclusion : Vertex),
    premise ≠ selected ∧
      premise ∈ component.frontier ∧
      state.core.marks[premise]? = some (some markedAge) ∧
      premise ∉ certificate.conclusions ∧
      certificate.links[linkIndex]? =
        some (.par storedLeft storedRight conclusion) ∧
      premise ∈ (Link.par storedLeft storedRight conclusion).premises ∧
      conclusion ∉ owned

/-- The exact reservation event behind a raw mark, aligned to the current
active occurrence carrier. -/
def ActiveRawMarkReservationAnchor
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (component : UnificationComponent) (owned : List Vertex)
    (premise : Vertex) (markedAge : RawTokenAge) : Prop :=
  ∃ (event : ReservationEvent certificate) (eventUsed : List Nat)
      (leftPath rightPath : certificate.referenceSwitchingGraph.EdgeSimplePath),
    tagHistory.reservationLedger[markedAge]? = some event ∧
      event.rawAge = markedAge ∧
      certificate.OccurrenceDerivation component.tree component.frontier
        eventUsed owned ∧
      event.linkIndex ∈ eventUsed ∧
      premise ∈ owned ∧
      event.search.result.left ∈ owned ∧
      event.search.result.right ∈ owned ∧
      leftPath.start = premise ∧
      leftPath.finish = event.search.result.left ∧
      (∀ current ∈ leftPath.vertices, current ∈ owned) ∧
      rightPath.start = premise ∧
      rightPath.finish = event.search.result.right ∧
      ∀ current ∈ rightPath.vertices, current ∈ owned

/-- The current continuation of an escaped par premise is forced into one of
three temporal forms. The raw sibling is either the selected head or outside
the active carrier; queued or marked conclusions live strictly below the
active raw boundary. -/
inductive ActiveParParentContinuation
    (certificate : Certificate) (state : ReservationState)
    (activeRawAge : RawTokenAge) (selected : Vertex) (owned : List Vertex)
    (premise : Vertex) (linkIndex : Nat) (conclusion : Vertex) : Prop where
  | rawSibling
      (consumer : ConnectiveBelow certificate premise)
      (sameIndex : consumer.linkIndex = linkIndex)
      (sameConclusion : consumer.conclusion = conclusion)
      (mateUnmarked : state.core.marks[consumer.mate]? = some none)
      (mateLocation : consumer.mate = selected ∨ consumer.mate ∉ owned) :
      ActiveParParentContinuation certificate state activeRawAge selected owned
        premise linkIndex conclusion
  | olderFuture
      (boundary : RawTokenAge)
      (work : FutureWorkAt state boundary conclusion)
      (older : boundary < activeRawAge) :
      ActiveParParentContinuation certificate state activeRawAge selected owned
        premise linkIndex conclusion
  | olderMarked
      (conclusionAge : RawTokenAge)
      (marked : state.core.marks[conclusion]? = some (some conclusionAge))
      (olderRepresentative :
        state.core.representative conclusionAge < activeRawAge) :
      ActiveParParentContinuation certificate state activeRawAge selected owned
        premise linkIndex conclusion

/-- Failure-conditioned temporal normal form for a par carrier escape. -/
def ActiveParCarrierTemporalResidual
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (input : ReadyHeadInput state) (component : UnificationComponent)
    (owned : List Vertex) : Prop :=
  ∃ (premise : Vertex) (markedAge : RawTokenAge) (linkIndex : Nat)
      (storedLeft storedRight conclusion : Vertex),
    premise ≠ input.vertex ∧
      premise ∈ component.frontier ∧
      premise ∈ owned ∧
      state.core.marks[premise]? = some (some markedAge) ∧
      tagHistory.RawMarked markedAge premise ∧
      state.core.representative markedAge = input.rawAge ∧
      premise ∉ certificate.conclusions ∧
      certificate.links[linkIndex]? =
        some (.par storedLeft storedRight conclusion) ∧
      premise ∈ (Link.par storedLeft storedRight conclusion).premises ∧
      conclusion ∉ owned ∧
      ActiveRawMarkReservationAnchor tagHistory component owned premise markedAge ∧
      ActiveParParentContinuation certificate state input.rawAge input.vertex owned
        premise linkIndex conclusion

private theorem submittedParPremise_bound
    {certificate : Certificate} (structural : certificate.StructurallyWellFormed)
    {linkIndex left right conclusion premise : Vertex}
    (lookup : certificate.links[linkIndex]? = some (.par left right conclusion))
    (membership : premise ∈ (Link.par left right conclusion).premises) :
    premise < certificate.formulas.size := by
  have wellFormed := structural.2.2.2.2.1 _ (List.mem_of_getElem? lookup)
  simp [Link.premises] at membership
  rcases membership with rfl | rfl
  · exact wellFormed.2.2.2.1
  · exact wellFormed.2.2.2.2.1

private theorem submittedParMate_not_conclusion
    {certificate : Certificate} (structural : certificate.StructurallyWellFormed)
    {linkIndex left right conclusion mate : Vertex}
    (lookup : certificate.links[linkIndex]? = some (.par left right conclusion))
    (mateMembership : mate ∈ (Link.par left right conclusion).premises) :
    mate ∉ certificate.conclusions := by
  have mateBound := submittedParPremise_bound structural lookup mateMembership
  intro global
  have node := structural.2.2.2.2.2 mate mateBound
  have noParent : certificate.parentUseCount mate = 0 := by
    simpa [global] using node.2
  have linkMembership : Link.par left right conclusion ∈ certificate.links :=
    List.mem_of_getElem? lookup
  have filtered : Link.par left right conclusion ∈
      certificate.links.filter (·.usesAsPremise mate) := by
    apply List.mem_filter.mpr
    exact ⟨linkMembership, by simpa [Link.usesAsPremise] using mateMembership⟩
  have positive : 0 < certificate.parentUseCount mate := by
    unfold Certificate.parentUseCount
    exact List.length_pos_of_mem filtered
  omega

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

private theorem connectiveMate_not_conclusion
    {certificate : Certificate} {vertex : Vertex}
    (consumer : ConnectiveBelow certificate vertex)
    (structural : certificate.StructurallyWellFormed) :
    consumer.mate ∉ certificate.conclusions := by
  have mateMembership : consumer.mate ∈ consumer.submittedLink.premises := by
    cases kindEq : consumer.kind <;> cases sideEq : consumer.side <;>
      simp [ConnectiveBelow.submittedLink, SequentialConnectiveKind.asLink,
        Link.premises, ConnectiveBelow.mate, TensorPremiseSide.mate, kindEq, sideEq]
  have mateBound := consumer.mate_bound
  intro global
  have node := structural.2.2.2.2.2 consumer.mate mateBound
  have noParent : certificate.parentUseCount consumer.mate = 0 := by
    simpa [global] using node.2
  have linkMembership : consumer.submittedLink ∈ certificate.links :=
    List.mem_of_getElem? consumer.link_eq
  have filtered : consumer.submittedLink ∈
      certificate.links.filter (·.usesAsPremise consumer.mate) := by
    apply List.mem_filter.mpr
    exact ⟨linkMembership, by simpa [Link.usesAsPremise] using mateMembership⟩
  have positive : 0 < certificate.parentUseCount consumer.mate := by
    unfold Certificate.parentUseCount
    exact List.length_pos_of_mem filtered
  omega

private theorem connectiveBelow_matches_par_parent
    {certificate : Certificate} (structural : certificate.StructurallyWellFormed)
    {premise linkIndex left right conclusion : Vertex}
    (consumer : ConnectiveBelow certificate premise)
    (lookup : certificate.links[linkIndex]? = some (.par left right conclusion))
    (membership : premise ∈ (Link.par left right conclusion).premises) :
    consumer.linkIndex = linkIndex ∧ consumer.conclusion = conclusion := by
  have premiseBound := submittedParPremise_bound structural lookup membership
  have escapeIndex :
      certificate.consumerIndex.uniqueConsumer? premise = some linkIndex := by
    simpa [Certificate.consumerIndex] using
      ConsumerIndex.build_uniqueConsumer?_eq_some structural lookup premiseBound membership
  have sameIndex : consumer.linkIndex = linkIndex :=
    Option.some.inj (consumer.consumer_eq.symm.trans escapeIndex)
  have consumerLookup := consumer.link_eq
  rw [sameIndex] at consumerLookup
  have sameLink :
      consumer.kind.asLink consumer.storedLeft consumer.storedRight
          consumer.conclusion =
        .par left right conclusion :=
    Option.some.inj (consumerLookup.symm.trans lookup)
  have sameConclusion : consumer.conclusion = conclusion := by
    cases kindEq : consumer.kind with
    | par =>
        simp [SequentialConnectiveKind.asLink, kindEq] at sameLink
        exact sameLink.2.2
    | tensor =>
        simp [SequentialConnectiveKind.asLink, kindEq] at sameLink
  exact ⟨sameIndex, sameConclusion⟩

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
  · exact (List.pairwise_append.mp increasing).2.2 boundary inPrefix input.rawAge (by simp)
  · exact False.elim (boundaryNeActive same)

private theorem ReadyHeadInput.activeReadyExact
    {certificate : Certificate} {state : ReservationState}
    (input : ReadyHeadInput state)
    (invariant : SchedulerInvariant certificate state)
    {component : UnificationComponent}
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component)) :
    ∀ pending,
      pending ∈ input.vertex :: input.readyTail ↔
        pending ∈ component.frontier ∧
          state.core.marks[pending]? = some none := by
  rcases List.getLast?_eq_some_iff.mp input.top_ready with
    ⟨readyPrefix, readyEquation⟩
  rcases List.getLast?_eq_some_iff.mp input.sigma_top with
    ⟨sigmaPrefix, sigmaEquation⟩
  have prefixLengths : readyPrefix.length = sigmaPrefix.length := by
    have aligned := invariant.stack_wellShaped.ready_aligned
    rw [readyEquation, sigmaEquation] at aligned
    simp at aligned
    omega
  have sigmaLookup :
      state.stack.sigma[readyPrefix.length]? = some input.rawAge := by
    rw [sigmaEquation, prefixLengths]
    simp
  have readyLookup :
      state.stack.ready[readyPrefix.length]? =
        some (input.vertex :: input.readyTail) := by
    rw [readyEquation]
    simp
  rcases invariant.ready_bucket_frontier_exact sigmaLookup readyLookup with
    ⟨actual, actualLookup, exactMembership⟩
  have actualEq : actual = component :=
    Option.some.inj
      (Option.some.inj (actualLookup.symm.trans componentLookup))
  subst actual
  exact exactMembership

/-- A failure-conditioned par escape has an authentic event anchor and one
of three exact temporal continuations: an exposed raw sibling, strictly older
queued parent work, or a strictly older marked parent conclusion. -/
private theorem parTemporalResidual
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (input : ReadyHeadInput state)
    (invariant : SchedulerInvariant certificate state)
    {component : UnificationComponent} {usedLinks owned : List Nat}
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component
        usedLinks owned)
    (accounted :
      Certificate.OwnedOccurrenceAccounted state.core input.rawAge
        component owned)
    (escape :
      ActiveParCarrierParentEscape certificate state component owned
        input.vertex)
    (noTail :
      ¬ ∃ pending,
        pending ∈ input.readyTail ∧ pending ∉ certificate.conclusions) :
    ActiveParCarrierTemporalResidual tagHistory input component owned := by
  rcases escape with
    ⟨premise, markedAge, linkIndex, storedLeft, storedRight, conclusion,
      premiseNeSelected, premiseFrontier, premiseMarked, premiseNotGlobal,
      parLookup, premiseMembership, conclusionNotOwned⟩
  have premiseOwned : premise ∈ owned :=
    occurrence.derivation.frontier_subset_owned premise premiseFrontier
  have premiseRepresentative :
      state.core.representative markedAge = input.rawAge := by
    rcases accounted premise premiseOwned with markedCase | unmarkedCase
    · rcases markedCase with ⟨accountedAge, accountedMarked, representative⟩
      have ageEq : accountedAge = markedAge :=
        Option.some.inj (Option.some.inj
          (accountedMarked.symm.trans premiseMarked))
      simpa [ageEq] using representative
    · exact False.elim (by
        have impossible := unmarkedCase.1.symm.trans premiseMarked
        simp at impossible)
  have authentic : tagHistory.RawMarked markedAge premise :=
    tagHistory.final_rawMarked_iff.mp premiseMarked
  have reservationAnchor :
      ActiveRawMarkReservationAnchor tagHistory component owned premise markedAge := by
    rcases tagHistory.rawMarked_reservationEvent_referenceAnchors invariant
        premiseMarked with
      ⟨event, anchorComponent, eventUsed, _forestUsed, anchorOwned,
        leftPath, rightPath, eventLookup, eventRawAge, anchorLookup,
        anchorDerivation, eventLink, _anchorWitness, _anchorAccounted,
        premiseAnchorOwned, leftOwned, rightOwned, leftStarts, leftFinishes,
        leftWithin, rightStarts, rightFinishes, rightWithin⟩
    have anchorLookupAtActive :
        state.core.components[input.rawAge]? = some (some anchorComponent) := by
      simpa [premiseRepresentative] using anchorLookup
    have componentEq : anchorComponent = component :=
      Option.some.inj
        (Option.some.inj (anchorLookupAtActive.symm.trans componentLookup))
    subst anchorComponent
    have ownedEq : anchorOwned = owned :=
      Certificate.OccurrenceDerivation.owned_unique invariant.structural
        anchorDerivation occurrence.derivation
    subst anchorOwned
    exact ⟨event, eventUsed, leftPath, rightPath, eventLookup, eventRawAge,
      anchorDerivation, eventLink, premiseAnchorOwned, leftOwned, rightOwned,
      leftStarts, leftFinishes, leftWithin, rightStarts, rightFinishes,
      rightWithin⟩
  have continuationCredit :
      ContinuationCredit certificate state premise :=
    tagHistory.markedNonconclusionContinuation premiseMarked premiseNotGlobal
  have continuation :
      ActiveParParentContinuation certificate state input.rawAge input.vertex
        owned premise linkIndex conclusion := by
    cases continuationCredit with
    | rawMate consumer mateUnmarked =>
        have same := connectiveBelow_matches_par_parent invariant.structural
          consumer parLookup premiseMembership
        have mateLocation :
            consumer.mate = input.vertex ∨ consumer.mate ∉ owned := by
          by_cases mateOwned : consumer.mate ∈ owned
          · have mateReady : consumer.mate ∈ input.vertex :: input.readyTail := by
              apply (input.activeReadyExact invariant componentLookup
                consumer.mate).mpr
              rcases accounted consumer.mate mateOwned with
                markedCase | unmarkedCase
              · rcases markedCase with ⟨mateAge, mateMarked, _representative⟩
                have impossible := mateMarked.symm.trans mateUnmarked
                simp at impossible
              · exact ⟨unmarkedCase.2, unmarkedCase.1⟩
            simp only [List.mem_cons] at mateReady
            rcases mateReady with mateSelected | mateTail
            · exact Or.inl mateSelected
            · exact False.elim (noTail ⟨consumer.mate, mateTail,
                connectiveMate_not_conclusion consumer invariant.structural⟩)
          · exact Or.inr mateOwned
        exact ActiveParParentContinuation.rawSibling consumer same.1 same.2
          mateUnmarked mateLocation
    | futureConclusion consumer boundary work =>
        have same := connectiveBelow_matches_par_parent invariant.structural
          consumer parLookup premiseMembership
        have workAtEscaped : FutureWorkAt state boundary conclusion := by
          rw [← same.2]
          exact work
        have older : boundary < input.rawAge :=
          workAtEscaped.boundary_lt_active_of_not_owned input invariant
            componentLookup occurrence conclusionNotOwned
        exact ActiveParParentContinuation.olderFuture boundary workAtEscaped older
    | markedConclusion consumer conclusionAge marked =>
        have same := connectiveBelow_matches_par_parent invariant.structural
          consumer parLookup premiseMembership
        have markedAtEscaped :
            state.core.marks[conclusion]? = some (some conclusionAge) := by
          rw [← same.2]
          exact marked
        have older :
            state.core.representative conclusionAge < input.rawAge :=
          markedOutsideActiveOwned_representative_lt input invariant
            componentLookup occurrence markedAtEscaped conclusionNotOwned
        exact ActiveParParentContinuation.olderMarked conclusionAge
          markedAtEscaped older
  exact ⟨premise, markedAge, linkIndex, storedLeft, storedRight, conclusion,
    premiseNeSelected, premiseFrontier, premiseOwned, premiseMarked, authentic,
    premiseRepresentative, premiseNotGlobal, parLookup, premiseMembership,
    conclusionNotOwned, reservationAnchor, continuation⟩

/-- Tensor specialization of the exact active-carrier parent escape. -/
private def ActiveCarrierTensorParentEscape
    (certificate : Certificate) (state : ReservationState)
    (component : UnificationComponent) (owned : List Vertex)
    (selected : Vertex) : Prop :=
  ∃ (premise : Vertex) (markedAge : RawTokenAge) (linkIndex : Nat)
      (storedLeft storedRight conclusion : Vertex),
    premise ≠ selected ∧
      premise ∈ component.frontier ∧
      state.core.marks[premise]? = some (some markedAge) ∧
      premise ∉ certificate.conclusions ∧
      certificate.links[linkIndex]? =
        some (.tensor storedLeft storedRight conclusion) ∧
      premise ∈ (Link.tensor storedLeft storedRight conclusion).premises ∧
      conclusion ∉ owned

private theorem markedFrontier_representative_eq
    {certificate : Certificate} {state : ReservationState}
    {component : UnificationComponent} {usedLinks owned : List Nat}
    {active markedAge : RawTokenAge} {premise : Vertex}
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component
        usedLinks owned)
    (accounted :
      Certificate.OwnedOccurrenceAccounted state.core active component owned)
    (premiseFrontier : premise ∈ component.frontier)
    (premiseMarked :
      state.core.marks[premise]? = some (some markedAge)) :
    state.core.representative markedAge = active := by
  have premiseOwned : premise ∈ owned :=
    occurrence.derivation.frontier_subset_owned premise premiseFrontier
  rcases accounted premise premiseOwned with marked | raw
  · rcases marked with ⟨actualAge, actualMarked, representative⟩
    have ageEq : actualAge = markedAge :=
      Option.some.inj (Option.some.inj (actualMarked.symm.trans premiseMarked))
    simpa [ageEq] using representative
  · exact False.elim (by
      rcases raw with ⟨premiseUnmarked, _frontier⟩
      rw [premiseMarked] at premiseUnmarked
      simp at premiseUnmarked)

private theorem tensorSibling_not_owned
    {certificate : Certificate} {component : UnificationComponent}
    {usedLinks owned : List Nat}
    (structural : certificate.StructurallyWellFormed)
    (acyclic : certificate.referenceSwitchingGraph.Acyclic)
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component
        usedLinks owned)
    {premise left right conclusion : Vertex} {linkIndex : Nat}
    (linkLookup :
      certificate.links[linkIndex]? = some (.tensor left right conclusion))
    (premiseMembership :
      premise ∈ (Link.tensor left right conclusion).premises)
    (premiseOwned : premise ∈ owned)
    (conclusionNotOwned : conclusion ∉ owned) :
    ∃ sibling,
      ((premise = left ∧ sibling = right) ∨
        (premise = right ∧ sibling = left)) ∧
      sibling ∉ owned := by
  have linkMembership : Link.tensor left right conclusion ∈ certificate.links :=
    List.mem_of_getElem? linkLookup
  have premiseCases : premise = left ∨ premise = right := by
    simpa [Link.premises] using premiseMembership
  rcases premiseCases with premiseEq | premiseEq
  · subst premise
    refine ⟨right, Or.inl ⟨rfl, rfl⟩, ?_⟩
    intro rightOwned
    rcases occurrence.referencePath_within_owned premiseOwned rightOwned with
      ⟨path, pathStarts, pathFinishes, pathWithin⟩
    apply referenceAcyclic_no_tensorBypass structural acyclic linkMembership
      path pathStarts pathFinishes
    intro conclusionInPath
    exact conclusionNotOwned (pathWithin conclusion conclusionInPath)
  · subst premise
    refine ⟨left, Or.inr ⟨rfl, rfl⟩, ?_⟩
    intro leftOwned
    rcases occurrence.referencePath_within_owned leftOwned premiseOwned with
      ⟨path, pathStarts, pathFinishes, pathWithin⟩
    apply referenceAcyclic_no_tensorBypass structural acyclic linkMembership
      path pathStarts pathFinishes
    intro conclusionInPath
    exact conclusionNotOwned (pathWithin conclusion conclusionInPath)

namespace CanonicalTagHistory

/-- Exact tensor-specific residue after occurrence geometry and raw-mark
history have been exhausted. The escaped source is anchored inside the
active carrier, while both its tensor sibling and its tensor conclusion are
outside.  Its concrete raw age resolves to the active sigma boundary, so the
strict-older premise of `OlderMarkedTensorPredecessorInvariant` is unavailable
for this occurrence. -/
def ActiveCarrierTensorSameBoundaryResidual
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (input : ReadyHeadInput state)
    (component : UnificationComponent) (owned : List Vertex) : Prop :=
  ∃ (premise : Vertex) (markedAge : RawTokenAge) (linkIndex : Nat)
      (storedLeft storedRight conclusion sibling : Vertex)
      (event : ReservationEvent certificate)
      (eventUsed forestUsed : List Nat)
      (leftPath rightPath :
        certificate.referenceSwitchingGraph.EdgeSimplePath),
    premise ≠ input.vertex ∧
      premise ∈ component.frontier ∧
      state.core.marks[premise]? = some (some markedAge) ∧
      tagHistory.RawMarked markedAge premise ∧
      premise ∉ certificate.conclusions ∧
      certificate.links[linkIndex]? =
        some (.tensor storedLeft storedRight conclusion) ∧
      premise ∈ (Link.tensor storedLeft storedRight conclusion).premises ∧
      conclusion ∉ owned ∧
      premise ∈ owned ∧
      state.core.representative markedAge = input.rawAge ∧
      sigmaBoundary? state.stack.sigma markedAge = some input.rawAge ∧
      ((premise = storedLeft ∧ sibling = storedRight) ∨
        (premise = storedRight ∧ sibling = storedLeft)) ∧
      sibling ∉ owned ∧
      tagHistory.reservationLedger[markedAge]? = some event ∧
      event.rawAge = markedAge ∧
      certificate.OccurrenceDerivation component.tree component.frontier
        eventUsed owned ∧
      event.linkIndex ∈ eventUsed ∧
      certificate.ComponentOccurrenceWitness component forestUsed owned ∧
      Certificate.OwnedOccurrenceAccounted state.core input.rawAge component owned ∧
      event.search.result.left ∈ owned ∧
      event.search.result.right ∈ owned ∧
      leftPath.start = premise ∧
      leftPath.finish = event.search.result.left ∧
      (∀ current ∈ leftPath.vertices, current ∈ owned) ∧
      rightPath.start = premise ∧
      rightPath.finish = event.search.result.right ∧
      ∀ current ∈ rightPath.vertices, current ∈ owned

end CanonicalTagHistory

/-- Correctness, exact occurrence accounting, and canonical raw-mark history
reduce a tensor parent escape to the same-boundary external-sibling residual.
The full-history older marked-tensor predecessor invariant is returned too;
its strict-order trigger is not fabricated. -/
private theorem tensorSameBoundaryResidual
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (input : ReadyHeadInput state)
    (invariant : SchedulerInvariant certificate state)
    {component : UnificationComponent} {usedLinks owned : List Nat}
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component
        usedLinks owned)
    (accounted :
      Certificate.OwnedOccurrenceAccounted state.core input.rawAge component owned)
    (escape :
      ActiveCarrierTensorParentEscape certificate state component owned
        input.vertex) :
    tagHistory.ActiveCarrierTensorSameBoundaryResidual input component owned ∧
      OlderMarkedTensorPredecessorInvariant certificate state := by
  rcases escape with
    ⟨premise, markedAge, linkIndex, storedLeft, storedRight, conclusion,
      premiseNeSelected, premiseFrontier, premiseMarked, premiseNotGlobal,
      linkLookup, premiseMembership, conclusionNotOwned⟩
  have premiseOwned : premise ∈ owned :=
    occurrence.derivation.frontier_subset_owned premise premiseFrontier
  have representativeEq :
      state.core.representative markedAge = input.rawAge :=
    markedFrontier_representative_eq occurrence accounted premiseFrontier
      premiseMarked
  have stackMarked :
      state.stack.marks[premise]? = some (some markedAge) := by
    rw [← invariant.realizesSigma.marks_eq]
    exact premiseMarked
  have markedAgeBound : markedAge < state.stack.nextAge :=
    invariant.stack_wellShaped.assigned_age_bound premise markedAge stackMarked
  have boundaryEq :
      sigmaBoundary? state.stack.sigma markedAge = some input.rawAge := by
    calc
      sigmaBoundary? state.stack.sigma markedAge =
          some (state.core.representative markedAge) :=
        invariant.realizesSigma.representative_eq_boundary markedAgeBound
      _ = some input.rawAge := congrArg some representativeEq
  have authentic : tagHistory.RawMarked markedAge premise :=
    tagHistory.final_rawMarked_iff.mp premiseMarked
  rcases tensorSibling_not_owned invariant.structural
      correct.referenceSwitchingTree.acyclic occurrence linkLookup
      premiseMembership premiseOwned conclusionNotOwned with
    ⟨sibling, siblingOrientation, siblingNotOwned⟩
  rcases tagHistory.rawMarked_reservationEvent_referenceAnchors invariant
      premiseMarked with
    ⟨event, eventComponent, eventUsed, forestUsed, eventOwned,
      leftPath, rightPath, eventLookup, eventRawAge,
      eventComponentLookup, eventDerivation, eventLinkUsed, eventWitness,
      eventAccounted, _premiseEventOwned, eventLeftOwned, eventRightOwned,
      leftStarts, leftFinishes, leftWithin, rightStarts, rightFinishes,
      rightWithin⟩
  have eventComponentLookupAtActive :
      state.core.components[input.rawAge]? = some (some eventComponent) := by
    simpa [representativeEq] using eventComponentLookup
  have eventComponentEq : eventComponent = component :=
    Option.some.inj
      (Option.some.inj (eventComponentLookupAtActive.symm.trans componentLookup))
  subst eventComponent
  have eventOwnedEq : eventOwned = owned :=
    Certificate.OccurrenceDerivation.owned_unique invariant.structural
      eventDerivation occurrence.derivation
  subst eventOwned
  refine ⟨?_, tagHistory.olderMarkedTensorPredecessorInvariant correct⟩
  exact ⟨premise, markedAge, linkIndex, storedLeft, storedRight, conclusion,
    sibling, event, eventUsed, forestUsed, leftPath, rightPath,
    premiseNeSelected, premiseFrontier, premiseMarked, authentic,
    premiseNotGlobal, linkLookup, premiseMembership, conclusionNotOwned,
    premiseOwned, representativeEq, boundaryEq, siblingOrientation,
    siblingNotOwned, eventLookup, eventRawAge, eventDerivation, eventLinkUsed,
    eventWitness, by simpa [representativeEq] using eventAccounted,
    eventLeftOwned, eventRightOwned, leftStarts, leftFinishes, leftWithin,
    rightStarts, rightFinishes, rightWithin⟩


/-- The exact failure-conditioned temporal normal form of an active-carrier
parent escape. The tensor branch retains the canonical older marked-tensor
invariant without fabricating its strict-order trigger. -/
inductive ActiveCarrierParentTemporalResidual
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (input : ReadyHeadInput state) (component : UnificationComponent)
    (owned : List Vertex) : Prop where
  | par
      (residual : ActiveParCarrierTemporalResidual tagHistory input component owned) :
      ActiveCarrierParentTemporalResidual tagHistory input component owned
  | tensor
      (residual : tagHistory.ActiveCarrierTensorSameBoundaryResidual
        input component owned)
      (olderMarkedTensor : OlderMarkedTensorPredecessorInvariant certificate state) :
      ActiveCarrierParentTemporalResidual tagHistory input component owned

/-- Normalize an exact no-tail parent escape by the submitted source kind.
The result is a par temporal continuation or the tensor same-boundary
external-sibling residual. This theorem does not eliminate either branch. -/
theorem ActiveCarrierParentEscape.temporalResidual_of_no_readyTail
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (input : ReadyHeadInput state)
    (invariant : SchedulerInvariant certificate state)
    {component : UnificationComponent} {usedLinks owned : List Nat}
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component
        usedLinks owned)
    (accounted :
      Certificate.OwnedOccurrenceAccounted state.core input.rawAge
        component owned)
    (escape :
      ActiveCarrierParentEscape certificate state component owned input.vertex)
    (noTail :
      ¬ ∃ pending,
        pending ∈ input.readyTail ∧ pending ∉ certificate.conclusions) :
    ActiveCarrierParentTemporalResidual tagHistory input component owned := by
  rcases escape with
    ⟨premise, markedAge, linkIndex, kind, storedLeft, storedRight, conclusion,
      premiseNeSelected, premiseFrontier, premiseMarked, premiseNotGlobal,
      linkLookup, premiseMembership, conclusionNotOwned⟩
  cases kind with
  | par =>
      have parEscape :
          ActiveParCarrierParentEscape certificate state component owned
            input.vertex :=
        ⟨premise, markedAge, linkIndex, storedLeft, storedRight, conclusion,
          premiseNeSelected, premiseFrontier, premiseMarked, premiseNotGlobal,
          by simpa [SequentialConnectiveKind.asLink] using linkLookup,
          by simpa [SequentialConnectiveKind.asLink] using premiseMembership,
          conclusionNotOwned⟩
      exact .par (parTemporalResidual tagHistory input invariant componentLookup
        occurrence accounted parEscape noTail)
  | tensor =>
      have tensorEscape :
          ActiveCarrierTensorParentEscape certificate state component owned
            input.vertex :=
        ⟨premise, markedAge, linkIndex, storedLeft, storedRight, conclusion,
          premiseNeSelected, premiseFrontier, premiseMarked, premiseNotGlobal,
          by simpa [SequentialConnectiveKind.asLink] using linkLookup,
          by simpa [SequentialConnectiveKind.asLink] using premiseMembership,
          conclusionNotOwned⟩
      rcases tensorSameBoundaryResidual tagHistory correct input invariant
          componentLookup occurrence accounted tensorEscape with
        ⟨residual, olderMarkedTensor⟩
      exact .tensor residual olderMarkedTensor

end SequentialFigure7
end ProofNetIR
