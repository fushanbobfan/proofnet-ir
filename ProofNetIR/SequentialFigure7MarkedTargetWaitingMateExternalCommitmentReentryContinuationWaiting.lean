/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7MarkedTargetWaitingMateExternalCommitmentReentryContinuationExit

/-!
# Figure-7 waiting-mate commitment re-entry continuation waiting

Carrier-forest ownership collapses every non-reflexive marked-conclusion
continuation at the external parent. The selected/current-mate return and the
marked-global endpoint are impossible, while an older future endpoint must be
located in the exact initialized waiting bucket.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge

/-- Exact scheduler data for future work residing in an initialized waiting
bucket. -/
def FutureWorkAtExactWaitingLocation
    (certificate : Certificate) (state : ReservationState)
    (boundary : RawTokenAge) (vertex : Vertex) : Prop :=
  ∃ (payload : List Vertex) (linkIndex : Nat) (left right : Vertex)
      (olderPremise youngerPremise : Vertex)
      (olderAge youngerAge youngerBoundary : RawTokenAge),
    state.stack.waiting[boundary]? = some (.initialized payload) ∧
      vertex ∈ payload ∧
      certificate.links[linkIndex]? = some (.par left right vertex) ∧
      (SequentialUnification.sourceIndex certificate)[vertex]? =
        some [{ linkIndex := linkIndex, link := .par left right vertex }] ∧
      state.core.marks[vertex]? = some none ∧
      ((olderPremise = left ∧ youngerPremise = right) ∨
        (olderPremise = right ∧ youngerPremise = left)) ∧
      state.core.marks[olderPremise]? = some (some olderAge) ∧
      state.core.marks[youngerPremise]? = some (some youngerAge) ∧
      sigmaBoundary? state.stack.sigma olderAge = some boundary ∧
      sigmaBoundary? state.stack.sigma youngerAge = some youngerBoundary ∧
      boundary < youngerBoundary

private theorem connectiveSubmitted
    {certificate : Certificate} {vertex : Vertex}
    (consumer : ConnectiveBelow certificate vertex) :
    certificate.links[consumer.linkIndex]? =
        some (.tensor consumer.storedLeft consumer.storedRight
          consumer.conclusion) ∨
      certificate.links[consumer.linkIndex]? =
        some (.par consumer.storedLeft consumer.storedRight
          consumer.conclusion) := by
  cases kindEq : consumer.kind with
  | tensor =>
      exact Or.inl (by
        simpa [ConnectiveBelow.submittedLink,
          SequentialConnectiveKind.asLink, kindEq] using consumer.link_eq)
  | par =>
      exact Or.inr (by
        simpa [ConnectiveBelow.submittedLink,
          SequentialConnectiveKind.asLink, kindEq] using consumer.link_eq)

private theorem connectiveVertexOwnedOfPremisesOwned
    {certificate : Certificate} {vertex : Vertex}
    (consumer : ConnectiveBelow certificate vertex)
    {owned : List Vertex}
    (premisesOwned :
      consumer.storedLeft ∈ owned ∧ consumer.storedRight ∈ owned) :
    vertex ∈ owned := by
  have premiseEq := consumer.premise_eq
  cases kindEq : consumer.kind <;> cases sideEq : consumer.side <;>
    simp_all [TensorPremiseSide.premise]

private theorem MarkedConclusionChain.originOwnedOfTerminalOwned
    {certificate : Certificate} {state : ReservationState}
    {origin terminal : Vertex}
    (structural : certificate.StructurallyWellFormed)
    {tree : CutFreeDerivation} {frontier usedLinks owned : List Nat}
    (occurrence :
      Certificate.OccurrenceDerivation certificate tree frontier usedLinks owned)
    (chain : MarkedConclusionChain certificate state origin terminal)
    (terminalOwned : terminal ∈ owned) :
    origin ∈ owned := by
  induction chain with
  | refl => exact terminalOwned
  | step consumer _marked _notConclusion _tail induction =>
      have premisesOwned :=
        occurrence.connectivePremises_owned_of_conclusion_owned structural
          (induction terminalOwned) (connectiveSubmitted consumer)
      exact connectiveVertexOwnedOfPremisesOwned consumer premisesOwned

private theorem terminalOwnedOfConclusionOwned
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {tree : CutFreeDerivation} {frontier usedLinks owned : List Nat}
    (occurrence :
      Certificate.OccurrenceDerivation certificate tree frontier usedLinks owned)
    {terminal : Vertex} (consumer : ConnectiveBelow certificate terminal)
    (conclusionOwned : consumer.conclusion ∈ owned) :
    terminal ∈ owned := by
  have premisesOwned :=
    occurrence.connectivePremises_owned_of_conclusion_owned structural
      conclusionOwned (connectiveSubmitted consumer)
  exact connectiveVertexOwnedOfPremisesOwned consumer premisesOwned

private theorem connectiveBelowMateConclusionEq
    {certificate : Certificate} {vertex : Vertex}
    (left right : ConnectiveBelow certificate vertex) :
    left.mate = right.mate ∧ left.conclusion = right.conclusion := by
  have sameIndex : left.linkIndex = right.linkIndex :=
    Option.some.inj (left.consumer_eq.symm.trans right.consumer_eq)
  have leftLookup := left.link_eq
  rw [sameIndex] at leftLookup
  have sameLink :
      left.kind.asLink left.storedLeft left.storedRight left.conclusion =
        right.kind.asLink right.storedLeft right.storedRight right.conclusion :=
    Option.some.inj (leftLookup.symm.trans right.link_eq)
  have leftPremise := left.premise_eq
  have rightPremise := right.premise_eq
  cases leftKind : left.kind <;> cases rightKind : right.kind <;>
    cases leftSide : left.side <;> cases rightSide : right.side <;>
      simp_all [SequentialConnectiveKind.asLink, ConnectiveBelow.mate,
        TensorPremiseSide.mate, TensorPremiseSide.premise]

private theorem noMarkedOutsideParent
    {certificate : Certificate} {state : ReservationState}
    {active : RawTokenAge} {component : UnificationComponent}
    {activeUsed activeOwned : List Nat}
    (invariant : SchedulerInvariant certificate state)
    (activeLookup : state.core.components[active]? = some (some component))
    (activeOccurrence :
      certificate.ComponentOccurrenceWitness component activeUsed activeOwned)
    {origin : Vertex} (originFrontier : origin ∈ component.frontier)
    (consumer : ConnectiveBelow certificate origin)
    (conclusionOutside : consumer.conclusion ∉ activeOwned)
    {rawAge : RawTokenAge}
    (marked : state.core.marks[consumer.conclusion]? = some (some rawAge)) :
    False := by
  rcases invariant.component_forest_provenance with
    ⟨usedAt, ownedAt, live, separated, markedOwned⟩
  have activeFacts := live activeLookup
  have activeOwnedEq : activeOwned = ownedAt active :=
    Certificate.OccurrenceDerivation.owned_unique invariant.structural
      activeOccurrence.derivation activeFacts.1.derivation
  have originActive : origin ∈ ownedAt active :=
    activeFacts.1.derivation.frontier_subset_owned origin originFrontier
  rcases markedOwned marked with
    ⟨ownerIndex, ownerComponent, _ownerRepresentative, ownerLookup,
      conclusionOwner⟩
  by_cases sameIndex : ownerIndex = active
  · have conclusionActive : consumer.conclusion ∈ ownedAt active := by
      simpa [sameIndex] using conclusionOwner
    exact conclusionOutside (by simpa [activeOwnedEq] using conclusionActive)
  · have ownerFacts := live ownerLookup
    have originOwner : origin ∈ ownedAt ownerIndex :=
      terminalOwnedOfConclusionOwned invariant.structural
        ownerFacts.1.derivation consumer conclusionOwner
    exact (separated ownerLookup activeLookup sameIndex).2
      origin originOwner originActive

private theorem MarkedConclusionChain.terminalEqOrigin
    {certificate : Certificate} {state : ReservationState}
    {active : RawTokenAge} {component : UnificationComponent}
    {activeUsed activeOwned : List Nat}
    (invariant : SchedulerInvariant certificate state)
    (activeLookup : state.core.components[active]? = some (some component))
    (activeOccurrence :
      certificate.ComponentOccurrenceWitness component activeUsed activeOwned)
    {origin terminal : Vertex} (originFrontier : origin ∈ component.frontier)
    (firstConsumer : ConnectiveBelow certificate origin)
    (firstConclusionOutside : firstConsumer.conclusion ∉ activeOwned)
    (chain : MarkedConclusionChain certificate state origin terminal) :
    terminal = origin := by
  cases chain with
  | refl => rfl
  | step chainConsumer firstMarked _notConclusion _tail =>
      have same := connectiveBelowMateConclusionEq chainConsumer firstConsumer
      have markedAtFirst : ∃ firstAge,
          state.core.marks[firstConsumer.conclusion]? =
            some (some firstAge) := by
        exact ⟨_, by simpa [same.2] using firstMarked⟩
      rcases markedAtFirst with ⟨firstAge, markedAtFirst⟩
      exact False.elim
        (noMarkedOutsideParent invariant activeLookup activeOccurrence
          originFrontier firstConsumer firstConclusionOutside markedAtFirst)

private theorem futureWorkExactWaitingLocation
    {certificate : Certificate} {state : ReservationState}
    {active : RawTokenAge} {component : UnificationComponent}
    (invariant : SchedulerInvariant certificate state)
    (activeLookup : state.core.components[active]? = some (some component))
    {origin terminal : Vertex}
    (originFrontier : origin ∈ component.frontier)
    (chain : MarkedConclusionChain certificate state origin terminal)
    (consumer : ConnectiveBelow certificate terminal)
    {boundary : RawTokenAge}
    (work : FutureWorkAt state boundary consumer.conclusion)
    (boundaryOlder : boundary < active) :
    FutureWorkAtExactWaitingLocation certificate state boundary
      consumer.conclusion := by
  have location := work.exactSchedulerLocation invariant
  cases location with
  | ready sigmaAt readyAt member endpointLookup endpointFrontier unmarked =>
      rcases invariant.component_forest_provenance with
        ⟨usedAt, ownedAt, live, separated, _markedOwned⟩
      have activeFacts := live activeLookup
      have originActive : origin ∈ ownedAt active :=
        activeFacts.1.derivation.frontier_subset_owned origin originFrontier
      have endpointFacts := live endpointLookup
      have conclusionOwned : consumer.conclusion ∈ ownedAt boundary :=
        endpointFacts.1.derivation.frontier_subset_owned
          consumer.conclusion endpointFrontier
      have terminalOwned : terminal ∈ ownedAt boundary :=
        terminalOwnedOfConclusionOwned invariant.structural
          endpointFacts.1.derivation consumer conclusionOwned
      have originOlder : origin ∈ ownedAt boundary :=
        chain.originOwnedOfTerminalOwned invariant.structural
          endpointFacts.1.derivation terminalOwned
      have different : boundary ≠ active := Nat.ne_of_lt boundaryOlder
      exact False.elim
        ((separated endpointLookup activeLookup different).2 origin
          originOlder originActive)
  | waiting waitingAt member linkLookup sourceLookup unmarked
      premiseOrientation olderMarked youngerMarked olderBoundary
      youngerBoundaryLookup boundaryLt =>
      exact ⟨_, _, _, _, _, _, _, _, _, waitingAt, member, linkLookup,
        sourceLookup, unmarked, premiseOrientation, olderMarked, youngerMarked,
        olderBoundary, youngerBoundaryLookup, boundaryLt⟩

/-- The external marked parent after ownership normalization: its mate is a raw
vertex outside the active carrier, or its conclusion is older work located in
an exact initialized waiting bucket. -/
def ActiveCarrierExternalReentryMarkedOuterMateSeparatedWaitingParentTarget
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (input : ReadyHeadInput state) (component : UnificationComponent)
    (owned : List Vertex) (endpoint : Vertex)
    (current : ConnectiveBelow certificate input.vertex) : Prop :=
  ∃ (path : certificate.referenceSwitchingGraph.EdgeSimplePath)
      (directed : certificate.referenceSwitchingGraph.DirectedEdge)
      (markedAge : RawTokenAge),
    path.start = endpoint ∧
      path.finish ∈ owned ∧
      directed ∈ path.traversed ∧
      ActiveCarrierInboundParentEdge certificate component owned directed ∧
      directed.target ≠ input.vertex ∧
      directed.target ≠ current.mate ∧
      state.core.marks[directed.target]? = some (some markedAge) ∧
      tagHistory.RawMarked markedAge directed.target ∧
      state.core.representative markedAge = input.rawAge ∧
      ∃ targetConsumer : ConnectiveBelow certificate directed.target,
        targetConsumer.mate ≠ input.vertex ∧
          directed.source = targetConsumer.conclusion ∧
          targetConsumer.conclusion ∉ owned ∧
          ((state.core.marks[targetConsumer.mate]? = some none ∧
              targetConsumer.mate ∉ owned) ∨
            ∃ boundary,
              FutureWorkAt state boundary targetConsumer.conclusion ∧
                boundary < input.rawAge ∧
                FutureWorkAtExactWaitingLocation certificate state boundary
                  targetConsumer.conclusion)

namespace ActiveCarrierExternalReentryMarkedOuterMateSeparatedContinuationExitTarget

/-- Collapse all continuation chains at an external marked parent, eliminate
the selected return and marked-global cases, and refine older future work to
its exact initialized waiting location. -/
theorem waitingParentTarget
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {usedLinks owned : List Nat} {endpoint : Vertex}
    (invariant : SchedulerInvariant certificate state)
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      certificate.ComponentOccurrenceWitness component usedLinks owned)
    {current : ConnectiveBelow certificate input.vertex}
    (target :
      ActiveCarrierExternalReentryMarkedOuterMateSeparatedContinuationExitTarget
        tagHistory input component owned endpoint current) :
    ActiveCarrierExternalReentryMarkedOuterMateSeparatedWaitingParentTarget
      tagHistory input component owned endpoint current := by
  rcases target with
    ⟨path, directed, markedAge, pathStarts, finishOwned, directedMembership,
      parentEdge, targetNeSelected, targetNeMate, targetMarked, authentic,
      representativeEq, targetConsumer, targetConsumerMateNeSelected,
      sourceConsumer, targetConclusionOutside, status⟩
  have targetFrontier : directed.target ∈ component.frontier := by
    rcases parentEdge with
      ⟨_linkIndex, _kind, _storedLeft, _storedRight, _conclusion,
        _source, frontier, _notConclusion, _lookup, _premise, _outside⟩
    exact frontier
  refine ⟨path, directed, markedAge, pathStarts, finishOwned,
    directedMembership, parentEdge, targetNeSelected, targetNeMate,
    targetMarked, authentic, representativeEq, targetConsumer,
    targetConsumerMateNeSelected, sourceConsumer, targetConclusionOutside, ?_⟩
  rcases status with raw | future | marked
  · rcases raw with
      ⟨terminal, chain, terminalConsumer, mateUnmarked, mateLocation⟩
    have terminalEq := chain.terminalEqOrigin invariant componentLookup
      occurrence targetFrontier targetConsumer targetConclusionOutside
    subst terminal
    have same := connectiveBelowMateConclusionEq terminalConsumer targetConsumer
    rcases mateLocation with mateOutside | selectedReturn
    · exact Or.inl ⟨by simpa [same.1] using mateUnmarked,
        by simpa [same.1] using mateOutside⟩
    · exact False.elim
        (targetConsumerMateNeSelected (by simpa [same.1] using selectedReturn.1))
  · rcases future with
      ⟨terminal, chain, terminalConsumer, boundary, work,
        _conclusionOutside, boundaryOlder⟩
    have terminalEq := chain.terminalEqOrigin invariant componentLookup
      occurrence targetFrontier targetConsumer targetConclusionOutside
    subst terminal
    have same := connectiveBelowMateConclusionEq terminalConsumer targetConsumer
    have targetWork :
        FutureWorkAt state boundary targetConsumer.conclusion := by
      simpa [same.2] using work
    have waiting := futureWorkExactWaitingLocation invariant componentLookup
      targetFrontier (.refl directed.target) targetConsumer targetWork
      boundaryOlder
    exact Or.inr ⟨boundary, targetWork, boundaryOlder, waiting⟩
  · rcases marked with
      ⟨terminal, chain, terminalConsumer, conclusionAge, conclusionMarked,
        _conclusionGlobal, _conclusionOutside, _representativeOlder⟩
    have terminalEq := chain.terminalEqOrigin invariant componentLookup
      occurrence targetFrontier targetConsumer targetConclusionOutside
    subst terminal
    have same := connectiveBelowMateConclusionEq terminalConsumer targetConsumer
    have markedAtTargetConclusion :
        state.core.marks[targetConsumer.conclusion]? =
          some (some conclusionAge) := by
      simpa [same.2] using conclusionMarked
    exact False.elim
      (noMarkedOutsideParent invariant componentLookup occurrence targetFrontier
        targetConsumer targetConclusionOutside markedAtTargetConclusion)

end ActiveCarrierExternalReentryMarkedOuterMateSeparatedContinuationExitTarget

end SequentialFigure7
end ProofNetIR
