/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7CommitmentIntervalParGuardReentryMarkedTargetContinuationExit

/-!
# Figure-7 marked-target raw-return first descent

A nontrivial marked-conclusion chain that starts in the active occurrence
carrier and whose first parent conclusion lies outside that carrier crosses to
a strictly older representative at its first step. Canonical tag history also
authenticates that first conclusion as an executed raw-mark event.

This replaces the generic exact raw-return alternative by an explicit,
history-authenticated first-step descent. The integrated theorem applies the
reduction to the strictly older Wait branch. Unlike the typed Nop result, it
does not eliminate the return. It does not derive a ready-tail witness, the
history-tail law, completion, or progress.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerBridge

private theorem connectivePremiseMembership
    {certificate : Certificate} {vertex : Vertex}
    (consumer : ConnectiveBelow certificate vertex) :
    vertex ∈ consumer.submittedLink.premises := by
  rcases consumer with
    ⟨linkIndex, kind, storedLeft, storedRight, conclusion, side,
      consumerEq, linkEq, wellFormed, premiseEq⟩
  subst vertex
  cases kind <;> cases side <;>
    simp [ConnectiveBelow.submittedLink,
      SequentialConnectiveKind.asLink, Link.premises,
      TensorPremiseSide.premise]

private theorem connectiveBelow_conclusion_eq_of_parent
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {vertex linkIndex : Nat} {kind : SequentialConnectiveKind}
    {storedLeft storedRight conclusion : Vertex}
    (consumer : ConnectiveBelow certificate vertex)
    (lookup :
      certificate.links[linkIndex]? =
        some (kind.asLink storedLeft storedRight conclusion))
    (membership :
      vertex ∈ (kind.asLink storedLeft storedRight conclusion).premises) :
    consumer.conclusion = conclusion := by
  have sameLink :
      consumer.submittedLink =
        kind.asLink storedLeft storedRight conclusion :=
    UnificationState.StructurallyWellFormed.parentLink_unique structural
      (List.mem_of_getElem? consumer.link_eq)
      (connectivePremiseMembership consumer)
      (List.mem_of_getElem? lookup) membership
  cases consumerKind : consumer.kind <;> cases kindEq : kind <;>
    simp [ConnectiveBelow.submittedLink, SequentialConnectiveKind.asLink,
      consumerKind, kindEq] at sameLink
  · exact sameLink.2.2
  · exact sameLink.2.2

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
      Certificate.ComponentOccurrenceWitness certificate component
        usedLinks owned)
    {vertex : Vertex} {rawAge : RawTokenAge}
    (marked : state.core.marks[vertex]? = some (some rawAge))
    (notOwned : vertex ∉ owned) :
    state.core.representative rawAge < input.rawAge := by
  have representativeLe :=
    input.markedRepresentative_le_active invariant marked
  have representativeNe : state.core.representative rawAge ≠ input.rawAge := by
    intro sameRepresentative
    rcases SchedulerInvariant.exactMarkedOccurrenceOwner invariant marked with
      ⟨ownerRawAge, ownerIndex, ownerComponent, ownerUsed, ownerOwned,
        ownerMarked, ownerRepresentative, ownerLookup, ownerOccurrence,
        _ownerAccounted, ownerMembership⟩
    have ownerRawAgeEq : ownerRawAge = rawAge :=
      Option.some.inj (Option.some.inj (ownerMarked.symm.trans marked))
    subst ownerRawAge
    have ownerIndexEq : ownerIndex = input.rawAge :=
      ownerRepresentative.symm.trans sameRepresentative
    have ownerLookupAtActive :
        state.core.components[input.rawAge]? = some (some ownerComponent) := by
      simpa [ownerIndexEq] using ownerLookup
    have componentEq : ownerComponent = component :=
      Option.some.inj
        (Option.some.inj (ownerLookupAtActive.symm.trans componentLookup))
    subst ownerComponent
    have ownedEq : ownerOwned = owned :=
      Certificate.OccurrenceDerivation.owned_unique invariant.structural
        ownerOccurrence.derivation occurrence.derivation
    exact notOwned (by simpa [ownedEq] using ownerMembership)
  exact Nat.lt_of_le_of_ne representativeLe representativeNe

/-- The first step of a nontrivial marked-conclusion chain leaves the active
representative, and canonical history authenticates that older conclusion. -/
def MarkedConclusionChainFirstRepresentativeDescent
    (certificate : Certificate) (state : ReservationState)
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (origin terminal : Vertex) (active : RawTokenAge) : Prop :=
  ∃ (originAge : RawTokenAge) (consumer : ConnectiveBelow certificate origin)
      (conclusionAge : RawTokenAge),
    state.core.marks[origin]? = some (some originAge) ∧
      state.core.representative originAge = active ∧
      state.core.marks[consumer.conclusion]? = some (some conclusionAge) ∧
      tagHistory.RawMarked conclusionAge consumer.conclusion ∧
      consumer.conclusion ∉ certificate.conclusions ∧
      state.core.representative conclusionAge < active ∧
      MarkedConclusionChain certificate state consumer.conclusion terminal

/-- A marked chain whose exact first parent lies outside the active occurrence
carrier has an authenticated, strictly older first step. -/
theorem MarkedConclusionChain.firstRepresentativeDescent_of_ne
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    {origin terminal : Vertex}
    (chain : MarkedConclusionChain certificate state origin terminal)
    (different : origin ≠ terminal)
    (input : ReadyHeadInput state)
    (invariant : SchedulerInvariant certificate state)
    {component : UnificationComponent} {usedLinks owned : List Nat}
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component
        usedLinks owned)
    {originAge : RawTokenAge}
    (originMarked : state.core.marks[origin]? = some (some originAge))
    (originRepresentative :
      state.core.representative originAge = input.rawAge)
    (originConsumer : ConnectiveBelow certificate origin)
    (originConclusionOutside : originConsumer.conclusion ∉ owned) :
    MarkedConclusionChainFirstRepresentativeDescent certificate state
      tagHistory origin terminal input.rawAge := by
  cases chain with
  | refl => exact False.elim (different rfl)
  | @step vertex terminal conclusionAge consumer marked notConclusion tail =>
      have conclusionEq :
          originConsumer.conclusion = consumer.conclusion :=
        connectiveBelow_conclusion_eq_of_parent invariant.structural
          originConsumer consumer.link_eq
          (connectivePremiseMembership consumer)
      have conclusionOutside : consumer.conclusion ∉ owned := by
        rw [← conclusionEq]
        exact originConclusionOutside
      have older :
          state.core.representative conclusionAge < input.rawAge :=
        markedOutsideActiveOwned_representative_lt input invariant
          componentLookup occurrence marked conclusionOutside
      have authentic : tagHistory.RawMarked conclusionAge consumer.conclusion :=
        tagHistory.final_rawMarked_iff.mp marked
      exact ⟨originAge, consumer, conclusionAge, originMarked,
        originRepresentative, marked, authentic, notConclusion, older, tail⟩

/-- The marked re-entry target after replacing exact raw return by an
authenticated first-step descent to a strictly older representative. -/
def ActiveCarrierExternalReentryMarkedMateSeparatedContinuationFirstDescentTarget
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (input : ReadyHeadInput state) (component : UnificationComponent)
    (owned : List Vertex)
    (current : ConnectiveBelow certificate input.vertex) : Prop :=
  ∃ (path : certificate.referenceSwitchingGraph.EdgeSimplePath)
      (directed : certificate.referenceSwitchingGraph.DirectedEdge)
      (markedAge : RawTokenAge),
    path.start = current.mate ∧
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
        ((∃ terminal,
            MarkedConclusionChain certificate state directed.target terminal ∧
            ∃ terminalConsumer : ConnectiveBelow certificate terminal,
              state.core.marks[terminalConsumer.mate]? = some none ∧
              terminalConsumer.mate ∉ owned) ∨
          MarkedConclusionChainFirstRepresentativeDescent certificate state
            tagHistory directed.target current.mate input.rawAge ∨
          (∃ terminal,
            MarkedConclusionChain certificate state directed.target terminal ∧
            ∃ terminalConsumer : ConnectiveBelow certificate terminal,
              ∃ boundary,
                FutureWorkAt state boundary terminalConsumer.conclusion ∧
                terminalConsumer.conclusion ∉ owned ∧
                boundary < input.rawAge) ∨
          ∃ terminal,
            MarkedConclusionChain certificate state directed.target terminal ∧
            ∃ terminalConsumer : ConnectiveBelow certificate terminal,
              ∃ conclusionAge,
                state.core.marks[terminalConsumer.conclusion]? =
                  some (some conclusionAge) ∧
                terminalConsumer.conclusion ∈ certificate.conclusions ∧
                terminalConsumer.conclusion ∉ owned ∧
                state.core.representative conclusionAge < input.rawAge)

namespace ActiveCarrierExternalReentryMarkedMateSeparatedContinuationExitTarget

/-- Refine the generic finite continuation target by exposing the first
representative descent in its exact raw-return branch. -/
theorem firstDescentTarget
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    (input : ReadyHeadInput state)
    (invariant : SchedulerInvariant certificate state)
    {component : UnificationComponent} {usedLinks owned : List Nat}
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component
        usedLinks owned)
    (current : ConnectiveBelow certificate input.vertex)
    (target :
      ActiveCarrierExternalReentryMarkedMateSeparatedContinuationExitTarget
        tagHistory input component owned current) :
    ActiveCarrierExternalReentryMarkedMateSeparatedContinuationFirstDescentTarget
      tagHistory input component owned current := by
  rcases target with
    ⟨path, directed, markedAge, pathStart, finishOwned, directedMembership,
      parentEdge, targetNeSelected, targetNeMate, targetMarked, authentic,
      representativeEq, targetConsumer, targetConsumerMateNeSelected,
      sourceConsumer, targetConclusionOutside, status⟩
  refine ⟨path, directed, markedAge, pathStart, finishOwned,
    directedMembership, parentEdge, targetNeSelected, targetNeMate,
    targetMarked, authentic, representativeEq, targetConsumer,
    targetConsumerMateNeSelected, sourceConsumer, targetConclusionOutside, ?_⟩
  rcases status with raw | future | marked
  · rcases raw with
      ⟨terminal, chain, terminalConsumer, mateUnmarked,
        mateOutside | exactReturn⟩
    · exact Or.inl ⟨terminal, chain, terminalConsumer, mateUnmarked,
        mateOutside⟩
    · rcases exactReturn with
        ⟨_mateSelected, terminalEq, _conclusionEq, _complexityLt⟩
      subst terminal
      have descent :
          MarkedConclusionChainFirstRepresentativeDescent certificate state
            tagHistory directed.target current.mate input.rawAge :=
        chain.firstRepresentativeDescent_of_ne tagHistory targetNeMate input
          invariant componentLookup occurrence targetMarked representativeEq
          targetConsumer targetConclusionOutside
      exact Or.inr (Or.inl descent)
  · exact Or.inr (Or.inr (Or.inl future))
  · exact Or.inr (Or.inr (Or.inr marked))

end ActiveCarrierExternalReentryMarkedMateSeparatedContinuationExitTarget

namespace CanonicalTagHistory

private theorem CommitmentIntervalParTraceOutcome.mapOlderMateStatus
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state}
    {consumer : ConnectiveBelow certificate input.vertex}
    {position edgeCount : Nat} {first : RawTokenAge}
    {beforeStatus afterStatus : Prop}
    (outcome : tagHistory.CommitmentIntervalParTraceOutcome input consumer
      position edgeCount first beforeStatus)
    (mapStatus : beforeStatus → afterStatus) :
    tagHistory.CommitmentIntervalParTraceOutcome input consumer position
      edgeCount first afterStatus := by
  cases outcome with
  | avoiding path => exact .avoiding path
  | equalSelected offset parent child event offsetLt parentAt childAt
      notAvoiding membership eventAge childEq side beforeTrace afterTrace trace =>
      exact .equalSelected offset parent child event offsetLt parentAt childAt
        notAvoiding membership eventAge childEq side beforeTrace afterTrace trace
  | equalMate offset parent child event offsetLt parentAt childAt notAvoiding
      membership eventAge childEq side beforeTrace afterTrace trace =>
      exact .equalMate offset parent child event offsetLt parentAt childAt
        notAvoiding membership eventAge childEq side beforeTrace afterTrace trace
  | olderMate offset parent child event offsetLt parentAt childAt notAvoiding
      membership eventAge childEq side beforeTrace afterTrace trace status =>
      exact .olderMate offset parent child event offsetLt parentAt childAt
        notAvoiding membership eventAge childEq side beforeTrace afterTrace trace
        (mapStatus status)

end CanonicalTagHistory

/-- In the strictly older Wait branch, expose an authenticated first-step
representative descent whenever the finite continuation returns exactly. -/
theorem WaitStep.commitmentInterval_parTraceReentryMarkedContinuationFirstDescentOutcome
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    (connected : certificate.ReferenceSwitchingConnected)
    (tagHistory : CanonicalTagHistory certificate history)
    (invariant : SchedulerInvariant certificate before)
    (step : WaitStep certificate before after)
    {component : UnificationComponent} {usedLinks owned : List Nat}
    (componentLookup :
      before.core.components[step.prepared.stackResult.rawAge]? =
        some (some component))
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component
        usedLinks owned)
    {position edgeCount : Nat} {first : RawTokenAge}
    (positive : 0 < edgeCount)
    (firstAt : before.stack.sigma[position]? = some first)
    (lastAt :
      before.stack.sigma[position + edgeCount]? =
        some step.prepared.stackResult.rawAge)
    (noTail :
      ¬ ∃ pending,
        pending ∈ step.prepared.stackResult.remainingTop ∧
          pending ∉ certificate.conclusions) :
    tagHistory.CommitmentIntervalParTraceOutcome
      step.prepared.readyHeadInput step.consumer position edgeCount first
        (step.consumer.mate ∉ owned ∧
          before.core.marks[step.consumer.mate]? =
            some (some step.mateRawAge) ∧
          before.core.representative step.mateRawAge <
            step.prepared.stackResult.rawAge ∧
          ActiveCarrierExternalReentryMarkedMateSeparatedContinuationFirstDescentTarget
            tagHistory step.prepared.readyHeadInput component owned
              step.consumer) := by
  apply
    (step.commitmentInterval_parTraceReentryMarkedContinuationExitOutcome
      connected tagHistory invariant componentLookup occurrence positive firstAt
      lastAt noTail).mapOlderMateStatus
  intro status
  rcases status with ⟨mateOutside, mateMarked, representativeOlder, target⟩
  exact ⟨mateOutside, mateMarked, representativeOlder,
    target.firstDescentTarget step.prepared.readyHeadInput invariant
      componentLookup occurrence step.consumer⟩

end SequentialFigure7
end ProofNetIR
