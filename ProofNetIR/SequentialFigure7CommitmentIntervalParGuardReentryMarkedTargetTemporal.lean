/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7CommitmentIntervalParGuardReentryMateSeparation
import ProofNetIR.SequentialFigure7ContinuationCreditPreservation

/-!
# Figure-7 marked re-entry target temporal reduction

The unique consumer of a mate-separated marked re-entry target is the exact
parent represented by the inbound edge. Its continuation is therefore raw
outside the active carrier, queued at a strictly older boundary, or marked at
a strictly older representative.

This does not eliminate the marked target or any temporal alternative, derive
a ready-tail witness or the history-tail law, or prove progress.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge

/-- A mate-separated marked re-entry target together with the exact temporal
status of its unique submitted parent. -/
def ActiveCarrierExternalReentryMarkedMateSeparatedTemporalTarget
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
          ((state.core.marks[targetConsumer.mate]? = some none ∧
              targetConsumer.mate ∉ owned) ∨
            (∃ boundary,
              FutureWorkAt state boundary targetConsumer.conclusion ∧
                boundary < input.rawAge) ∨
            ∃ conclusionAge,
              state.core.marks[targetConsumer.conclusion]? =
                  some (some conclusionAge) ∧
                state.core.representative conclusionAge < input.rawAge)

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

private theorem connectiveMateMembership
    {certificate : Certificate} {vertex : Vertex}
    (consumer : ConnectiveBelow certificate vertex) :
    consumer.mate ∈ consumer.submittedLink.premises := by
  cases kindEq : consumer.kind <;> cases sideEq : consumer.side <;>
    simp [ConnectiveBelow.mate, ConnectiveBelow.submittedLink,
      SequentialConnectiveKind.asLink, Link.premises,
      TensorPremiseSide.mate, kindEq, sideEq]

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

private theorem ReadyHeadInput.activeOwnedAccounted
    {certificate : Certificate} {state : ReservationState}
    (input : ReadyHeadInput state)
    (invariant : SchedulerInvariant certificate state)
    {component : UnificationComponent} {usedLinks owned : List Nat}
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component
        usedLinks owned) :
    Certificate.OwnedOccurrenceAccounted state.core input.rawAge component
      owned := by
  rcases input.activeComponent invariant with
    ⟨actual, _actualUsed, actualOwned, actualLookup, actualOccurrence,
      actualAccounted, _selectedOwned, _activeRoot⟩
  have actualEq : actual = component :=
    Option.some.inj
      (Option.some.inj (actualLookup.symm.trans componentLookup))
  subst actual
  have ownedEq : actualOwned = owned :=
    Certificate.OccurrenceDerivation.owned_unique invariant.structural
      actualOccurrence.derivation occurrence.derivation
  simpa [ownedEq] using actualAccounted

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
  have representativeLe := input.markedRepresentative_le_active invariant marked
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

private theorem FutureWorkAt.boundary_lt_active_of_not_owned
    {certificate : Certificate} {state : ReservationState}
    (input : ReadyHeadInput state)
    (invariant : SchedulerInvariant certificate state)
    {component : UnificationComponent} {usedLinks owned : List Nat}
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component
        usedLinks owned)
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
        have componentEq : readyComponent = component :=
          Option.some.inj
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

/-- Normalize the exact marked re-entry target through its unique parent.
The raw endpoint is outside the active carrier; queued and marked parent
conclusions are strictly older than the active boundary. -/
theorem ActiveCarrierExternalReentryMarkedMateSeparatedTarget.temporalTarget
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {usedLinks owned : List Nat}
    (invariant : SchedulerInvariant certificate state)
    (current : ConnectiveBelow certificate input.vertex)
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component
        usedLinks owned)
    (target :
      ActiveCarrierExternalReentryMarkedMateSeparatedTarget tagHistory input
        component owned current)
    (noTail :
      ¬ ∃ pending,
        pending ∈ input.readyTail ∧ pending ∉ certificate.conclusions) :
    ActiveCarrierExternalReentryMarkedMateSeparatedTemporalTarget tagHistory
      input component owned current := by
  rcases target with
    ⟨path, directed, markedAge, pathStarts, finishOwned, directedMembership,
      parentEdge, targetNeSelected, targetNeMate, targetMarked, authentic,
      representativeEq, targetConsumerMateNeSelected⟩
  rcases parentEdge with
    ⟨linkIndex, kind, storedLeft, storedRight, conclusion, sourceEq,
      targetFrontier, targetNotGlobal, linkLookup, targetPremise,
      conclusionOutside⟩
  have accounted := input.activeOwnedAccounted invariant componentLookup
    occurrence
  have credit : ContinuationCredit certificate state directed.target :=
    tagHistory.markedNonconclusionContinuation targetMarked targetNotGlobal
  have rebuiltParentEdge :
      ActiveCarrierInboundParentEdge certificate component owned directed :=
    ⟨linkIndex, kind, storedLeft, storedRight, conclusion, sourceEq,
      targetFrontier, targetNotGlobal, linkLookup, targetPremise,
      conclusionOutside⟩
  refine ⟨path, directed, markedAge, pathStarts, finishOwned,
    directedMembership, rebuiltParentEdge, targetNeSelected, targetNeMate,
    targetMarked, authentic, representativeEq, ?_⟩
  cases credit with
  | rawMate targetConsumer mateUnmarked =>
      have conclusionEq := connectiveBelow_conclusion_eq_of_parent
        invariant.structural targetConsumer linkLookup targetPremise
      have sourceConsumer : directed.source = targetConsumer.conclusion :=
        sourceEq.trans conclusionEq.symm
      have consumerConclusionOutside : targetConsumer.conclusion ∉ owned := by
        simpa [conclusionEq] using conclusionOutside
      have mateNeSelected := targetConsumerMateNeSelected targetConsumer
      have mateOutside : targetConsumer.mate ∉ owned := by
        intro mateOwned
        rcases accounted targetConsumer.mate mateOwned with
          markedCase | rawCase
        · rcases markedCase with ⟨mateAge, mateMarked, _mateRepresentative⟩
          have impossible := mateMarked.symm.trans mateUnmarked
          simp at impossible
        · have mateReady :
              targetConsumer.mate ∈ input.vertex :: input.readyTail :=
            (input.activeReadyExact invariant componentLookup
              targetConsumer.mate).mpr ⟨rawCase.2, rawCase.1⟩
          rcases List.mem_cons.mp mateReady with mateSelected | mateTail
          · exact mateNeSelected mateSelected
          · exact noTail ⟨targetConsumer.mate, mateTail,
              submittedPremise_not_conclusion invariant.structural
                targetConsumer.link_eq
                (connectiveMateMembership targetConsumer)⟩
      exact ⟨targetConsumer, mateNeSelected, sourceConsumer,
        consumerConclusionOutside, Or.inl ⟨mateUnmarked, mateOutside⟩⟩
  | futureConclusion targetConsumer boundary work =>
      have conclusionEq := connectiveBelow_conclusion_eq_of_parent
        invariant.structural targetConsumer linkLookup targetPremise
      have sourceConsumer : directed.source = targetConsumer.conclusion :=
        sourceEq.trans conclusionEq.symm
      have consumerConclusionOutside : targetConsumer.conclusion ∉ owned := by
        simpa [conclusionEq] using conclusionOutside
      have older : boundary < input.rawAge :=
        work.boundary_lt_active_of_not_owned input invariant componentLookup
          occurrence consumerConclusionOutside
      exact ⟨targetConsumer, targetConsumerMateNeSelected targetConsumer,
        sourceConsumer, consumerConclusionOutside,
        Or.inr (Or.inl ⟨boundary, work, older⟩)⟩
  | markedConclusion targetConsumer conclusionAge marked =>
      have conclusionEq := connectiveBelow_conclusion_eq_of_parent
        invariant.structural targetConsumer linkLookup targetPremise
      have sourceConsumer : directed.source = targetConsumer.conclusion :=
        sourceEq.trans conclusionEq.symm
      have consumerConclusionOutside : targetConsumer.conclusion ∉ owned := by
        simpa [conclusionEq] using conclusionOutside
      have older :
          state.core.representative conclusionAge < input.rawAge :=
        markedOutsideActiveOwned_representative_lt input invariant
          componentLookup occurrence marked consumerConclusionOutside
      exact ⟨targetConsumer, targetConsumerMateNeSelected targetConsumer,
        sourceConsumer, consumerConclusionOutside,
        Or.inr (Or.inr ⟨conclusionAge, marked, older⟩)⟩

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
      membership eventAge childLt side beforeTrace afterTrace trace status =>
      exact .olderMate offset parent child event offsetLt parentAt childAt
        notAvoiding membership eventAge childLt side beforeTrace afterTrace trace
        (mapStatus status)

end CanonicalTagHistory

/-- In the strictly older Nop branch, the mate-separated marked target has an
exact parent continuation: raw outside, queued older, or marked older. -/
theorem NopStep.commitmentInterval_parTraceReentryMarkedTemporalOutcome
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    (connected : certificate.ReferenceSwitchingConnected)
    (tagHistory : CanonicalTagHistory certificate history)
    (invariant : SchedulerInvariant certificate before)
    (step : NopStep certificate before after)
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
          before.core.marks[step.consumer.mate]? = some none ∧
          ActiveCarrierExternalReentryMarkedMateSeparatedTemporalTarget
            tagHistory step.prepared.readyHeadInput component owned
              step.consumer) := by
  apply (step.commitmentInterval_parTraceReentryMateSeparatedOutcome connected
    tagHistory invariant componentLookup occurrence positive firstAt lastAt
    noTail).mapOlderMateStatus
  intro status
  rcases status with ⟨mateOutside, mateUnmarked, target⟩
  exact ⟨mateOutside, mateUnmarked,
    ActiveCarrierExternalReentryMarkedMateSeparatedTarget.temporalTarget
      (tagHistory := tagHistory) (input := step.prepared.readyHeadInput)
      (component := component) (owned := owned) invariant step.consumer
      componentLookup occurrence target noTail⟩

/-- In the strictly older Wait branch, the mate-separated marked target has
an exact parent continuation: raw outside, queued older, or marked older. -/
theorem WaitStep.commitmentInterval_parTraceReentryMarkedTemporalOutcome
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
          ActiveCarrierExternalReentryMarkedMateSeparatedTemporalTarget
            tagHistory step.prepared.readyHeadInput component owned
              step.consumer) := by
  apply (step.commitmentInterval_parTraceReentryMateSeparatedOutcome connected
    tagHistory invariant componentLookup occurrence positive firstAt lastAt
    noTail).mapOlderMateStatus
  intro status
  rcases status with
    ⟨mateOutside, mateMarked, representativeOlder, target⟩
  exact ⟨mateOutside, mateMarked, representativeOlder,
    ActiveCarrierExternalReentryMarkedMateSeparatedTarget.temporalTarget
      (tagHistory := tagHistory) (input := step.prepared.readyHeadInput)
      (component := component) (owned := owned) invariant step.consumer
      componentLookup occurrence target noTail⟩

end SequentialFigure7
end ProofNetIR
