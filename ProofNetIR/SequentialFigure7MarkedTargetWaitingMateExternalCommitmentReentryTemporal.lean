/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7MarkedTargetWaitingMateExternalCommitmentReentryMarked

/-!
# Figure-7 waiting-mate commitment re-entry temporal normalization

Each marked re-entry retained below an active waiting mate starts at that
waiting consumer's external conclusion rather than at the enclosing current
mate. Frontier ownership still separates its target from the enclosing mate.
Structural parent uniqueness then identifies the target's exact submitted
parent, whose continuation is raw outside the active carrier, queued at a
strictly older boundary, or marked at a strictly older representative.

This module transports that endpoint-parametric temporal normalization through
the active waiting endpoint, future-work mate, continuation sibling exit, and
typed Wait commitment-interval trace. All unrelated raw, future, marked,
causal, cyclic, avoiding, and equal-final branches are preserved.

The result does not eliminate the marked target or any surviving temporal
alternative, recover a ready-tail payer, identify arbitrary crossing and
re-entry witnesses, derive the history-tail law, or establish progress,
completion, termination, or totality.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge

/-- An endpoint-parametric marked re-entry target, separated from the
enclosing current mate, together with the exact temporal status of its unique
submitted parent. -/
def ActiveCarrierExternalReentryMarkedOuterMateSeparatedTemporalTarget
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

/-- Normalize an arbitrary-endpoint marked re-entry target through its unique
parent while separating it from the enclosing current mate. -/
theorem ActiveCarrierExternalReentryMarkedHistoricalTarget.outerMateSeparatedTemporalTarget
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {usedLinks owned : List Nat} {endpoint : Vertex}
    (invariant : SchedulerInvariant certificate state)
    (current : ConnectiveBelow certificate input.vertex)
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component
        usedLinks owned)
    (mateOutside : current.mate ∉ owned)
    (target :
      ActiveCarrierExternalReentryMarkedHistoricalTarget tagHistory input
        component owned endpoint)
    (noTail :
      ¬ ∃ pending,
        pending ∈ input.readyTail ∧ pending ∉ certificate.conclusions) :
    ActiveCarrierExternalReentryMarkedOuterMateSeparatedTemporalTarget
      tagHistory input component owned endpoint current := by
  rcases target with
    ⟨path, directed, markedAge, pathStarts, finishOwned, directedMembership,
      parentEdge, targetNeSelected, targetMarked, authentic,
      representativeEq⟩
  rcases parentEdge with
    ⟨linkIndex, kind, storedLeft, storedRight, conclusion, sourceEq,
      targetFrontier, targetNotGlobal, linkLookup, targetPremise,
      conclusionOutside⟩
  have targetOwned : directed.target ∈ owned :=
    occurrence.derivation.frontier_subset_owned directed.target targetFrontier
  have targetNeMate : directed.target ≠ current.mate := by
    intro same
    exact mateOutside (by simpa [same] using targetOwned)
  have targetConsumerMateNeSelected :
      ∀ targetConsumer : ConnectiveBelow certificate directed.target,
        targetConsumer.mate ≠ input.vertex := by
    intro targetConsumer same
    have currentMateEq : current.mate = directed.target :=
      connectiveBelow_mate_eq_of_mate_eq invariant.structural targetConsumer
        current same
    exact targetNeMate currentMateEq.symm
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
      have consumerMateOutside : targetConsumer.mate ∉ owned := by
        intro mateOwned
        rcases accounted targetConsumer.mate mateOwned with
          markedCase | rawCase
        · rcases markedCase with
            ⟨mateAge, mateMarked, _mateRepresentative⟩
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
        consumerConclusionOutside,
        Or.inl ⟨mateUnmarked, consumerMateOutside⟩⟩
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

/-- The exact two-case waiting-parent endpoint with its marked re-entry target
normalized through the unique parent relative to the enclosing current mate. -/
inductive ActiveMateWaitingParentExternalCommitmentReentryTemporalOutcome
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (input : ReadyHeadInput state) (component : UnificationComponent)
    (owned : List Vertex) (current : ConnectiveBelow certificate input.vertex)
    {terminal : Vertex} (consumer : ConnectiveBelow certificate terminal) : Prop where
  | olderFuture
      (boundary : RawTokenAge)
      (work : FutureWorkAt state boundary consumer.conclusion)
      (older : boundary < input.rawAge)
      (outside : consumer.conclusion ∉ owned)
      (commitmentSplit :
        tagHistory.StrictOlderCommitmentSplit boundary input.rawAge)
      (crossing :
        ActiveCarrierExternalEndpointCrossing certificate owned
          consumer.conclusion)
      (reentry :
        ActiveCarrierExternalEndpointReentry certificate owned
          consumer.conclusion)
      (temporalTarget :
        ActiveCarrierExternalReentryMarkedOuterMateSeparatedTemporalTarget
          tagHistory input component owned consumer.conclusion current) :
      ActiveMateWaitingParentExternalCommitmentReentryTemporalOutcome
        tagHistory input component owned current consumer
  | olderMarked
      (conclusionAge : RawTokenAge)
      (marked :
        state.core.marks[consumer.conclusion]? = some (some conclusionAge))
      (olderRepresentative :
        state.core.representative conclusionAge < input.rawAge)
      (outside : consumer.conclusion ∉ owned)
      (commitmentSplit : tagHistory.StrictOlderCommitmentSplit
        (state.core.representative conclusionAge) input.rawAge)
      (crossing :
        ActiveCarrierExternalEndpointCrossing certificate owned
          consumer.conclusion)
      (reentry :
        ActiveCarrierExternalEndpointReentry certificate owned
          consumer.conclusion)
      (temporalTarget :
        ActiveCarrierExternalReentryMarkedOuterMateSeparatedTemporalTarget
          tagHistory input component owned consumer.conclusion current) :
      ActiveMateWaitingParentExternalCommitmentReentryTemporalOutcome
        tagHistory input component owned current consumer

namespace ActiveMateWaitingParentExternalCommitmentReentryMarkedOutcome

/-- Normalize either marked waiting endpoint through its unique parent using
the enclosing current mate's external-carrier receipt. -/
theorem temporalOutcome
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {usedLinks owned : List Nat}
    {terminal : Vertex} {consumer : ConnectiveBelow certificate terminal}
    (outcome :
      ActiveMateWaitingParentExternalCommitmentReentryMarkedOutcome tagHistory
        input component owned consumer)
    (invariant : SchedulerInvariant certificate state)
    (current : ConnectiveBelow certificate input.vertex)
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component
        usedLinks owned)
    (mateOutside : current.mate ∉ owned)
    (noTail :
      ¬ ∃ pending,
        pending ∈ input.readyTail ∧ pending ∉ certificate.conclusions) :
    ActiveMateWaitingParentExternalCommitmentReentryTemporalOutcome tagHistory
      input component owned current consumer := by
  cases outcome with
  | olderFuture boundary work older outside commitmentSplit crossing reentry
      target =>
      exact .olderFuture boundary work older outside commitmentSplit crossing
        reentry
        (target.outerMateSeparatedTemporalTarget invariant current
          componentLookup occurrence mateOutside noTail)
  | olderMarked conclusionAge marked olderRepresentative outside
      commitmentSplit crossing reentry target =>
      exact .olderMarked conclusionAge marked olderRepresentative outside
        commitmentSplit crossing reentry
        (target.outerMateSeparatedTemporalTarget invariant current
          componentLookup occurrence mateOutside noTail)

end ActiveMateWaitingParentExternalCommitmentReentryMarkedOutcome

/-- The future-work mate split with an unchanged older-outside branch and an
active-owned branch whose waiting endpoint has an exact older temporal parent. -/
inductive FutureWorkMateActiveCarrierExternalCommitmentReentryTemporalStatus
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (input : ReadyHeadInput state) (component : UnificationComponent)
    (owned : List Vertex) (current : ConnectiveBelow certificate input.vertex)
    (terminal : Vertex) (consumer : ConnectiveBelow certificate terminal)
    (boundary mateAge : RawTokenAge) : Prop where
  | olderOutside
      (notMembership : consumer.mate ∉ owned)
      (representativeOlder :
        state.core.representative mateAge < input.rawAge) :
      FutureWorkMateActiveCarrierExternalCommitmentReentryTemporalStatus
        tagHistory input component owned current terminal consumer boundary
          mateAge
  | activeExternal
      (membership : consumer.mate ∈ owned)
      (representative :
        state.core.representative mateAge = input.rawAge)
      (waiting :
        FutureWorkActiveMateWaitingOutcome certificate state input terminal
          consumer boundary)
      (external :
        ActiveMateWaitingParentExternalCommitmentReentryTemporalOutcome
          tagHistory input component owned current consumer) :
      FutureWorkMateActiveCarrierExternalCommitmentReentryTemporalStatus
        tagHistory input component owned current terminal consumer boundary
          mateAge

namespace FutureWorkMateActiveCarrierExternalCommitmentReentryMarkedStatus

/-- Normalize the active-owned waiting endpoint of the marked future-work mate
status while preserving its older-outside branch verbatim. -/
theorem temporalStatus
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {usedLinks owned : List Nat}
    {terminal : Vertex} {consumer : ConnectiveBelow certificate terminal}
    {boundary mateAge : RawTokenAge}
    (status :
      FutureWorkMateActiveCarrierExternalCommitmentReentryMarkedStatus tagHistory
        input component owned terminal consumer boundary mateAge)
    (invariant : SchedulerInvariant certificate state)
    (current : ConnectiveBelow certificate input.vertex)
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component
        usedLinks owned)
    (mateOutside : current.mate ∉ owned)
    (noTail :
      ¬ ∃ pending,
        pending ∈ input.readyTail ∧ pending ∉ certificate.conclusions) :
    FutureWorkMateActiveCarrierExternalCommitmentReentryTemporalStatus
      tagHistory input component owned current terminal consumer boundary
        mateAge := by
  cases status with
  | olderOutside notMembership representativeOlder =>
      exact .olderOutside notMembership representativeOlder
  | activeExternal membership representative waiting external =>
      exact .activeExternal membership representative waiting
        (external.temporalOutcome invariant current componentLookup occurrence
          mateOutside noTail)

end FutureWorkMateActiveCarrierExternalCommitmentReentryMarkedStatus

/-- A continuation exit that preserves both raw exits and refines only the
future-work mate status to its exact temporal-parent form. -/
inductive ContinuationExitRawOrFutureActiveCarrierExternalCommitmentReentryTemporalOutcome
    (certificate : Certificate) (state : ReservationState)
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (input : ReadyHeadInput state) (component : UnificationComponent)
    (owned : List Vertex) (current : ConnectiveBelow certificate input.vertex)
    (origin : Vertex) : Prop where
  | rawOutside {terminal : Vertex}
      (chain : MarkedConclusionChain certificate state origin terminal)
      (terminalOutside : terminal ∉ owned)
      (consumer : ConnectiveBelow certificate terminal)
      (mateUnmarked : state.core.marks[consumer.mate]? = some none)
      (mateOutside : consumer.mate ∉ owned) :
      ContinuationExitRawOrFutureActiveCarrierExternalCommitmentReentryTemporalOutcome
        certificate state tagHistory input component owned current origin
  | rawSelectedReturn {terminal : Vertex}
      (chain : MarkedConclusionChain certificate state origin terminal)
      (terminalOutside : terminal ∉ owned)
      (consumer : ConnectiveBelow certificate terminal)
      (mateUnmarked : state.core.marks[consumer.mate]? = some none)
      (mateSelected : consumer.mate = input.vertex)
      (terminalCurrentMate : terminal = current.mate)
      (conclusionCurrent : consumer.conclusion = current.conclusion) :
      ContinuationExitRawOrFutureActiveCarrierExternalCommitmentReentryTemporalOutcome
        certificate state tagHistory input component owned current origin
  | futureOlder {terminal : Vertex}
      (chain : MarkedConclusionChain certificate state origin terminal)
      (terminalOutside : terminal ∉ owned)
      (consumer : ConnectiveBelow certificate terminal)
      (boundary : RawTokenAge)
      (work : FutureWorkAt state boundary consumer.conclusion)
      (conclusionOutside : consumer.conclusion ∉ owned)
      (boundaryOlder : boundary < input.rawAge)
      (terminalAge mateAge : RawTokenAge)
      (terminalMarked : state.core.marks[terminal]? = some (some terminalAge))
      (mateMarked :
        state.core.marks[consumer.mate]? = some (some mateAge))
      (terminalEvent : tagHistory.RawMarked terminalAge terminal)
      (mateEvent : tagHistory.RawMarked mateAge consumer.mate)
      (terminalRepresentativeOlder :
        state.core.representative terminalAge < input.rawAge)
      (mateStatus :
        FutureWorkMateActiveCarrierExternalCommitmentReentryTemporalStatus
          tagHistory input component owned current terminal consumer boundary
            mateAge)
      (premiseOrder :
        tagHistory.RawMarkedBefore terminalAge terminal mateAge consumer.mate ∨
          tagHistory.RawMarkedBefore mateAge consumer.mate terminalAge terminal)
      (location :
        FutureWorkAtExactSchedulerLocation certificate state boundary
          consumer.conclusion) :
      ContinuationExitRawOrFutureActiveCarrierExternalCommitmentReentryTemporalOutcome
        certificate state tagHistory input component owned current origin

namespace
  ContinuationExitRawOrFutureActiveCarrierExternalCommitmentReentryMarkedOutcome

/-- Normalize only the future-work branch of a marked continuation outcome;
preserve both raw exits and every existing chain, event, order, and location
receipt. -/
theorem temporalOutcome
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {usedLinks owned : List Nat}
    {current : ConnectiveBelow certificate input.vertex} {origin : Vertex}
    (outcome :
      ContinuationExitRawOrFutureActiveCarrierExternalCommitmentReentryMarkedOutcome
        certificate state tagHistory input component owned current origin)
    (invariant : SchedulerInvariant certificate state)
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component
        usedLinks owned)
    (mateOutside : current.mate ∉ owned)
    (noTail :
      ¬ ∃ pending,
        pending ∈ input.readyTail ∧ pending ∉ certificate.conclusions) :
    ContinuationExitRawOrFutureActiveCarrierExternalCommitmentReentryTemporalOutcome
      certificate state tagHistory input component owned current origin := by
  cases outcome with
  | rawOutside chain terminalOutside consumer mateUnmarked consumerMateOutside =>
      exact .rawOutside chain terminalOutside consumer mateUnmarked
        consumerMateOutside
  | rawSelectedReturn chain terminalOutside consumer mateUnmarked mateSelected
      terminalCurrentMate conclusionCurrent =>
      exact .rawSelectedReturn chain terminalOutside consumer mateUnmarked
        mateSelected terminalCurrentMate conclusionCurrent
  | futureOlder chain terminalOutside consumer boundary work conclusionOutside
      boundaryOlder terminalAge mateAge terminalMarked mateMarked terminalEvent
      mateEvent terminalRepresentativeOlder mateStatus premiseOrder location =>
      exact .futureOlder chain terminalOutside consumer boundary work
        conclusionOutside boundaryOlder terminalAge mateAge terminalMarked
        mateMarked terminalEvent mateEvent terminalRepresentativeOlder
        (mateStatus.temporalStatus invariant current componentLookup occurrence
          mateOutside noTail)
        premiseOrder location

end
  ContinuationExitRawOrFutureActiveCarrierExternalCommitmentReentryMarkedOutcome

/-- The stored-right waiting sibling-exit target with every nested active
waiting re-entry normalized through its exact older temporal parent. -/
def ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitWaitingTemporalTarget
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (input : ReadyHeadInput state) (component : UnificationComponent)
    (owned : List Vertex) (current : ConnectiveBelow certificate input.vertex) :
    Prop :=
  ∃ (outerAge : RawTokenAge),
    tagHistory.RawMarked outerAge current.mate ∧
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
                MarkedConclusionChain certificate state directed.target
                    terminal ∧
                  ∃ terminalConsumer : ConnectiveBelow certificate terminal,
                    state.core.marks[terminalConsumer.mate]? = some none ∧
                    terminalConsumer.mate ∉ owned) ∨
              (MarkedConclusionChainFirstCausalDescent certificate state
                  tagHistory directed.target current.mate input.rawAge ∧
                ∃ (consumer : ConnectiveBelow certificate directed.target)
                    (mateAge : RawTokenAge),
                  tagHistory.RawMarkedBefore mateAge consumer.mate outerAge
                      current.mate ∧
                    ContinuationExitRawOrFutureActiveCarrierExternalCommitmentReentryTemporalOutcome
                        certificate state tagHistory input component owned current
                          consumer.conclusion ∧
                      MarkedConclusionRawReturnCyclicJunctionCausalOutcome
                        certificate state tagHistory current.mate
                          consumer.conclusion outerAge) ∨
              (∃ terminal,
                MarkedConclusionChain certificate state directed.target
                    terminal ∧
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

namespace
  ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitWaitingMarkedTarget

/-- Normalize only the causal continuation branch of the waiting marked target;
preserve its outer marked target, raw/future/marked sibling exits, and causal
and cyclic-junction receipts verbatim. -/
theorem temporalTarget
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {usedLinks owned : List Nat}
    {current : ConnectiveBelow certificate input.vertex}
    (target :
      ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitWaitingMarkedTarget
        tagHistory input component owned current)
    (invariant : SchedulerInvariant certificate state)
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component
        usedLinks owned)
    (mateOutside : current.mate ∉ owned)
    (noTail :
      ¬ ∃ pending,
        pending ∈ input.readyTail ∧ pending ∉ certificate.conclusions) :
    ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitWaitingTemporalTarget
      tagHistory input component owned current := by
  rcases target with
    ⟨outerAge, outerEvent, path, directed, markedAge, pathStart, pathFinish,
      directedMembership, inbound, targetNeSelected, targetNeMate, targetMarked,
      targetEvent, targetRepresentative, targetConsumer, targetMateNeSelected,
      directedSource, conclusionOutside, exit⟩
  refine ⟨outerAge, outerEvent, path, directed, markedAge, pathStart, pathFinish,
    directedMembership, inbound, targetNeSelected, targetNeMate, targetMarked,
    targetEvent, targetRepresentative, targetConsumer, targetMateNeSelected,
    directedSource, conclusionOutside, ?_⟩
  rcases exit with raw | causal | future | marked
  · exact Or.inl raw
  · rcases causal with
      ⟨descent, consumer, mateAge, mateBeforeOuter, siblingOutcome,
        causalOutcome⟩
    exact Or.inr (Or.inl ⟨descent, consumer, mateAge, mateBeforeOuter,
      siblingOutcome.temporalOutcome invariant componentLookup occurrence
        mateOutside noTail,
      causalOutcome⟩)
  · exact Or.inr (Or.inr (Or.inl future))
  · exact Or.inr (Or.inr (Or.inr marked))

end
  ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitWaitingMarkedTarget

namespace CanonicalTagHistory

private theorem CommitmentIntervalParTraceOutcome.mapWaitingTemporalStatus
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

namespace WaitStep

/-- Lift endpoint-parametric temporal normalization to the older-mate status of
the typed Wait commitment-interval trace, leaving every other branch
unchanged. -/
theorem commitmentInterval_parTraceReentryMarkedContinuationSiblingExitWaitingTemporalOutcome
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    (correct : certificate.DeclarativelyCorrect)
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
        ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitWaitingTemporalTarget
            tagHistory step.prepared.readyHeadInput component owned
              step.consumer) := by
  apply
    CanonicalTagHistory.CommitmentIntervalParTraceOutcome.mapWaitingTemporalStatus
      (step.commitmentInterval_parTraceReentryMarkedContinuationSiblingExitWaitingMarkedOutcome
        correct connected tagHistory invariant componentLookup occurrence
          positive firstAt lastAt noTail)
  intro status
  rcases status with ⟨mateOutside, mateMarked, representativeOlder, target⟩
  exact ⟨mateOutside, mateMarked, representativeOlder,
    target.temporalTarget invariant componentLookup occurrence mateOutside
      noTail⟩

end WaitStep

end SequentialFigure7
end ProofNetIR
