/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7MarkedTargetRawReturnSiblingExitReadyMateElimination
import ProofNetIR.SequentialFigure7ActiveTopDebtParentExternalTemporalOutcome

/-!
# Figure-7 active-mate waiting external temporal outcome

Eliminates the internal raw-return alternative from an active-owned exact
waiting mate. The waiting span already marks both premises of its par producer.
Continuation credit for the active mate therefore cannot return raw to the
older terminal: that would make the same terminal both concrete-marked and
raw-unmarked. Every surviving continuation reaches the submitted conclusion,
which is outside the active carrier, as strictly older future work or a
strictly older concrete mark.

The result strengthens the ready-mate sibling exit and the corresponding typed
Wait trace target. It does not eliminate the older-outside mate case, discharge
the resulting external temporal endpoints, recover a ready-tail payer, derive
the history-tail law, or establish completion or progress.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge
open Certificate.OccurrenceDerivation

private theorem connectiveMateMembership
    {certificate : Certificate} {vertex : Vertex}
    (consumer : ConnectiveBelow certificate vertex) :
    consumer.mate ∈ consumer.submittedLink.premises := by
  cases kindEq : consumer.kind <;> cases sideEq : consumer.side <;>
    simp [ConnectiveBelow.mate, ConnectiveBelow.submittedLink,
      SequentialConnectiveKind.asLink, Link.premises,
      TensorPremiseSide.mate, kindEq, sideEq]

private theorem connectiveBelow_opposite_of_mate_eq
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {leftVertex rightVertex : Vertex}
    (left : ConnectiveBelow certificate leftVertex)
    (right : ConnectiveBelow certificate rightVertex)
    (leftMate : left.mate = rightVertex) :
    right.mate = leftVertex ∧ right.conclusion = left.conclusion := by
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
      certificate.ComponentOccurrenceWitness component usedLinks owned)
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
        ownerAccounted, ownerMembership⟩
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
      certificate.ComponentOccurrenceWitness component usedLinks owned)
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

/-- The two strictly older endpoints left after an active waiting mate cannot
return raw to its marked terminal. Both endpoints are the submitted
conclusion. -/
inductive ActiveMateWaitingParentExternalTemporalOutcome
    (certificate : Certificate) (state : ReservationState)
    (input : ReadyHeadInput state) (owned : List Vertex)
    {terminal : Vertex} (consumer : ConnectiveBelow certificate terminal) :
    Prop where
  | olderFuture
      (boundary : RawTokenAge)
      (work : FutureWorkAt state boundary consumer.conclusion)
      (older : boundary < input.rawAge)
      (outside : consumer.conclusion ∉ owned) :
      ActiveMateWaitingParentExternalTemporalOutcome certificate state input
        owned consumer
  | olderMarked
      (conclusionAge : RawTokenAge)
      (marked :
        state.core.marks[consumer.conclusion]? = some (some conclusionAge))
      (olderRepresentative :
        state.core.representative conclusionAge < input.rawAge)
      (outside : consumer.conclusion ∉ owned) :
      ActiveMateWaitingParentExternalTemporalOutcome certificate state input
        owned consumer

namespace ActiveMateWaitingParentExternalTemporalOutcome

/-- Forget the exact waiting-mate endpoint and reuse the active-carrier
external temporal interface. -/
theorem activeCarrierOutcome
    {certificate : Certificate} {state : ReservationState}
    {input : ReadyHeadInput state} {owned : List Vertex}
    {terminal : Vertex} {consumer : ConnectiveBelow certificate terminal}
    (outcome : ActiveMateWaitingParentExternalTemporalOutcome certificate state
      input owned consumer) :
    ActiveCarrierParentExternalTemporalOutcome certificate state input.rawAge
      owned := by
  cases outcome with
  | olderFuture boundary work older outside =>
      exact .olderFuture consumer.conclusion boundary work older outside
  | olderMarked conclusionAge marked olderRepresentative outside =>
      exact .olderMarked consumer.conclusion conclusionAge marked
        olderRepresentative outside

end ActiveMateWaitingParentExternalTemporalOutcome

/-- An active-owned exact waiting mate cannot return raw to its concrete-marked
older terminal. Its continuation reaches the outside submitted conclusion as
strictly older future work or a strictly older concrete mark. -/
theorem FutureWorkActiveMateWaitingOutcome.parentExternalTemporalOutcome
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {usedLinks owned : List Nat}
    (invariant : SchedulerInvariant certificate state)
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      certificate.ComponentOccurrenceWitness component usedLinks owned)
    {terminal : Vertex} {consumer : ConnectiveBelow certificate terminal}
    {boundary : RawTokenAge}
    (conclusionOutside : consumer.conclusion ∉ owned)
    (waiting :
      FutureWorkActiveMateWaitingOutcome certificate state input terminal
        consumer boundary) :
    ActiveMateWaitingParentExternalTemporalOutcome certificate state input
      owned consumer := by
  cases waiting with
  | @waitingReturn payload linkIndex left right olderPremise youngerPremise
      olderAge youngerAge waitingAt member linkLookup sourceLookup unmarked
      olderMarked youngerMarked olderBoundary boundaryOlder terminalOlder
      mateYounger youngerBoundaryActive =>
      have mateMarked :
          state.core.marks[consumer.mate]? = some (some youngerAge) := by
        simpa [mateYounger] using youngerMarked
      have mateNotGlobal : consumer.mate ∉ certificate.conclusions :=
        submittedPremise_not_conclusion invariant.structural consumer.link_eq
          (connectiveMateMembership consumer)
      have credit : ContinuationCredit certificate state consumer.mate :=
        tagHistory.markedNonconclusionContinuation mateMarked mateNotGlobal
      cases credit with
      | rawMate inner mateUnmarked =>
          have opposite := connectiveBelow_opposite_of_mate_eq
            invariant.structural consumer inner rfl
          have terminalMarked :
              state.core.marks[terminal]? = some (some olderAge) := by
            simpa [terminalOlder] using olderMarked
          have terminalUnmarked : state.core.marks[terminal]? = some none := by
            rw [← opposite.1]
            exact mateUnmarked
          rw [terminalMarked] at terminalUnmarked
          simp at terminalUnmarked
      | futureConclusion inner parentBoundary work =>
          have opposite := connectiveBelow_opposite_of_mate_eq
            invariant.structural consumer inner rfl
          have workAtConclusion :
              FutureWorkAt state parentBoundary consumer.conclusion := by
            rw [← opposite.2]
            exact work
          have older : parentBoundary < input.rawAge :=
            workAtConclusion.boundary_lt_active_of_not_owned input invariant
              componentLookup occurrence conclusionOutside
          exact .olderFuture parentBoundary workAtConclusion older
            conclusionOutside
      | markedConclusion inner conclusionAge marked =>
          have opposite := connectiveBelow_opposite_of_mate_eq
            invariant.structural consumer inner rfl
          have markedAtConclusion :
              state.core.marks[consumer.conclusion]? =
                some (some conclusionAge) := by
            rw [← opposite.2]
            exact marked
          have older :
              state.core.representative conclusionAge < input.rawAge :=
            markedOutsideActiveOwned_representative_lt input invariant
              componentLookup occurrence markedAtConclusion conclusionOutside
          exact .olderMarked conclusionAge markedAtConclusion older
            conclusionOutside

/-- Ready-eliminated future-mate status with every active waiting branch
normalized to an external temporal parent endpoint. -/
inductive FutureWorkMateActiveCarrierExternalTemporalStatus
    (certificate : Certificate) (state : ReservationState)
    (input : ReadyHeadInput state) (owned : List Vertex)
    (terminal : Vertex) (consumer : ConnectiveBelow certificate terminal)
    (boundary mateAge : RawTokenAge) : Prop where
  | olderOutside
      (notMembership : consumer.mate ∉ owned)
      (representativeOlder :
        state.core.representative mateAge < input.rawAge) :
      FutureWorkMateActiveCarrierExternalTemporalStatus certificate state input
        owned terminal consumer boundary mateAge
  | activeExternal
      (membership : consumer.mate ∈ owned)
      (representative :
        state.core.representative mateAge = input.rawAge)
      (waiting :
        FutureWorkActiveMateWaitingOutcome certificate state input terminal
          consumer boundary)
      (external :
        ActiveMateWaitingParentExternalTemporalOutcome certificate state input
          owned consumer) :
      FutureWorkMateActiveCarrierExternalTemporalStatus certificate state input
        owned terminal consumer boundary mateAge

/-- Refine ready-mate elimination by sending its active waiting branch directly
to the external parent temporal interface. -/
theorem FutureWorkMateActiveCarrierReadyEliminatedStatus.externalTemporalStatus
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {usedLinks owned : List Nat}
    (invariant : SchedulerInvariant certificate state)
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      certificate.ComponentOccurrenceWitness component usedLinks owned)
    {terminal : Vertex} {consumer : ConnectiveBelow certificate terminal}
    {boundary mateAge : RawTokenAge}
    (conclusionOutside : consumer.conclusion ∉ owned)
    (status :
      FutureWorkMateActiveCarrierReadyEliminatedStatus certificate state input
        owned terminal consumer boundary mateAge) :
    FutureWorkMateActiveCarrierExternalTemporalStatus certificate state input
      owned terminal consumer boundary mateAge := by
  cases status with
  | olderOutside notMembership representativeOlder =>
      exact .olderOutside notMembership representativeOlder
  | activeWaiting membership representative waiting =>
      exact .activeExternal membership representative waiting
        (waiting.parentExternalTemporalOutcome tagHistory invariant
          componentLookup occurrence conclusionOutside)

/-- Raw-or-future sibling exit after every active waiting future mate has been
normalized to an external parent temporal endpoint. -/
inductive ContinuationExitRawOrFutureActiveCarrierExternalTemporalOutcome
    (certificate : Certificate) (state : ReservationState)
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (input : ReadyHeadInput state) (owned : List Vertex)
    (current : ConnectiveBelow certificate input.vertex)
    (origin : Vertex) : Prop where
  | rawOutside {terminal : Vertex}
      (chain : MarkedConclusionChain certificate state origin terminal)
      (terminalOutside : terminal ∉ owned)
      (consumer : ConnectiveBelow certificate terminal)
      (mateUnmarked : state.core.marks[consumer.mate]? = some none)
      (mateOutside : consumer.mate ∉ owned) :
      ContinuationExitRawOrFutureActiveCarrierExternalTemporalOutcome
        certificate state tagHistory input owned current origin
  | rawSelectedReturn {terminal : Vertex}
      (chain : MarkedConclusionChain certificate state origin terminal)
      (terminalOutside : terminal ∉ owned)
      (consumer : ConnectiveBelow certificate terminal)
      (mateUnmarked : state.core.marks[consumer.mate]? = some none)
      (mateSelected : consumer.mate = input.vertex)
      (terminalCurrentMate : terminal = current.mate)
      (conclusionCurrent : consumer.conclusion = current.conclusion) :
      ContinuationExitRawOrFutureActiveCarrierExternalTemporalOutcome
        certificate state tagHistory input owned current origin
  | futureOlder {terminal : Vertex}
      (chain : MarkedConclusionChain certificate state origin terminal)
      (terminalOutside : terminal ∉ owned)
      (consumer : ConnectiveBelow certificate terminal)
      (boundary : RawTokenAge)
      (work : FutureWorkAt state boundary consumer.conclusion)
      (conclusionOutside : consumer.conclusion ∉ owned)
      (boundaryOlder : boundary < input.rawAge)
      (terminalAge mateAge : RawTokenAge)
      (terminalMarked :
        state.core.marks[terminal]? = some (some terminalAge))
      (mateMarked :
        state.core.marks[consumer.mate]? = some (some mateAge))
      (terminalEvent : tagHistory.RawMarked terminalAge terminal)
      (mateEvent : tagHistory.RawMarked mateAge consumer.mate)
      (terminalRepresentativeOlder :
        state.core.representative terminalAge < input.rawAge)
      (mateStatus :
        FutureWorkMateActiveCarrierExternalTemporalStatus certificate state
          input owned terminal consumer boundary mateAge)
      (premiseOrder :
        tagHistory.RawMarkedBefore terminalAge terminal mateAge consumer.mate ∨
          tagHistory.RawMarkedBefore mateAge consumer.mate terminalAge terminal)
      (location :
        FutureWorkAtExactSchedulerLocation certificate state boundary
          consumer.conclusion) :
      ContinuationExitRawOrFutureActiveCarrierExternalTemporalOutcome
        certificate state tagHistory input owned current origin

/-- Lift external waiting-parent refinement across a ready-mate-eliminated
sibling exit. -/
theorem ContinuationExitRawOrFutureActiveCarrierReadyMateOutcome.externalTemporalOutcome
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {usedLinks owned : List Nat}
    (invariant : SchedulerInvariant certificate state)
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      certificate.ComponentOccurrenceWitness component usedLinks owned)
    {current : ConnectiveBelow certificate input.vertex} {origin : Vertex}
    (outcome :
      ContinuationExitRawOrFutureActiveCarrierReadyMateOutcome certificate
        state tagHistory input owned current origin) :
    ContinuationExitRawOrFutureActiveCarrierExternalTemporalOutcome certificate
      state tagHistory input owned current origin := by
  cases outcome with
  | rawOutside chain terminalOutside consumer mateUnmarked mateOutside =>
      exact .rawOutside chain terminalOutside consumer mateUnmarked mateOutside
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
        (mateStatus.externalTemporalStatus tagHistory invariant componentLookup
          occurrence conclusionOutside)
        premiseOrder location

/-- Causal-ownership target whose first-descending sibling exit records every
active waiting mate as an external parent temporal endpoint. -/
def ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitExternalTemporalTarget
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
                    ContinuationExitRawOrFutureActiveCarrierExternalTemporalOutcome
                        certificate state tagHistory input owned current
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
  ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitReadyMateTarget

/-- Refine the causal sibling branch of the ready-mate target to the external
waiting-parent temporal target. -/
theorem externalTemporalTarget
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {usedLinks owned : List Nat}
    {current : ConnectiveBelow certificate input.vertex}
    (invariant : SchedulerInvariant certificate state)
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      certificate.ComponentOccurrenceWitness component usedLinks owned)
    (target :
      ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitReadyMateTarget
        tagHistory input component owned current) :
    ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitExternalTemporalTarget
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
      siblingOutcome.externalTemporalOutcome invariant componentLookup
        occurrence,
      causalOutcome⟩)
  · exact Or.inr (Or.inr (Or.inl future))
  · exact Or.inr (Or.inr (Or.inr marked))

end
  ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitReadyMateTarget

namespace CanonicalTagHistory

private theorem CommitmentIntervalParTraceOutcome.mapExternalTemporalStatus
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

namespace WaitStep

/-- In the strictly older Wait branch, normalize every active-owned waiting
future sibling mate to an external parent temporal endpoint. -/
theorem commitmentInterval_parTraceReentryMarkedContinuationSiblingExitExternalTemporalOutcome
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
        ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitExternalTemporalTarget
            tagHistory step.prepared.readyHeadInput component owned
              step.consumer) := by
  apply CanonicalTagHistory.CommitmentIntervalParTraceOutcome.mapExternalTemporalStatus
    (step.commitmentInterval_parTraceReentryMarkedContinuationSiblingExitReadyMateOutcome
      correct connected tagHistory invariant componentLookup occurrence positive
        firstAt lastAt noTail)
  intro status
  rcases status with ⟨mateOutside, mateMarked, representativeOlder, target⟩
  exact ⟨mateOutside, mateMarked, representativeOlder,
    target.externalTemporalTarget invariant componentLookup occurrence⟩

end WaitStep

end SequentialFigure7
end ProofNetIR
