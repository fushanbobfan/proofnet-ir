/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7MarkedTargetRawReturnSiblingExitOpen

/-!
# Figure-7 sibling continuation temporal exits

An open sibling continuation has only raw-mate or future-work endpoints.  If
the raw mate lies in the active occurrence carrier, exact accounting and the
absence of a non-global ready tail force it to be the current selected head;
consumer uniqueness then identifies the terminal with the current mate and
its conclusion with the current connective conclusion.  Otherwise the raw
mate lies outside the carrier.  A future conclusion outside the carrier is
scheduled at a boundary strictly older than the active ready head.

The strengthened target and typed Wait theorem change only the sibling exit
inside the first causal-descent branch.  Separate target raw, future, and
older marked-global branches remain untouched.  This checkpoint does not
eliminate the exact selected/mate return, produce a ready-tail witness or
history-tail law, discharge the parent re-entry residual, or prove completion
or progress.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerBridge

/-- An open continuation endpoint normalized relative to the active carrier:
raw work outside, an exact return to the current selected/mate pair, or older
future work outside. -/
inductive ContinuationExitRawOrFutureActiveCarrierOutcome
    (certificate : Certificate) (state : ReservationState)
    (input : ReadyHeadInput state) (owned : List Vertex)
    (current : ConnectiveBelow certificate input.vertex)
    (origin : Vertex) : Prop where
  | rawOutside {terminal : Vertex}
      (chain : MarkedConclusionChain certificate state origin terminal)
      (terminalOutside : terminal ∉ owned)
      (consumer : ConnectiveBelow certificate terminal)
      (mateUnmarked : state.core.marks[consumer.mate]? = some none)
      (mateOutside : consumer.mate ∉ owned) :
      ContinuationExitRawOrFutureActiveCarrierOutcome certificate state input
        owned current origin
  | rawSelectedReturn {terminal : Vertex}
      (chain : MarkedConclusionChain certificate state origin terminal)
      (terminalOutside : terminal ∉ owned)
      (consumer : ConnectiveBelow certificate terminal)
      (mateUnmarked : state.core.marks[consumer.mate]? = some none)
      (mateSelected : consumer.mate = input.vertex)
      (terminalCurrentMate : terminal = current.mate)
      (conclusionCurrent : consumer.conclusion = current.conclusion) :
      ContinuationExitRawOrFutureActiveCarrierOutcome certificate state input
        owned current origin
  | futureOlder {terminal : Vertex}
      (chain : MarkedConclusionChain certificate state origin terminal)
      (terminalOutside : terminal ∉ owned)
      (consumer : ConnectiveBelow certificate terminal)
      (boundary : RawTokenAge)
      (work : FutureWorkAt state boundary consumer.conclusion)
      (conclusionOutside : consumer.conclusion ∉ owned)
      (boundaryOlder : boundary < input.rawAge) :
      ContinuationExitRawOrFutureActiveCarrierOutcome certificate state input
        owned current origin

private theorem connectiveMateMembership
    {certificate : Certificate} {vertex : Vertex}
    (consumer : ConnectiveBelow certificate vertex) :
    consumer.mate ∈ consumer.submittedLink.premises := by
  cases kindEq : consumer.kind <;> cases sideEq : consumer.side <;>
    simp [ConnectiveBelow.mate, ConnectiveBelow.submittedLink,
      SequentialConnectiveKind.asLink, Link.premises,
      TensorPremiseSide.mate, kindEq, sideEq]

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

private theorem connectiveVertexOwned_of_premisesOwned
    {certificate : Certificate} {vertex : Vertex}
    (consumer : ConnectiveBelow certificate vertex)
    {owned : List Vertex}
    (premisesOwned :
      consumer.storedLeft ∈ owned ∧ consumer.storedRight ∈ owned) :
    vertex ∈ owned := by
  have premiseEq := consumer.premise_eq
  cases kindEq : consumer.kind <;> cases sideEq : consumer.side <;>
    simp_all [TensorPremiseSide.premise]

private theorem connectiveBelow_mate_and_conclusion_eq_of_mate_eq
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

private theorem connectiveBelowConclusionEq
    {certificate : Certificate} {vertex : Vertex}
    (left right : ConnectiveBelow certificate vertex) :
    left.conclusion = right.conclusion := by
  have sameIndex : left.linkIndex = right.linkIndex :=
    Option.some.inj (left.consumer_eq.symm.trans right.consumer_eq)
  have leftLookup := left.link_eq
  rw [sameIndex] at leftLookup
  have sameLink :
      left.kind.asLink left.storedLeft left.storedRight left.conclusion =
        right.kind.asLink right.storedLeft right.storedRight right.conclusion :=
    Option.some.inj (leftLookup.symm.trans right.link_eq)
  cases leftKind : left.kind <;> cases rightKind : right.kind <;>
    simp [SequentialConnectiveKind.asLink, leftKind, rightKind] at sameLink
  · exact sameLink.2.2
  · exact sameLink.2.2

private theorem MarkedConclusionChain.terminalOutside
    {certificate : Certificate} {state : ReservationState}
    {origin terminal : Vertex}
    (structural : certificate.StructurallyWellFormed)
    {component : UnificationComponent} {usedLinks owned : List Nat}
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component
        usedLinks owned)
    (chain : MarkedConclusionChain certificate state origin terminal)
    (originOutside : origin ∉ owned) :
    terminal ∉ owned := by
  induction chain with
  | refl => exact originOutside
  | step consumer _marked _notConclusion _tail induction =>
      apply induction
      intro conclusionOwned
      have premisesOwned :=
        occurrence.derivation.connectivePremises_owned_of_conclusion_owned
          structural conclusionOwned (connectiveSubmitted consumer)
      exact originOutside
        (connectiveVertexOwned_of_premisesOwned consumer premisesOwned)

private theorem consumerConclusionOutside
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {component : UnificationComponent} {usedLinks owned : List Nat}
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component
        usedLinks owned)
    {terminal : Vertex}
    (terminalOutside : terminal ∉ owned)
    (consumer : ConnectiveBelow certificate terminal) :
    consumer.conclusion ∉ owned := by
  intro conclusionOwned
  have premisesOwned :=
    occurrence.derivation.connectivePremises_owned_of_conclusion_owned
      structural conclusionOwned (connectiveSubmitted consumer)
  have terminalOwned : terminal ∈ owned :=
    connectiveVertexOwned_of_premisesOwned consumer premisesOwned
  exact terminalOutside terminalOwned

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

/-- Normalize an open continuation exit against an exact active occurrence
carrier and a failed non-global ready-tail search. -/
theorem ContinuationExitRawOrFuture.activeCarrierOutcome
    {certificate : Certificate} {state : ReservationState}
    {origin : Vertex}
    (exit : ContinuationExitRawOrFuture certificate state origin)
    (invariant : SchedulerInvariant certificate state)
    (input : ReadyHeadInput state)
    (current : ConnectiveBelow certificate input.vertex)
    {component : UnificationComponent} {usedLinks owned : List Nat}
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component
        usedLinks owned)
    (originOutside : origin ∉ owned)
    (noTail :
      ¬ ∃ pending,
        pending ∈ input.readyTail ∧ pending ∉ certificate.conclusions) :
    ContinuationExitRawOrFutureActiveCarrierOutcome certificate state input
      owned current origin := by
  cases exit with
  | @rawMate terminal chain terminalConsumer mateUnmarked =>
      have terminalOutside := chain.terminalOutside invariant.structural
        occurrence originOutside
      by_cases mateOutside : terminalConsumer.mate ∉ owned
      · exact .rawOutside chain terminalOutside terminalConsumer mateUnmarked
          mateOutside
      · have mateOwned : terminalConsumer.mate ∈ owned := by
          simpa using mateOutside
        have accounted := input.activeOwnedAccounted invariant componentLookup
          occurrence
        rcases accounted terminalConsumer.mate mateOwned with markedCase | rawCase
        · rcases markedCase with ⟨mateAge, mateMarked, _mateRepresentative⟩
          have impossible := mateMarked.symm.trans mateUnmarked
          simp at impossible
        · have mateReady :
              terminalConsumer.mate ∈ input.vertex :: input.readyTail :=
            (input.activeReadyExact invariant componentLookup
              terminalConsumer.mate).mpr ⟨rawCase.2, rawCase.1⟩
          rcases List.mem_cons.mp mateReady with mateSelected | mateTail
          · have sameLink :=
              connectiveBelow_mate_and_conclusion_eq_of_mate_eq
                invariant.structural terminalConsumer current mateSelected
            exact .rawSelectedReturn chain terminalOutside terminalConsumer
              mateUnmarked mateSelected sameLink.1.symm sameLink.2.symm
          · exact False.elim (noTail ⟨terminalConsumer.mate, mateTail,
              submittedPremise_not_conclusion invariant.structural
                terminalConsumer.link_eq
                (connectiveMateMembership terminalConsumer)⟩)
  | @futureConclusion terminal chain terminalConsumer boundary work =>
      have terminalOutside := chain.terminalOutside invariant.structural
        occurrence originOutside
      have conclusionOutside := consumerConclusionOutside invariant.structural
        occurrence terminalOutside terminalConsumer
      have older := work.boundary_lt_active_of_not_owned input invariant
        componentLookup occurrence conclusionOutside
      exact .futureOlder chain terminalOutside terminalConsumer boundary work
        conclusionOutside older

/-- The marked re-entry target after additionally normalizing the two open
sibling endpoints relative to the active occurrence carrier. -/
def ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitTemporalTarget
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (input : ReadyHeadInput state) (component : UnificationComponent)
    (owned : List Vertex)
    (current : ConnectiveBelow certificate input.vertex) : Prop :=
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
                    ContinuationExitRawOrFutureActiveCarrierOutcome certificate
                        state input owned current consumer.conclusion ∧
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

namespace ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitOpenTarget

/-- Normalize the open sibling exit without changing the other target
branches. -/
theorem temporalTarget
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
      Certificate.ComponentOccurrenceWitness certificate component
        usedLinks owned)
    (noTail :
      ¬ ∃ pending,
        pending ∈ input.readyTail ∧ pending ∉ certificate.conclusions)
    (target :
      ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitOpenTarget
        tagHistory input component owned current) :
    ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitTemporalTarget
      tagHistory input component owned current := by
  rcases target with
    ⟨outerAge, outerEvent, path, directed, markedAge, pathStart, finishOwned,
      directedMembership, parentEdge, targetNeSelected, targetNeMate,
      targetMarked, targetEvent, representativeEq, targetConsumer,
      targetConsumerMateNeSelected, sourceConsumer, targetConclusionOutside,
      status⟩
  refine ⟨outerAge, outerEvent, path, directed, markedAge, pathStart,
    finishOwned, directedMembership, parentEdge, targetNeSelected,
    targetNeMate, targetMarked, targetEvent, representativeEq, targetConsumer,
    targetConsumerMateNeSelected, sourceConsumer, targetConclusionOutside, ?_⟩
  rcases status with raw | descent | future | marked
  · exact Or.inl raw
  · rcases descent with
      ⟨descent, consumer, mateAge, mateBeforeOuter, openOutcome,
        causalOutcome⟩
    have conclusionEq : targetConsumer.conclusion = consumer.conclusion :=
      connectiveBelowConclusionEq targetConsumer consumer
    have originOutside : consumer.conclusion ∉ owned := by
      simpa [conclusionEq] using targetConclusionOutside
    exact Or.inr (Or.inl ⟨descent, consumer, mateAge, mateBeforeOuter,
      openOutcome.activeCarrierOutcome invariant input current componentLookup
        occurrence originOutside noTail,
      causalOutcome⟩)
  · exact Or.inr (Or.inr (Or.inl future))
  · exact Or.inr (Or.inr (Or.inr marked))

end ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitOpenTarget

namespace CanonicalTagHistory

private theorem CommitmentIntervalParTraceOutcome.mapTemporalSiblingStatus
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

/-- In the strictly older Wait branch, normalize each open sibling endpoint
relative to the active occurrence carrier. -/
theorem WaitStep.commitmentInterval_parTraceReentryMarkedContinuationSiblingExitTemporalOutcome
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
          ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitTemporalTarget
            tagHistory step.prepared.readyHeadInput component owned
              step.consumer) := by
  apply
    (step.commitmentInterval_parTraceReentryMarkedContinuationSiblingExitOpenOutcome
      correct connected tagHistory invariant componentLookup occurrence positive
      firstAt lastAt noTail).mapTemporalSiblingStatus
  intro status
  rcases status with ⟨mateOutside, mateMarked, representativeOlder, target⟩
  exact ⟨mateOutside, mateMarked, representativeOlder,
    target.temporalTarget invariant componentLookup occurrence noTail⟩

end SequentialFigure7
end ProofNetIR
