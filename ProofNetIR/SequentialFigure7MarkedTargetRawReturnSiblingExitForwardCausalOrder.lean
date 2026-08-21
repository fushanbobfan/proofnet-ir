/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7MarkedTargetRawReturnCompleteCancellationCausalEndpoints

/-!
# Figure-7 sibling-exit forward causal order

A first causal descent marks both submitted premises before their shared
non-global conclusion.  Its sibling continuation can therefore be re-rooted
after that shared conclusion: a reflexive raw exit would contradict the marked
opposite premise, a reflexive future exit would contradict queued-unmarkedness,
and a reflexive marked-global exit would contradict non-globality.

Two finite marked-conclusion chains with the same origin have comparable
terminals because submitted parents are unique.  Consequently, when one chain
reaches an authenticated outer vertex, a marked-global endpoint of the other
continuation must be strictly after that outer event.  The former
marked-global-before alternative disappears; raw-mate and future exits remain.

The strengthened target and typed Wait theorem keep this forward causal
classification beside the cyclic-source outcome.  They do not eliminate the
raw or future exit, complete cancellation, either exact endpoint junction, the
surviving par-pair residual, the descent, or any ready-tail failure.  No payer,
history-tail law, completion, or progress theorem follows.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerBridge

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

private theorem connectiveBelow_conclusion_eq_of_mate_eq
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {leftVertex rightVertex : Vertex}
    (left : ConnectiveBelow certificate leftVertex)
    (right : ConnectiveBelow certificate rightVertex)
    (leftMate : left.mate = rightVertex) :
    left.conclusion = right.conclusion := by
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
      left.kind.asLink left.storedLeft left.storedRight left.conclusion =
        right.kind.asLink right.storedLeft right.storedRight right.conclusion :=
    Option.some.inj (left.link_eq.symm.trans rightLookup)
  cases leftKind : left.kind <;> cases rightKind : right.kind <;>
    simp [SequentialConnectiveKind.asLink, leftKind, rightKind] at sameLink
  · exact sameLink.2.2
  · exact sameLink.2.2

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

private theorem MarkedConclusionChain.terminalComparable
    {certificate : Certificate} {state : ReservationState}
    {origin first second : Vertex}
    (firstChain : MarkedConclusionChain certificate state origin first)
    (secondChain : MarkedConclusionChain certificate state origin second) :
    MarkedConclusionChain certificate state first second ∨
      MarkedConclusionChain certificate state second first := by
  induction firstChain generalizing second with
  | refl vertex => exact Or.inl secondChain
  | @step vertex terminal rawAge firstConsumer firstMarked firstNotGlobal
      firstTail induction =>
      cases secondChain with
      | refl =>
          exact Or.inr (.step firstConsumer firstMarked firstNotGlobal firstTail)
      | @step _ secondTerminal secondAge secondConsumer secondMarked
          secondNotGlobal secondTail =>
          have conclusionEq :
              firstConsumer.conclusion = secondConsumer.conclusion :=
            connectiveBelowConclusionEq firstConsumer secondConsumer
          have secondTail' :
              MarkedConclusionChain certificate state firstConsumer.conclusion
                second := by
            rw [conclusionEq]
            exact secondTail
          exact induction secondTail'

private theorem rawMarkedAgeEq
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {firstAge secondAge : RawTokenAge} {vertex : Vertex}
    (first : tagHistory.RawMarked firstAge vertex)
    (second : tagHistory.RawMarked secondAge vertex) :
    firstAge = secondAge := by
  have firstMarked :
      state.core.marks[vertex]? = some (some firstAge) :=
    tagHistory.final_rawMarked_iff.mpr first
  have secondMarked :
      state.core.marks[vertex]? = some (some secondAge) :=
    tagHistory.final_rawMarked_iff.mpr second
  exact Option.some.inj (Option.some.inj
    (firstMarked.symm.trans secondMarked))

/-- A continuation exit ordered forward from an authenticated outer vertex.
Raw-mate and future endpoints remain unchanged; a marked-global endpoint is
strictly after the outer event. -/
inductive ContinuationExitOuterTerminalForwardCausalOutcome
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (origin outer : Vertex) (outerAge : RawTokenAge) : Prop where
  | rawMate {terminal : Vertex}
      (chain : MarkedConclusionChain certificate state origin terminal)
      (consumer : ConnectiveBelow certificate terminal)
      (mateUnmarked : state.core.marks[consumer.mate]? = some none) :
      ContinuationExitOuterTerminalForwardCausalOutcome tagHistory origin outer
        outerAge
  | futureConclusion {terminal : Vertex}
      (chain : MarkedConclusionChain certificate state origin terminal)
      (consumer : ConnectiveBelow certificate terminal)
      (boundary : RawTokenAge)
      (work : FutureWorkAt state boundary consumer.conclusion) :
      ContinuationExitOuterTerminalForwardCausalOutcome tagHistory origin outer
        outerAge
  | markedGlobalAfter {terminal : Vertex}
      (chain : MarkedConclusionChain certificate state origin terminal)
      (consumer : ConnectiveBelow certificate terminal)
      (conclusionAge : RawTokenAge)
      (marked :
        state.core.marks[consumer.conclusion]? = some (some conclusionAge))
      (global : consumer.conclusion ∈ certificate.conclusions)
      (before : tagHistory.RawMarkedBefore outerAge outer conclusionAge
        consumer.conclusion) :
      ContinuationExitOuterTerminalForwardCausalOutcome tagHistory origin outer
        outerAge

/-- Remove one already-marked sibling step from a continuation exit. -/
theorem ContinuationExit.afterMarkedSibling
    {certificate : Certificate} {state : ReservationState}
    (structural : certificate.StructurallyWellFormed)
    (queuedUnmarked : QueuedVerticesUnmarked state)
    {origin : Vertex} (consumer : ConnectiveBelow certificate origin)
    {originAge conclusionAge : RawTokenAge}
    (originMarked : state.core.marks[origin]? = some (some originAge))
    (conclusionMarked :
      state.core.marks[consumer.conclusion]? = some (some conclusionAge))
    (conclusionNotGlobal : consumer.conclusion ∉ certificate.conclusions)
    (exit : ContinuationExit certificate state consumer.mate) :
    ContinuationExit certificate state consumer.conclusion := by
  cases exit with
  | rawMate chain terminalConsumer mateUnmarked =>
      cases chain with
      | refl vertex =>
          have mateEq : terminalConsumer.mate = origin :=
            connectiveBelow_mate_eq_of_mate_eq structural consumer
              terminalConsumer rfl
          rw [mateEq, originMarked] at mateUnmarked
          simp at mateUnmarked
      | step first marked notConclusion tail =>
          have conclusionEq : first.conclusion = consumer.conclusion :=
            (connectiveBelow_conclusion_eq_of_mate_eq structural consumer first
              rfl).symm
          exact .rawMate (by simpa [conclusionEq] using tail)
            terminalConsumer mateUnmarked
  | futureConclusion chain terminalConsumer boundary work =>
      cases chain with
      | refl vertex =>
          have conclusionEq :
              terminalConsumer.conclusion = consumer.conclusion :=
            (connectiveBelow_conclusion_eq_of_mate_eq structural consumer
              terminalConsumer rfl).symm
          have unmarked := queuedUnmarked terminalConsumer.conclusion
            work.mem_queued
          rw [conclusionEq, conclusionMarked] at unmarked
          simp at unmarked
      | step first marked notConclusion tail =>
          have conclusionEq : first.conclusion = consumer.conclusion :=
            (connectiveBelow_conclusion_eq_of_mate_eq structural consumer first
              rfl).symm
          exact .futureConclusion (by simpa [conclusionEq] using tail)
            terminalConsumer boundary work
  | markedGlobalConclusion chain terminalConsumer rawAge marked global =>
      cases chain with
      | refl vertex =>
          have conclusionEq :
              terminalConsumer.conclusion = consumer.conclusion :=
            (connectiveBelow_conclusion_eq_of_mate_eq structural consumer
              terminalConsumer rfl).symm
          exact False.elim
            (conclusionNotGlobal (by simpa [conclusionEq] using global))
      | step first firstMarked firstNotConclusion tail =>
          have conclusionEq : first.conclusion = consumer.conclusion :=
            (connectiveBelow_conclusion_eq_of_mate_eq structural consumer first
              rfl).symm
          exact .markedGlobalConclusion (by simpa [conclusionEq] using tail)
            terminalConsumer rawAge marked global

/-- Compare an exit from a common marked-chain origin with an authenticated
outer vertex. A marked-global endpoint can only occur after that vertex. -/
theorem ContinuationExit.outerTerminalForwardCausalOutcome
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {origin outer : Vertex} {outerAge : RawTokenAge}
    (exit : ContinuationExit certificate state origin)
    (outerChain : MarkedConclusionChain certificate state origin outer)
    (outerEvent : tagHistory.RawMarked outerAge outer) :
    ContinuationExitOuterTerminalForwardCausalOutcome tagHistory origin outer
      outerAge := by
  cases exit with
  | rawMate chain consumer mateUnmarked =>
      exact .rawMate chain consumer mateUnmarked
  | futureConclusion chain consumer boundary work =>
      exact .futureConclusion chain consumer boundary work
  | markedGlobalConclusion chain consumer conclusionAge marked global =>
      have conclusionEvent :
          tagHistory.RawMarked conclusionAge consumer.conclusion :=
        tagHistory.final_rawMarked_iff.mp marked
      rcases tagHistory.rawMarkedPremisesBefore consumer conclusionEvent with
        ⟨terminalAge, _mateAge, terminalBefore, _mateBefore⟩
      rcases chain.terminalComparable outerChain with
        terminalToOuter | outerToTerminal
      · cases terminalToOuter with
        | refl =>
            have ageEq : terminalAge = outerAge :=
              rawMarkedAgeEq terminalBefore.first_rawMarked outerEvent
            subst terminalAge
            exact .markedGlobalAfter chain consumer conclusionAge marked global
              terminalBefore
        | step first firstMarked firstNotGlobal tail =>
            have conclusionEq : first.conclusion = consumer.conclusion :=
              connectiveBelowConclusionEq first consumer
            exact False.elim
              (firstNotGlobal (by simpa [conclusionEq] using global))
      · rcases outerToTerminal.rawMarkedBefore_or_eq tagHistory
          terminalBefore.first_rawMarked with same | ⟨age, outerBeforeTerminal⟩
        · subst outer
          have ageEq : terminalAge = outerAge :=
            rawMarkedAgeEq terminalBefore.first_rawMarked outerEvent
          subst terminalAge
          exact .markedGlobalAfter chain consumer conclusionAge marked global
            terminalBefore
        · have ageEq : age = outerAge :=
            rawMarkedAgeEq outerBeforeTerminal.first_rawMarked outerEvent
          subst age
          exact .markedGlobalAfter chain consumer conclusionAge marked global
            (CanonicalTagHistory.RawMarkedBefore.trans outerBeforeTerminal
              terminalBefore)

private theorem
    MarkedConclusionChainFirstCausalDescent.sourceExitOuterTerminalForwardCausalOutcome
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {origin outer : Vertex} {active outerAge : RawTokenAge}
    (structural : certificate.StructurallyWellFormed)
    (queuedUnmarked : QueuedVerticesUnmarked state)
    (descent : MarkedConclusionChainFirstCausalDescent certificate state
      tagHistory origin outer active)
    (outerEvent : tagHistory.RawMarked outerAge outer) :
    ∃ consumer : ConnectiveBelow certificate origin,
      ContinuationExitOuterTerminalForwardCausalOutcome tagHistory
        consumer.conclusion outer outerAge := by
  rcases descent with
    ⟨originAge, consumer, conclusionAge, _mateAge, originMarked,
      _originRepresentative, conclusionMarked, _conclusionEvent,
      conclusionNotGlobal, _conclusionOlder, _originBefore, _mateBefore,
      mateExit, tail⟩
  have sourceExit :
      ContinuationExit certificate state consumer.conclusion :=
    mateExit.afterMarkedSibling structural queuedUnmarked consumer originMarked
      conclusionMarked conclusionNotGlobal
  exact ⟨consumer,
    sourceExit.outerTerminalForwardCausalOutcome tail outerEvent⟩

/-- The marked re-entry target with its sibling continuation re-rooted at the
shared cyclic source. A marked-global endpoint is retained only after the
authenticated outer terminal. -/
def ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitForwardCausalTarget
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
                    ContinuationExitOuterTerminalForwardCausalOutcome tagHistory
                        consumer.conclusion current.mate outerAge ∧
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

namespace ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitCausalEndpointTarget

/-- Re-root the sibling exit at its shared marked parent and remove the
marked-global-before case without changing the other target branches. -/
theorem forwardCausalTarget
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {owned : List Vertex}
    {current : ConnectiveBelow certificate input.vertex}
    (structural : certificate.StructurallyWellFormed)
    (queuedUnmarked : QueuedVerticesUnmarked state)
    (target :
      ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitCausalEndpointTarget
        tagHistory input component owned current) :
    ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitForwardCausalTarget
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
      ⟨descent, consumer, mateAge, mateBeforeOuter, _siblingOutcome,
        causalOutcome⟩
    rcases descent.sourceExitOuterTerminalForwardCausalOutcome structural
        queuedUnmarked outerEvent with ⟨sourceConsumer, sourceOutcome⟩
    have conclusionEq : sourceConsumer.conclusion = consumer.conclusion :=
      connectiveBelowConclusionEq sourceConsumer consumer
    exact Or.inr (Or.inl ⟨descent, consumer, mateAge, mateBeforeOuter,
      by simpa [conclusionEq] using sourceOutcome, causalOutcome⟩)
  · exact Or.inr (Or.inr (Or.inl future))
  · exact Or.inr (Or.inr (Or.inr marked))

end ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitCausalEndpointTarget

namespace CanonicalTagHistory

private theorem CommitmentIntervalParTraceOutcome.mapForwardCausalStatus
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

/-- In the strictly older Wait branch, re-root the sibling exit at the cyclic
source and retain only the forward marked-global order. -/
theorem
    WaitStep.commitmentInterval_parTraceReentryMarkedContinuationSiblingExitForwardCausalOutcome
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
          ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitForwardCausalTarget
            tagHistory step.prepared.readyHeadInput component owned
              step.consumer) := by
  apply CanonicalTagHistory.CommitmentIntervalParTraceOutcome.mapForwardCausalStatus
    (step.commitmentInterval_parTraceReentryMarkedContinuationSiblingExitCausalEndpointOutcome
      correct connected tagHistory invariant componentLookup occurrence positive
      firstAt lastAt noTail)
  intro status
  rcases status with ⟨mateOutside, mateMarked, representativeOlder, target⟩
  exact ⟨mateOutside, mateMarked, representativeOlder,
    target.forwardCausalTarget invariant.structural
      invariant.queued_vertices_unmarked⟩

end SequentialFigure7
end ProofNetIR
