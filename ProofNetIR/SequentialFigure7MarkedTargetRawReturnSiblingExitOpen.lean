/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7MarkedTargetRawReturnSiblingExitForwardCausalOrder

/-!
# Figure-7 sibling continuation open exits

The selected ready head is raw-unmarked.  If the sibling continuation from a
first causal descent ended at a marked global conclusion, comparison with the
descent tail would force the selected connective conclusion to be marked.
Canonical raw-mark history would then force the selected premise itself to
have been marked earlier, contradicting the ready-head state.

Thus only raw-mate and future-work sibling exits remain in this context.

The strengthened target and typed Wait theorem change only the sibling exit
inside the first causal-descent branch.  The target's separate raw, future,
and older marked-global branches remain untouched.  This checkpoint does not
eliminate the two open sibling endpoints, produce a ready-tail witness or
history-tail law, discharge the parent re-entry residual, or prove completion
or progress.
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

/-- Two finite marked-conclusion chains from one origin have comparable
terminals. -/
theorem MarkedConclusionChain.terminalComparable
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

/-- A continuation exit whose endpoint remains open: either a raw opposite
premise or scheduled conclusion work. -/
inductive ContinuationExitRawOrFuture (certificate : Certificate)
    (state : ReservationState) (origin : Vertex) : Prop where
  | rawMate {terminal : Vertex}
      (chain : MarkedConclusionChain certificate state origin terminal)
      (consumer : ConnectiveBelow certificate terminal)
      (mateUnmarked : state.core.marks[consumer.mate]? = some none) :
      ContinuationExitRawOrFuture certificate state origin
  | futureConclusion {terminal : Vertex}
      (chain : MarkedConclusionChain certificate state origin terminal)
      (consumer : ConnectiveBelow certificate terminal)
      (boundary : RawTokenAge)
      (work : FutureWorkAt state boundary consumer.conclusion) :
      ContinuationExitRawOrFuture certificate state origin

private theorem selectedPremise_not_marked
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (input : ReadyHeadInput state)
    (current : ConnectiveBelow certificate input.vertex)
    (selectedUnmarked : state.core.marks[input.vertex]? = some none)
    {conclusionAge : RawTokenAge}
    (conclusionMarked :
      state.core.marks[current.conclusion]? = some (some conclusionAge)) :
    False := by
  have conclusionEvent :
      tagHistory.RawMarked conclusionAge current.conclusion :=
    tagHistory.final_rawMarked_iff.mp conclusionMarked
  rcases tagHistory.rawMarkedPremisesBefore current conclusionEvent with
    ⟨premiseAge, _mateAge, premiseBefore, _mateBefore⟩
  have selectedMarked :
      state.core.marks[input.vertex]? = some (some premiseAge) :=
    tagHistory.final_rawMarked_iff.mpr premiseBefore.first_rawMarked
  rw [selectedUnmarked] at selectedMarked
  simp at selectedMarked

/-- A first causal descent from a selected ready head has only raw-mate or
future-work sibling exits; a marked-global sibling endpoint is impossible. -/
theorem MarkedConclusionChainFirstCausalDescent.sourceExitRawOrFuture
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {origin : Vertex} {active : RawTokenAge}
    (structural : certificate.StructurallyWellFormed)
    (queuedUnmarked : QueuedVerticesUnmarked state)
    (input : ReadyHeadInput state)
    (current : ConnectiveBelow certificate input.vertex)
    (selectedUnmarked : state.core.marks[input.vertex]? = some none)
    (descent : MarkedConclusionChainFirstCausalDescent certificate state
      tagHistory origin current.mate active) :
    ∃ consumer : ConnectiveBelow certificate origin,
      ContinuationExitRawOrFuture certificate state consumer.conclusion := by
  rcases descent with
    ⟨originAge, consumer, conclusionAge, _mateAge, originMarked,
      _originRepresentative, conclusionMarked, _conclusionEvent,
      conclusionNotGlobal, _conclusionOlder, _originBefore, _mateBefore,
      mateExit, tail⟩
  have sourceExit :
      ContinuationExit certificate state consumer.conclusion :=
    mateExit.afterMarkedSibling structural queuedUnmarked consumer
      originMarked conclusionMarked conclusionNotGlobal
  refine ⟨consumer, ?_⟩
  cases sourceExit with
  | rawMate chain terminalConsumer mateUnmarked =>
      exact .rawMate chain terminalConsumer mateUnmarked
  | futureConclusion chain terminalConsumer boundary work =>
      exact .futureConclusion chain terminalConsumer boundary work
  | markedGlobalConclusion chain terminalConsumer terminalAge terminalMarked
      terminalGlobal =>
      have currentConclusionMarked :
          ∃ rawAge,
            state.core.marks[current.conclusion]? = some (some rawAge) := by
        rcases chain.terminalComparable tail with terminalToOuter | outerToTerminal
        · cases terminalToOuter with
          | refl =>
              have conclusionEq :
                  current.conclusion = terminalConsumer.conclusion :=
                connectiveBelow_conclusion_eq_of_mate_eq
                  structural current terminalConsumer rfl
              exact ⟨terminalAge, by simpa [conclusionEq] using terminalMarked⟩
          | step first firstMarked firstNotGlobal firstTail =>
              have conclusionEq :
                  first.conclusion = terminalConsumer.conclusion :=
                connectiveBelowConclusionEq first terminalConsumer
              exact False.elim
                (firstNotGlobal (by simpa [conclusionEq] using terminalGlobal))
        · cases outerToTerminal with
          | refl =>
              have conclusionEq :
                  current.conclusion = terminalConsumer.conclusion :=
                connectiveBelow_conclusion_eq_of_mate_eq
                  structural current terminalConsumer rfl
              exact ⟨terminalAge, by simpa [conclusionEq] using terminalMarked⟩
          | step first firstMarked firstNotGlobal firstTail =>
              have conclusionEq : current.conclusion = first.conclusion :=
                connectiveBelow_conclusion_eq_of_mate_eq
                  structural current first rfl
              exact ⟨_, by simpa [conclusionEq] using firstMarked⟩
      rcases currentConclusionMarked with ⟨currentAge, currentMarked⟩
      exact False.elim
        (selectedPremise_not_marked tagHistory input current selectedUnmarked
          currentMarked)

/-- The marked re-entry target after eliminating the marked-global sibling
endpoint from its first causal-descent branch. -/
def ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitOpenTarget
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
                    ContinuationExitRawOrFuture certificate state
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

namespace ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitForwardCausalTarget

/-- Eliminate the marked-global sibling endpoint from a forward-causal target
selected from the active ready head. -/
theorem openTarget
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {owned : List Vertex}
    {current : ConnectiveBelow certificate input.vertex}
    (structural : certificate.StructurallyWellFormed)
    (queuedUnmarked : QueuedVerticesUnmarked state)
    (selectedUnmarked : state.core.marks[input.vertex]? = some none)
    (target :
      ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitForwardCausalTarget
        tagHistory input component owned current) :
    ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitOpenTarget
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
      ⟨descent, consumer, mateAge, mateBeforeOuter, _forwardOutcome,
        causalOutcome⟩
    rcases descent.sourceExitRawOrFuture structural queuedUnmarked input current
        selectedUnmarked with
      ⟨sourceConsumer, openOutcome⟩
    have conclusionEq : sourceConsumer.conclusion = consumer.conclusion :=
      connectiveBelowConclusionEq sourceConsumer consumer
    exact Or.inr (Or.inl ⟨descent, consumer, mateAge, mateBeforeOuter,
      by simpa [conclusionEq] using openOutcome, causalOutcome⟩)
  · exact Or.inr (Or.inr (Or.inl future))
  · exact Or.inr (Or.inr (Or.inr marked))

end ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitForwardCausalTarget

namespace CanonicalTagHistory

private theorem CommitmentIntervalParTraceOutcome.mapOpenStatus
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

/-- In the strictly older Wait branch, the first causal-descent sibling has
only a raw-mate or future-work endpoint. -/
theorem WaitStep.commitmentInterval_parTraceReentryMarkedContinuationSiblingExitOpenOutcome
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
          ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitOpenTarget
            tagHistory step.prepared.readyHeadInput component owned
              step.consumer) := by
  apply CanonicalTagHistory.CommitmentIntervalParTraceOutcome.mapOpenStatus
    (step.commitmentInterval_parTraceReentryMarkedContinuationSiblingExitForwardCausalOutcome
      correct connected tagHistory invariant componentLookup occurrence positive
      firstAt lastAt noTail)
  intro status
  rcases status with ⟨mateOutside, mateMarked, representativeOlder, target⟩
  have selectedUnmarked :
      before.core.marks[step.prepared.stackResult.vertex]? = some none :=
    invariant.queued_vertices_unmarked step.prepared.stackResult.vertex
      (step.prepared.readyHeadInput.futureWorkAt invariant).mem_queued
  exact ⟨mateOutside, mateMarked, representativeOlder,
    target.openTarget invariant.structural invariant.queued_vertices_unmarked
      selectedUnmarked⟩

end SequentialFigure7
end ProofNetIR
