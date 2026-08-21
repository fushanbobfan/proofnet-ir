/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7MarkedTargetRawReturnSiblingExitCausalJunction

/-!
# Figure-7 cyclic-junction endpoint causal order

Nonempty complete raw-return cancellation follows the exact reverse of its
retained switching prefix. Consequently both segment endpoints, rather than one
disjunctive cancellation site, expose simultaneous reverse junctions with
their exact walk endpoints.

The marked-conclusion chain also places the cyclic source endpoint either at
the authenticated outer terminal or strictly before it in canonical raw-mark
order. The generic target adapter and typed Wait theorem retain this causal
endpoint classification on the same first-descent branch as the sibling exit
and cyclic normal form.

This checkpoint does not rule out complete cancellation, either endpoint
junction, the surviving par-pair residual, any sibling exit, or either marked-
global order. It derives no ready-tail witness, history-tail law, completion,
or progress theorem.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerBridge

/-- The exact reverse traversal in nonempty complete cancellation exposes
both reverse segment junctions and their four walk endpoints at once. -/
def MarkedConclusionRawReturnCompleteCancellationEndpointJunctions
    {certificate : Certificate}
    (base source : Vertex)
    (retainedPrefix continuationTail :
      List certificate.fullGraph.DirectedEdge) : Prop :=
  ∃ prefixLast tailHead prefixHead tailLast,
    retainedPrefix.getLast? = some prefixLast ∧
      continuationTail.head? = some tailHead ∧
        tailHead = prefixLast.reverse ∧
          prefixLast.forward = false ∧
            tailHead.forward = true ∧
              retainedPrefix.head? = some prefixHead ∧
                continuationTail.getLast? = some tailLast ∧
                  prefixHead = tailLast.reverse ∧
                    prefixHead.forward = false ∧
                      tailLast.forward = true ∧
                        prefixLast.target = source ∧
                          tailHead.source = source ∧
                            prefixHead.source = base ∧
                              tailLast.target = base

/-- The exact reverse-traversal ledger of nonempty complete cancellation gives
both endpoint junctions simultaneously. -/
theorem
    MarkedConclusionRawReturnCompleteCancellationTraversal.endpointJunctions
    {certificate : Certificate} {state : ReservationState}
    {base source : Vertex}
    {retainedPrefix continuationTail :
      List certificate.fullGraph.DirectedEdge}
    (complete :
      MarkedConclusionRawReturnCompleteCancellationTraversal state
        retainedPrefix continuationTail)
    (prefixWalk : certificate.fullGraph.EdgeWalk base retainedPrefix source)
    (tailWalk : certificate.fullGraph.EdgeWalk source continuationTail base)
    (prefixNonempty : retainedPrefix ≠ []) :
    MarkedConclusionRawReturnCompleteCancellationEndpointJunctions
      base source retainedPrefix continuationTail := by
  rcases complete with ⟨pairing, traversalEq⟩
  have tailNonempty : continuationTail ≠ [] := by
    rw [traversalEq]
    simpa [Graph.EdgeWalk.reverseTraversal] using prefixNonempty
  let prefixLast := retainedPrefix.getLast prefixNonempty
  let tailHead := continuationTail.head tailNonempty
  let prefixHead := retainedPrefix.head prefixNonempty
  let tailLast := continuationTail.getLast tailNonempty
  have prefixLastLookup : retainedPrefix.getLast? = some prefixLast := by
    exact List.getLast?_eq_some_getLast prefixNonempty
  have tailHeadLookup : continuationTail.head? = some tailHead := by
    exact List.head?_eq_some_head tailNonempty
  have prefixHeadLookup : retainedPrefix.head? = some prefixHead := by
    exact List.head?_eq_some_head prefixNonempty
  have tailLastLookup : continuationTail.getLast? = some tailLast := by
    exact List.getLast?_eq_some_getLast tailNonempty
  have tailHeadEq : tailHead = prefixLast.reverse := by
    have headEquation := congrArg List.head? traversalEq
    rw [tailHeadLookup] at headEquation
    have reverseHeadLookup :
        (Graph.EdgeWalk.reverseTraversal retainedPrefix).head? =
          some prefixLast.reverse := by
      simp [Graph.EdgeWalk.reverseTraversal, prefixLastLookup]
    exact Option.some.inj (headEquation.trans reverseHeadLookup)
  have tailLastEq : tailLast = prefixHead.reverse := by
    have lastEquation := congrArg List.getLast? traversalEq
    rw [tailLastLookup] at lastEquation
    have reverseLastLookup :
        (Graph.EdgeWalk.reverseTraversal retainedPrefix).getLast? =
          some prefixHead.reverse := by
      simp [Graph.EdgeWalk.reverseTraversal, prefixHeadLookup]
    exact Option.some.inj (lastEquation.trans reverseLastLookup)
  have prefixLastMembership : prefixLast ∈ retainedPrefix :=
    List.getLast_mem prefixNonempty
  have prefixHeadMembership : prefixHead ∈ retainedPrefix :=
    List.head_mem prefixNonempty
  have prefixLastBackward : prefixLast.forward = false :=
    (pairing.2.2.1 prefixLast prefixLastMembership).1
  have prefixHeadBackward : prefixHead.forward = false :=
    (pairing.2.2.1 prefixHead prefixHeadMembership).1
  have tailHeadForward : tailHead.forward = true := by
    rw [tailHeadEq]
    simp [Graph.DirectedEdge.reverse, prefixLastBackward]
  have tailLastForward : tailLast.forward = true := by
    rw [tailLastEq]
    simp [Graph.DirectedEdge.reverse, prefixHeadBackward]
  have prefixLastTarget : prefixLast.target = source := by
    simpa [prefixLast] using prefixWalk.getLast_target prefixNonempty
  have tailLastTarget : tailLast.target = base := by
    simpa [tailLast] using tailWalk.getLast_target tailNonempty
  have prefixHeadSource : prefixHead.source = base := by
    have chain := prefixWalk.toChain
    rw [← List.cons_head_tail prefixNonempty] at chain
    simpa [prefixHead] using chain.head_source
  have tailHeadSource : tailHead.source = source := by
    have chain := tailWalk.toChain
    rw [← List.cons_head_tail tailNonempty] at chain
    simpa [tailHead] using chain.head_source
  refine ⟨prefixLast, tailHead, prefixHead, tailLast,
    prefixLastLookup, tailHeadLookup, tailHeadEq, prefixLastBackward,
    tailHeadForward, prefixHeadLookup, tailLastLookup, ?_,
    prefixHeadBackward, tailLastForward, prefixLastTarget, tailHeadSource,
    prefixHeadSource, tailLastTarget⟩
  rw [tailLastEq]
  simp

/-- A cyclic-junction outcome together with the canonical causal position of
its source endpoint relative to an authenticated base endpoint. -/
def MarkedConclusionRawReturnCyclicJunctionCausalOutcome
    (certificate : Certificate) (state : ReservationState)
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (base source : Vertex) (baseAge : RawTokenAge) : Prop :=
  MarkedConclusionRawReturnCyclicJunctionOutcome certificate state base source ∧
    (source = base ∨
      ∃ sourceAge,
        tagHistory.RawMarkedBefore sourceAge source baseAge base)

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

/-- The same first-causal-descent chain that produces the cyclic-junction
normal form also places its source endpoint at or strictly before the
authenticated outer endpoint. -/
theorem
    MarkedConclusionChainFirstCausalDescent.rawReturnCyclicJunctionCausalOutcome
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {origin outer : Vertex} {active outerAge : RawTokenAge}
    (correct : certificate.DeclarativelyCorrect)
    (descent : MarkedConclusionChainFirstCausalDescent certificate state
      tagHistory origin outer active)
    (outerEvent : tagHistory.RawMarked outerAge outer)
    (path : certificate.referenceSwitchingGraph.EdgeSimplePath)
    (pathStart : path.start = outer)
    (directed : certificate.referenceSwitchingGraph.DirectedEdge)
    (directedMembership : directed ∈ path.traversed)
    (targetConsumer : ConnectiveBelow certificate origin)
    (sourceConsumer : directed.source = targetConsumer.conclusion)
    (different : origin ≠ outer) :
    MarkedConclusionRawReturnCyclicJunctionCausalOutcome certificate state
      tagHistory outer targetConsumer.conclusion outerAge := by
  have cyclic := descent.rawReturnCyclicJunctionOutcome correct path pathStart
    directed directedMembership targetConsumer sourceConsumer different
  rcases descent with
    ⟨_originAge, consumer, _conclusionAge, _mateAge, _originMarked,
      _originRepresentative, _conclusionMarked, _conclusionEvent,
      _conclusionNotGlobal, _conclusionOlder, _originBefore, _mateBefore,
      _mateExit, tail⟩
  have conclusionEq : consumer.conclusion = targetConsumer.conclusion :=
    connectiveBelowConclusionEq consumer targetConsumer
  refine ⟨cyclic, ?_⟩
  rcases MarkedConclusionChain.rawMarkedBefore_or_eq tagHistory tail outerEvent
      with same | ⟨sourceAge, before⟩
  · exact Or.inl (conclusionEq.symm.trans same)
  · exact Or.inr ⟨sourceAge, by simpa [conclusionEq] using before⟩

/-- The sibling-exit causal/cyclic target with the cyclic source endpoint
ordered against its authenticated outer endpoint. -/
def ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitCausalEndpointTarget
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
                    ContinuationExitOuterTerminalCausalOutcome tagHistory
                        consumer.mate current.mate outerAge ∧
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

namespace ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitCausalJunctionTarget

/-- Add the cyclic source's causal position to the first-descent branch without
changing the other three continuation exits. -/
theorem causalEndpointTarget
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {owned : List Vertex}
    {current : ConnectiveBelow certificate input.vertex}
    (correct : certificate.DeclarativelyCorrect)
    (target :
      ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitCausalJunctionTarget
        tagHistory input component owned current) :
    ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitCausalEndpointTarget
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
      ⟨descent, consumer, mateAge, mateBeforeOuter, siblingOutcome,
        _cyclicOutcome⟩
    have causalOutcome := descent.rawReturnCyclicJunctionCausalOutcome correct
      outerEvent path pathStart directed directedMembership targetConsumer
      sourceConsumer targetNeMate
    have conclusionEq : targetConsumer.conclusion = consumer.conclusion :=
      connectiveBelowConclusionEq targetConsumer consumer
    exact Or.inr (Or.inl ⟨descent, consumer, mateAge, mateBeforeOuter,
      siblingOutcome, by simpa [conclusionEq] using causalOutcome⟩)
  · exact Or.inr (Or.inr (Or.inl future))
  · exact Or.inr (Or.inr (Or.inr marked))

end ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitCausalJunctionTarget

namespace CanonicalTagHistory

private theorem CommitmentIntervalParTraceOutcome.mapCausalEndpointStatus
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

open ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitCausalJunctionTarget

/-- In the strictly older Wait branch, align both cyclic endpoint junctions and
the cyclic source's causal order with the retained sibling-exit receipt. -/
theorem
    WaitStep.commitmentInterval_parTraceReentryMarkedContinuationSiblingExitCausalEndpointOutcome
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
          ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitCausalEndpointTarget
            tagHistory step.prepared.readyHeadInput component owned
              step.consumer) := by
  apply CanonicalTagHistory.CommitmentIntervalParTraceOutcome.mapCausalEndpointStatus
    (step.commitmentInterval_parTraceReentryMarkedContinuationSiblingExitCausalJunctionOutcome
      correct connected tagHistory invariant componentLookup occurrence positive
      firstAt lastAt noTail)
  intro status
  rcases status with ⟨mateOutside, mateMarked, representativeOlder, target⟩
  exact ⟨mateOutside, mateMarked, representativeOlder,
    target.causalEndpointTarget correct⟩

end SequentialFigure7
end ProofNetIR
