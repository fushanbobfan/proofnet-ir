/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7MarkedTargetRawReturnSiblingExitCausalOrder
import ProofNetIR.SequentialFigure7MarkedTargetRawReturnCyclicReduction

/-!
# Figure-7 sibling-exit causal/cyclic junction

The first causal descent still carries the exact marked-conclusion chain that
returns from the re-entry target to the outer mate. This module applies the
existing cyclic-junction reduction to that same chain and retains the sibling
exit's causal classification against the authenticated outer terminal.

The result aligns chronology and switching geometry on one witness. It does
not eliminate a cyclic junction, par-pair residual, sibling endpoint, or
ordered marked-global branch, and it derives no ready-tail witness,
history-tail law, completion, or progress theorem.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerBridge

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

/-- The full chain retained by a first causal descent has the existing exact
cyclic-junction normal form on the same switching prefix. -/
theorem MarkedConclusionChainFirstCausalDescent.rawReturnCyclicJunctionOutcome
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {origin outer : Vertex} {active : RawTokenAge}
    (correct : certificate.DeclarativelyCorrect)
    (descent : MarkedConclusionChainFirstCausalDescent certificate state
      tagHistory origin outer active)
    (path : certificate.referenceSwitchingGraph.EdgeSimplePath)
    (pathStart : path.start = outer)
    (directed : certificate.referenceSwitchingGraph.DirectedEdge)
    (directedMembership : directed ∈ path.traversed)
    (targetConsumer : ConnectiveBelow certificate origin)
    (sourceConsumer : directed.source = targetConsumer.conclusion)
    (different : origin ≠ outer) :
    MarkedConclusionRawReturnCyclicJunctionOutcome certificate state outer
      targetConsumer.conclusion := by
  rcases descent with
    ⟨_originAge, consumer, _conclusionAge, _mateAge, _originMarked,
      _originRepresentative, conclusionMarked, _conclusionEvent,
      conclusionNotGlobal, _conclusionOlder, _originBefore, _mateBefore,
      _mateExit, tail⟩
  have conclusionEq : consumer.conclusion = targetConsumer.conclusion :=
    connectiveBelowConclusionEq consumer targetConsumer
  have fullChain :
      MarkedConclusionChain certificate state origin outer :=
    .step consumer conclusionMarked conclusionNotGlobal tail
  have sourceConsumer' : directed.source = consumer.conclusion :=
    sourceConsumer.trans conclusionEq.symm
  have outcome := fullChain.rawReturnCyclicJunctionReduction correct path
    pathStart directed directedMembership consumer sourceConsumer' different
  simpa [conclusionEq] using outcome

/-- A sibling-exit causal target whose first-descent chain also carries its
exact cyclic-junction normal form. -/
def ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitCausalJunctionTarget
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
                      MarkedConclusionRawReturnCyclicJunctionOutcome certificate
                        state current.mate consumer.conclusion) ∨
              (∃ terminal,
                MarkedConclusionChain certificate state directed.target
                    terminal ∧
                  ∃ terminalConsumer : ConnectiveBelow certificate terminal,
                    ∃ boundary,
                      FutureWorkAt state boundary terminalConsumer.conclusion ∧
                      terminalConsumer.conclusion ∉ owned ∧
                      boundary < input.rawAge) ∨
              ∃ terminal,
                MarkedConclusionChain certificate state directed.target
                    terminal ∧
                  ∃ terminalConsumer : ConnectiveBelow certificate terminal,
                    ∃ conclusionAge,
                      state.core.marks[terminalConsumer.conclusion]? =
                        some (some conclusionAge) ∧
                      terminalConsumer.conclusion ∈ certificate.conclusions ∧
                      terminalConsumer.conclusion ∉ owned ∧
                      state.core.representative conclusionAge < input.rawAge)

namespace ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitCausalTarget

/-- Add the exact cyclic-junction normal form to the retained first-descent
branch without changing the other three continuation exits. -/
theorem causalJunctionTarget
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {owned : List Vertex}
    {current : ConnectiveBelow certificate input.vertex}
    (correct : certificate.DeclarativelyCorrect)
    (target :
      ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitCausalTarget
        tagHistory input component owned current) :
    ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitCausalJunctionTarget
      tagHistory input component owned current := by
  rcases target with
    ⟨outerAge, outerEvent, path, directed, markedAge, pathStart, finishOwned,
      directedMembership, parentEdge, targetNeSelected, targetNeMate,
      targetMarked, targetEvent, representativeEq, targetConsumer,
      targetConsumerMateNeSelected, sourceConsumer, targetConclusionOutside,
      status⟩
  refine ⟨outerAge, outerEvent, path, directed, markedAge, pathStart,
    finishOwned, directedMembership, parentEdge, targetNeSelected, targetNeMate,
    targetMarked, targetEvent, representativeEq, targetConsumer,
    targetConsumerMateNeSelected, sourceConsumer, targetConclusionOutside, ?_⟩
  rcases status with raw | descent | future | marked
  · exact Or.inl raw
  · rcases descent with
      ⟨descent, consumer, mateAge, mateBeforeOuter, siblingOutcome⟩
    have cyclicOutcome := descent.rawReturnCyclicJunctionOutcome correct path
      pathStart directed directedMembership targetConsumer sourceConsumer
      targetNeMate
    have conclusionEq : targetConsumer.conclusion = consumer.conclusion :=
      connectiveBelowConclusionEq targetConsumer consumer
    exact Or.inr (Or.inl ⟨descent, consumer, mateAge, mateBeforeOuter,
      siblingOutcome, by simpa [conclusionEq] using cyclicOutcome⟩)
  · exact Or.inr (Or.inr (Or.inl future))
  · exact Or.inr (Or.inr (Or.inr marked))

end ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitCausalTarget

namespace CanonicalTagHistory

private theorem CommitmentIntervalParTraceOutcome.mapCausalJunctionStatus
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

open ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitCausalTarget

/-- In the strictly older Wait branch, align the sibling-exit causal order with
the exact cyclic-junction normal form of the same first-descent chain. -/
theorem
    WaitStep.commitmentInterval_parTraceReentryMarkedContinuationSiblingExitCausalJunctionOutcome
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
          ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitCausalJunctionTarget
            tagHistory step.prepared.readyHeadInput component owned
              step.consumer) := by
  apply CanonicalTagHistory.CommitmentIntervalParTraceOutcome.mapCausalJunctionStatus
    (step.commitmentInterval_parTraceReentryMarkedContinuationSiblingExitCausalOutcome
      connected tagHistory invariant componentLookup occurrence positive firstAt
      lastAt noTail)
  intro status
  rcases status with ⟨mateOutside, mateMarked, representativeOlder, target⟩
  exact ⟨mateOutside, mateMarked, representativeOlder,
    target.causalJunctionTarget correct⟩

end SequentialFigure7
end ProofNetIR
