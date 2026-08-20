/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7CommitmentIntervalParGuardReentryMarkedTargetContinuationExit

/-!
# Figure-7 marked-target Nop raw-return elimination

A nontrivial marked-conclusion chain always leaves a concrete mark at its
terminal vertex. A successful typed Nop instead keeps its current opposite
premise raw-unmarked. Consequently, the exact raw-return alternative ending at
that opposite premise is impossible in the Nop branch.

The refined target retains the same re-entry geometry and the remaining three
continuation exits: a raw mate outside the active occurrence carrier, older
future work outside that carrier, or an older marked global conclusion outside
the carrier. The generic complete-cancellation and par-pair normal forms remain
valid for other contexts, including Wait. This module does not derive a
ready-tail witness, the history-tail law, completion, or progress.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerBridge

/-- A nontrivial marked-conclusion chain ends at a concretely marked vertex. -/
theorem MarkedConclusionChain.terminal_marked_of_ne
    {certificate : Certificate} {state : ReservationState}
    {origin terminal : Vertex}
    (chain : MarkedConclusionChain certificate state origin terminal)
    (different : origin ≠ terminal) :
    ∃ rawAge,
      state.core.marks[terminal]? = some (some rawAge) := by
  induction chain with
  | refl => exact False.elim (different rfl)
  | @step vertex terminal rawAge consumer marked notConclusion tail induction =>
      by_cases conclusionEq : consumer.conclusion = terminal
      · subst terminal
        exact ⟨rawAge, marked⟩
      · exact induction conclusionEq

private theorem NopStep.no_markedConclusionChain_to_mate
    {certificate : Certificate} {before after : ReservationState}
    (step : NopStep certificate before after)
    {origin : Vertex}
    (different : origin ≠ step.consumer.mate) :
    ¬ MarkedConclusionChain certificate before origin step.consumer.mate := by
  intro chain
  rcases chain.terminal_marked_of_ne different with ⟨rawAge, mateMarked⟩
  rw [step.mate_unmarked_before] at mateMarked
  simp at mateMarked

/-- The mate-separated marked re-entry target after removing the Nop-only
exact raw return. The remaining raw exit is explicitly outside the active
occurrence carrier. -/
def ActiveCarrierExternalReentryMarkedMateSeparatedContinuationNoExactReturnTarget
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

/-- A typed Nop removes the exact raw-return subcase from the generic finite
continuation target. -/
theorem nopNoExactReturnTarget
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    {tagHistory : CanonicalTagHistory certificate history}
    (step : NopStep certificate before after)
    {component : UnificationComponent} {owned : List Vertex}
    (target :
      ActiveCarrierExternalReentryMarkedMateSeparatedContinuationExitTarget
        tagHistory step.prepared.readyHeadInput component owned step.consumer) :
    ActiveCarrierExternalReentryMarkedMateSeparatedContinuationNoExactReturnTarget
      tagHistory step.prepared.readyHeadInput component owned step.consumer := by
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
      exact False.elim
        (step.no_markedConclusionChain_to_mate targetNeMate chain)
  · exact Or.inr (Or.inl future)
  · exact Or.inr (Or.inr marked)

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
      membership eventAge childLt side beforeTrace afterTrace trace status =>
      exact .olderMate offset parent child event offsetLt parentAt childAt
        notAvoiding membership eventAge childLt side beforeTrace afterTrace trace
        (mapStatus status)

end CanonicalTagHistory

/-- In the strictly older Nop branch, remove the exact raw-return alternative
from the marked target's finite continuation exit. -/
theorem NopStep.commitmentInterval_parTraceReentryMarkedContinuationNoExactReturnOutcome
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
          ActiveCarrierExternalReentryMarkedMateSeparatedContinuationNoExactReturnTarget
            tagHistory step.prepared.readyHeadInput component owned
              step.consumer) := by
  apply
    (step.commitmentInterval_parTraceReentryMarkedContinuationExitOutcome
      connected tagHistory invariant componentLookup occurrence positive firstAt
      lastAt noTail).mapOlderMateStatus
  intro status
  rcases status with ⟨mateOutside, mateUnmarked, target⟩
  exact ⟨mateOutside, mateUnmarked, target.nopNoExactReturnTarget step⟩

end SequentialFigure7
end ProofNetIR
