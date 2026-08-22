/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import
  ProofNetIR.SequentialFigure7MarkedTargetWaitingMateExternalCommitmentReentryContinuationQueueStatus

/-!
# Continuation sibling queue status

This module refines only the causal continuation sibling outcome while
preserving the enclosing waiting target and its other three exit branches.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerBridge

/-- The waiting sibling-exit target whose causal continuation carries the
queue-status endpoint. -/
def ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitWaitingQueueStatusTarget
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (input : ReadyHeadInput state) (component : UnificationComponent)
    (owned : List Vertex) (current : ConnectiveBelow certificate input.vertex) : Prop :=
  ∃ outerAge : RawTokenAge, tagHistory.RawMarked outerAge current.mate ∧
    ∃ (path : certificate.referenceSwitchingGraph.EdgeSimplePath)
        (directed : certificate.referenceSwitchingGraph.DirectedEdge)
        (markedAge : RawTokenAge),
      path.start = current.mate ∧ path.finish ∈ owned ∧
      directed ∈ path.traversed ∧
      ActiveCarrierInboundParentEdge certificate component owned directed ∧
      directed.target ≠ input.vertex ∧ directed.target ≠ current.mate ∧
      state.core.marks[directed.target]? = some (some markedAge) ∧
      tagHistory.RawMarked markedAge directed.target ∧
      state.core.representative markedAge = input.rawAge ∧
      ∃ targetConsumer : ConnectiveBelow certificate directed.target,
        targetConsumer.mate ≠ input.vertex ∧
        directed.source = targetConsumer.conclusion ∧
        targetConsumer.conclusion ∉ owned ∧
        ((∃ terminal, MarkedConclusionChain certificate state directed.target terminal ∧
            ∃ terminalConsumer : ConnectiveBelow certificate terminal,
              state.core.marks[terminalConsumer.mate]? = some none ∧
              terminalConsumer.mate ∉ owned) ∨
          (MarkedConclusionChainFirstCausalDescent certificate state tagHistory
              directed.target current.mate input.rawAge ∧
            ∃ (consumer : ConnectiveBelow certificate directed.target)
                (mateAge : RawTokenAge),
              tagHistory.RawMarkedBefore mateAge consumer.mate outerAge current.mate ∧
              ContinuationExitRawOrFutureActiveCarrierExternalCommitmentReentryQueueStatusOutcome
                  certificate state tagHistory input component owned current
                    consumer.conclusion ∧
              MarkedConclusionRawReturnCyclicJunctionCausalOutcome certificate state
                tagHistory current.mate consumer.conclusion outerAge) ∨
          (∃ terminal, MarkedConclusionChain certificate state directed.target terminal ∧
            ∃ terminalConsumer : ConnectiveBelow certificate terminal, ∃ boundary,
              FutureWorkAt state boundary terminalConsumer.conclusion ∧
              terminalConsumer.conclusion ∉ owned ∧ boundary < input.rawAge) ∨
          ∃ terminal, MarkedConclusionChain certificate state directed.target terminal ∧
            ∃ terminalConsumer : ConnectiveBelow certificate terminal, ∃ conclusionAge,
              state.core.marks[terminalConsumer.conclusion]? = some (some conclusionAge) ∧
              terminalConsumer.conclusion ∈ certificate.conclusions ∧
              terminalConsumer.conclusion ∉ owned ∧
              state.core.representative conclusionAge < input.rawAge)

namespace
  ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitWaitingTemporalTarget

/-- Refine only the nested causal continuation outcome and copy the remaining
waiting sibling-exit evidence exactly. -/
theorem queueStatusTarget
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {usedLinks owned : List Nat}
    {current : ConnectiveBelow certificate input.vertex}
    (target :
      ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitWaitingTemporalTarget
        tagHistory input component owned current)
    (invariant : SchedulerInvariant certificate state)
    (componentLookup : state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component usedLinks owned)
    (noTail : ¬ ∃ pending,
      pending ∈ input.readyTail ∧ pending ∉ certificate.conclusions) :
    ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitWaitingQueueStatusTarget
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
      ⟨descent, consumer, mateAge, mateBeforeOuter, siblingOutcome, causalOutcome⟩
    exact Or.inr (Or.inl ⟨descent, consumer, mateAge, mateBeforeOuter,
      siblingOutcome.queueStatusOutcome invariant componentLookup occurrence noTail,
      causalOutcome⟩)
  · exact Or.inr (Or.inr (Or.inl future))
  · exact Or.inr (Or.inr (Or.inr marked))

end
  ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitWaitingTemporalTarget
end SequentialFigure7
end ProofNetIR
