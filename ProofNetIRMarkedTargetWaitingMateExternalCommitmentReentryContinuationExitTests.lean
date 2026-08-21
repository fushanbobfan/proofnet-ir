/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7MarkedTargetWaitingMateExternalCommitmentReentryContinuationExit

/-!
# Figure-7 waiting re-entry continuation-exit consumer

Consumes both public declarations in the endpoint-parametric continuation-exit
checkpoint. The normalized target is reconstructed branch by branch, the
refinement theorem is invoked directly, and the fixed-mate specialization is
checked definitionally.
-/

namespace ProofNetIRMarkedTargetWaitingMateExternalCommitmentReentryContinuationExitTests

open ProofNetIR
open ProofNetIR.SequentialSchedulerState
open ProofNetIR.SequentialSchedulerBridge
open ProofNetIR.SequentialFigure7

example {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {owned : List Vertex} {endpoint : Vertex}
    {current : ConnectiveBelow certificate input.vertex}
    (target :
      ActiveCarrierExternalReentryMarkedOuterMateSeparatedContinuationExitTarget
        tagHistory input component owned endpoint current) :
    ActiveCarrierExternalReentryMarkedOuterMateSeparatedContinuationExitTarget
      tagHistory input component owned endpoint current := by
  rcases target with
    ⟨path, directed, markedAge, pathStarts, finishOwned, directedMembership,
      parentEdge, targetNeSelected, targetNeMate, targetMarked, authentic,
      representativeEq, targetConsumer, targetConsumerMateNeSelected,
      sourceConsumer, targetConclusionOutside, raw | future | marked⟩
  · rcases raw with
      ⟨terminal, chain, terminalConsumer, mateUnmarked,
        mateOutside | selectedReturn⟩
    · exact ⟨path, directed, markedAge, pathStarts, finishOwned,
        directedMembership, parentEdge, targetNeSelected, targetNeMate,
        targetMarked, authentic, representativeEq, targetConsumer,
        targetConsumerMateNeSelected, sourceConsumer, targetConclusionOutside,
        Or.inl ⟨terminal, chain, terminalConsumer, mateUnmarked,
          Or.inl mateOutside⟩⟩
    · exact ⟨path, directed, markedAge, pathStarts, finishOwned,
        directedMembership, parentEdge, targetNeSelected, targetNeMate,
        targetMarked, authentic, representativeEq, targetConsumer,
        targetConsumerMateNeSelected, sourceConsumer, targetConclusionOutside,
        Or.inl ⟨terminal, chain, terminalConsumer, mateUnmarked,
          Or.inr selectedReturn⟩⟩
  · rcases future with
      ⟨terminal, chain, terminalConsumer, boundary, work, conclusionOutside,
        older⟩
    exact ⟨path, directed, markedAge, pathStarts, finishOwned,
      directedMembership, parentEdge, targetNeSelected, targetNeMate,
      targetMarked, authentic, representativeEq, targetConsumer,
      targetConsumerMateNeSelected, sourceConsumer, targetConclusionOutside,
      Or.inr (Or.inl ⟨terminal, chain, terminalConsumer, boundary, work,
        conclusionOutside, older⟩)⟩
  · rcases marked with
      ⟨terminal, chain, terminalConsumer, conclusionAge, conclusionMarked,
        conclusionGlobal, conclusionOutside, older⟩
    exact ⟨path, directed, markedAge, pathStarts, finishOwned,
      directedMembership, parentEdge, targetNeSelected, targetNeMate,
      targetMarked, authentic, representativeEq, targetConsumer,
      targetConsumerMateNeSelected, sourceConsumer, targetConclusionOutside,
      Or.inr (Or.inr ⟨terminal, chain, terminalConsumer, conclusionAge,
        conclusionMarked, conclusionGlobal, conclusionOutside, older⟩)⟩

example {certificate : Certificate} {state : ReservationState}
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
    (target :
      ActiveCarrierExternalReentryMarkedOuterMateSeparatedTemporalTarget
        tagHistory input component owned endpoint current)
    (noTail :
      ¬ ∃ pending,
        pending ∈ input.readyTail ∧ pending ∉ certificate.conclusions) :
    ActiveCarrierExternalReentryMarkedOuterMateSeparatedContinuationExitTarget
      tagHistory input component owned endpoint current := by
  exact target.continuationExitTarget invariant current componentLookup
    occurrence noTail

example {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (input : ReadyHeadInput state) (component : UnificationComponent)
    (owned : List Vertex)
    (current : ConnectiveBelow certificate input.vertex) :
    ActiveCarrierExternalReentryMarkedOuterMateSeparatedContinuationExitTarget
        tagHistory input component owned current.mate current ↔
      ActiveCarrierExternalReentryMarkedMateSeparatedContinuationExitTarget
        tagHistory input component owned current := by
  rfl

#print axioms
  ActiveCarrierExternalReentryMarkedOuterMateSeparatedTemporalTarget.continuationExitTarget

end ProofNetIRMarkedTargetWaitingMateExternalCommitmentReentryContinuationExitTests

def main : IO Unit :=
  IO.println "Figure-7 waiting re-entry continuation exit: kernel-green"
