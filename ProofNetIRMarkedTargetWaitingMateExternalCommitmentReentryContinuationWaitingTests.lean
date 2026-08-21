/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import
  ProofNetIR.SequentialFigure7MarkedTargetWaitingMateExternalCommitmentReentryContinuationWaiting

/-!
# Figure-7 waiting re-entry continuation-waiting consumer

Reconstructs both public target definitions and invokes the ownership-based
continuation refinement directly.
-/

namespace ProofNetIRMarkedTargetWaitingMateExternalCommitmentReentryContinuationWaitingTests

open ProofNetIR
open ProofNetIR.SequentialSchedulerState
open ProofNetIR.SequentialSchedulerBridge
open ProofNetIR.SequentialFigure7

example {certificate : Certificate} {state : ReservationState}
    {boundary : RawTokenAge} {vertex : Vertex}
    (location :
      FutureWorkAtExactWaitingLocation certificate state boundary vertex) :
    FutureWorkAtExactWaitingLocation certificate state boundary vertex := by
  rcases location with
    ⟨payload, linkIndex, left, right, olderPremise, youngerPremise,
      olderAge, youngerAge, youngerBoundary, waitingAt, member, linkLookup,
      sourceLookup, unmarked, orientation, olderMarked, youngerMarked,
      olderBoundary, youngerBoundaryLookup, boundaryLt⟩
  exact ⟨payload, linkIndex, left, right, olderPremise, youngerPremise,
    olderAge, youngerAge, youngerBoundary, waitingAt, member, linkLookup,
    sourceLookup, unmarked, orientation, olderMarked, youngerMarked,
    olderBoundary, youngerBoundaryLookup, boundaryLt⟩

example {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {owned : List Vertex} {endpoint : Vertex}
    {current : ConnectiveBelow certificate input.vertex}
    (target :
      ActiveCarrierExternalReentryMarkedOuterMateSeparatedWaitingParentTarget
        tagHistory input component owned endpoint current) :
    ActiveCarrierExternalReentryMarkedOuterMateSeparatedWaitingParentTarget
      tagHistory input component owned endpoint current := by
  rcases target with
    ⟨path, directed, markedAge, pathStarts, finishOwned, directedMembership,
      parentEdge, targetNeSelected, targetNeMate, targetMarked, authentic,
      representativeEq, targetConsumer, targetConsumerMateNeSelected,
      sourceConsumer, targetConclusionOutside, raw | waiting⟩
  · exact ⟨path, directed, markedAge, pathStarts, finishOwned,
      directedMembership, parentEdge, targetNeSelected, targetNeMate,
      targetMarked, authentic, representativeEq, targetConsumer,
      targetConsumerMateNeSelected, sourceConsumer, targetConclusionOutside,
      Or.inl raw⟩
  · rcases waiting with ⟨boundary, work, older, location⟩
    exact ⟨path, directed, markedAge, pathStarts, finishOwned,
      directedMembership, parentEdge, targetNeSelected, targetNeMate,
      targetMarked, authentic, representativeEq, targetConsumer,
      targetConsumerMateNeSelected, sourceConsumer, targetConclusionOutside,
      Or.inr ⟨boundary, work, older, location⟩⟩

example {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {usedLinks owned : List Nat} {endpoint : Vertex}
    (invariant : SchedulerInvariant certificate state)
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component
        usedLinks owned)
    {current : ConnectiveBelow certificate input.vertex}
    (target :
      ActiveCarrierExternalReentryMarkedOuterMateSeparatedContinuationExitTarget
        tagHistory input component owned endpoint current) :
    ActiveCarrierExternalReentryMarkedOuterMateSeparatedWaitingParentTarget
      tagHistory input component owned endpoint current := by
  exact target.waitingParentTarget invariant componentLookup occurrence

#print axioms
  ActiveCarrierExternalReentryMarkedOuterMateSeparatedContinuationExitTarget.waitingParentTarget

end ProofNetIRMarkedTargetWaitingMateExternalCommitmentReentryContinuationWaitingTests

def main : IO Unit :=
  IO.println "Figure-7 waiting re-entry continuation waiting parent: kernel-green"
