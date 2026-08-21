/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import
  ProofNetIR.SequentialFigure7MarkedTargetWaitingMateExternalCommitmentReentryTemporal
import ProofNetIR.SequentialFigure7WaitingReentryContinuationOuterQueueStatus

/-!
# Marked waiting-target external re-entry: queue status

This module transports the waiting-parent queue-status target through the
two temporal endpoint constructors. It preserves every older-work, marking,
commitment-split, crossing, and re-entry receipt verbatim.

The transport changes only the outer carrier's nested target field. Its final
queue-status step refines that target's raw-unmarked mate leaf. It neither
aligns the target's internal path with the endpoint crossing nor supplies
elimination, payer, progress, completion, termination, or totality evidence.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerBridge

/-- The exact two-case waiting-parent endpoint whose nested marked target now
classifies its remaining raw-unmarked mate by current scheduler status. -/
inductive ActiveMateWaitingParentExternalCommitmentReentryQueueStatusOutcome
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (input : ReadyHeadInput state) (component : UnificationComponent)
    (owned : List Vertex) (current : ConnectiveBelow certificate input.vertex)
    {terminal : Vertex} (consumer : ConnectiveBelow certificate terminal) : Prop where
  | olderFuture
      (boundary : RawTokenAge)
      (work : FutureWorkAt state boundary consumer.conclusion)
      (older : boundary < input.rawAge)
      (outside : consumer.conclusion ∉ owned)
      (commitmentSplit :
        tagHistory.StrictOlderCommitmentSplit boundary input.rawAge)
      (crossing :
        ActiveCarrierExternalEndpointCrossing certificate owned
          consumer.conclusion)
      (reentry :
        ActiveCarrierExternalEndpointReentry certificate owned
          consumer.conclusion)
      (queueStatusTarget :
        ActiveCarrierExternalReentryMarkedOuterMateSeparatedWaitingParentQueueStatusTarget
          tagHistory input component owned consumer.conclusion current) :
      ActiveMateWaitingParentExternalCommitmentReentryQueueStatusOutcome
        tagHistory input component owned current consumer
  | olderMarked
      (conclusionAge : RawTokenAge)
      (marked :
        state.core.marks[consumer.conclusion]? = some (some conclusionAge))
      (olderRepresentative :
        state.core.representative conclusionAge < input.rawAge)
      (outside : consumer.conclusion ∉ owned)
      (commitmentSplit : tagHistory.StrictOlderCommitmentSplit
        (state.core.representative conclusionAge) input.rawAge)
      (crossing :
        ActiveCarrierExternalEndpointCrossing certificate owned
          consumer.conclusion)
      (reentry :
        ActiveCarrierExternalEndpointReentry certificate owned
          consumer.conclusion)
      (queueStatusTarget :
        ActiveCarrierExternalReentryMarkedOuterMateSeparatedWaitingParentQueueStatusTarget
          tagHistory input component owned consumer.conclusion current) :
      ActiveMateWaitingParentExternalCommitmentReentryQueueStatusOutcome
        tagHistory input component owned current consumer

namespace ActiveMateWaitingParentExternalCommitmentReentryTemporalOutcome

/-- Refine the nested temporal target in either endpoint constructor through
its continuation exit, exact waiting parent, and current queue status. -/
theorem queueStatusOutcome
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {usedLinks owned : List Nat}
    {current : ConnectiveBelow certificate input.vertex}
    {terminal : Vertex} {consumer : ConnectiveBelow certificate terminal}
    (outcome :
      ActiveMateWaitingParentExternalCommitmentReentryTemporalOutcome tagHistory
        input component owned current consumer)
    (invariant : SchedulerInvariant certificate state)
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component
        usedLinks owned)
    (noTail :
      ¬ ∃ pending,
        pending ∈ input.readyTail ∧ pending ∉ certificate.conclusions) :
    ActiveMateWaitingParentExternalCommitmentReentryQueueStatusOutcome
      tagHistory input component owned current consumer := by
  cases outcome with
  | olderFuture boundary work older outside commitmentSplit crossing reentry
      temporalTarget =>
      have continuationTarget :=
        temporalTarget.continuationExitTarget invariant current componentLookup
          occurrence noTail
      have waitingTarget :=
        continuationTarget.waitingParentTarget invariant componentLookup occurrence
      exact .olderFuture boundary work older outside commitmentSplit crossing
        reentry
        (waitingTarget.queueStatusTarget invariant componentLookup occurrence)
  | olderMarked conclusionAge marked olderRepresentative outside
      commitmentSplit crossing reentry temporalTarget =>
      have continuationTarget :=
        temporalTarget.continuationExitTarget invariant current componentLookup
          occurrence noTail
      have waitingTarget :=
        continuationTarget.waitingParentTarget invariant componentLookup occurrence
      exact .olderMarked conclusionAge marked olderRepresentative outside
        commitmentSplit crossing reentry
        (waitingTarget.queueStatusTarget invariant componentLookup occurrence)

end ActiveMateWaitingParentExternalCommitmentReentryTemporalOutcome
end SequentialFigure7
end ProofNetIR
