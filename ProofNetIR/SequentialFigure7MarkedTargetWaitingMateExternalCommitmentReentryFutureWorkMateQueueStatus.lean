/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import
  ProofNetIR.SequentialFigure7MarkedTargetWaitingMateExternalCommitmentReentryTemporal
import
  ProofNetIR.SequentialFigure7MarkedTargetWaitingMateExternalCommitmentReentryQueueStatus

/-!
# Future-work mate external re-entry: queue status

This module lifts the endpoint queue-status outcome through the two-branch
future-work mate status. The older-outside branch is copied verbatim. In the
active-owned branch, only the external endpoint field changes.

The transport does not identify scheduler, endpoint, or nested queue boundaries
and supplies no elimination, payer, progress, completion, or totality result.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerBridge

/-- The future-work mate split whose active external endpoint now classifies
the remaining raw-unmarked mate by current scheduler status. -/
inductive FutureWorkMateActiveCarrierExternalCommitmentReentryQueueStatus
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (input : ReadyHeadInput state) (component : UnificationComponent)
    (owned : List Vertex) (current : ConnectiveBelow certificate input.vertex)
    (terminal : Vertex) (consumer : ConnectiveBelow certificate terminal)
    (boundary mateAge : RawTokenAge) : Prop where
  | olderOutside
      (notMembership : consumer.mate ∉ owned)
      (representativeOlder :
        state.core.representative mateAge < input.rawAge) :
      FutureWorkMateActiveCarrierExternalCommitmentReentryQueueStatus
        tagHistory input component owned current terminal consumer boundary mateAge
  | activeExternal
      (membership : consumer.mate ∈ owned)
      (representative :
        state.core.representative mateAge = input.rawAge)
      (waiting :
        FutureWorkActiveMateWaitingOutcome certificate state input terminal
          consumer boundary)
      (external :
        ActiveMateWaitingParentExternalCommitmentReentryQueueStatusOutcome
          tagHistory input component owned current consumer) :
      FutureWorkMateActiveCarrierExternalCommitmentReentryQueueStatus
        tagHistory input component owned current terminal consumer boundary mateAge

namespace FutureWorkMateActiveCarrierExternalCommitmentReentryTemporalStatus

/-- Refine only the active branch's external endpoint while preserving every
future-work mate status field. -/
theorem queueStatus
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {usedLinks owned : List Nat}
    {current : ConnectiveBelow certificate input.vertex}
    {terminal : Vertex} {consumer : ConnectiveBelow certificate terminal}
    {boundary mateAge : RawTokenAge}
    (status :
      FutureWorkMateActiveCarrierExternalCommitmentReentryTemporalStatus
        tagHistory input component owned current terminal consumer boundary mateAge)
    (invariant : SchedulerInvariant certificate state)
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component
        usedLinks owned)
    (noTail :
      ¬ ∃ pending,
        pending ∈ input.readyTail ∧ pending ∉ certificate.conclusions) :
    FutureWorkMateActiveCarrierExternalCommitmentReentryQueueStatus
      tagHistory input component owned current terminal consumer boundary mateAge := by
  cases status with
  | olderOutside notMembership representativeOlder =>
      exact .olderOutside notMembership representativeOlder
  | activeExternal membership representative waiting external =>
      exact .activeExternal membership representative waiting
        (external.queueStatusOutcome invariant componentLookup occurrence noTail)

end FutureWorkMateActiveCarrierExternalCommitmentReentryTemporalStatus
end SequentialFigure7
end ProofNetIR
