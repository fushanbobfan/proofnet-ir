/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import
  ProofNetIR.SequentialFigure7MarkedTargetWaitingMateExternalCommitmentReentryFutureWorkMateQueueStatus

/-!
# Figure-7 future-work mate queue-status consumer

Reconstructs both public status constructors, invokes the adapter through the
public surface, checks its trust boundary, and emits a kernel-green marker.
-/

namespace
  ProofNetIRMarkedTargetWaitingMateExternalCommitmentReentryFutureWorkMateQueueStatusTests

open ProofNetIR
open ProofNetIR.SequentialSchedulerState
open ProofNetIR.SequentialSchedulerBridge
open ProofNetIR.SequentialFigure7

example {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {owned : List Vertex} {current : ConnectiveBelow certificate input.vertex}
    {terminal : Vertex} {consumer : ConnectiveBelow certificate terminal}
    {boundary mateAge : RawTokenAge}
    (status : FutureWorkMateActiveCarrierExternalCommitmentReentryQueueStatus
      tagHistory input component owned current terminal consumer boundary mateAge) :
    FutureWorkMateActiveCarrierExternalCommitmentReentryQueueStatus
      tagHistory input component owned current terminal consumer boundary mateAge := by
  cases status with
  | olderOutside notMembership representativeOlder =>
      exact .olderOutside notMembership representativeOlder
  | activeExternal membership representative waiting external =>
      exact .activeExternal membership representative waiting external

example {certificate : Certificate} {state : ReservationState}
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
  exact status.queueStatus invariant componentLookup occurrence noTail

end
  ProofNetIRMarkedTargetWaitingMateExternalCommitmentReentryFutureWorkMateQueueStatusTests

namespace ProofNetIR
namespace SequentialFigure7

#print axioms
  FutureWorkMateActiveCarrierExternalCommitmentReentryQueueStatus

namespace FutureWorkMateActiveCarrierExternalCommitmentReentryTemporalStatus
#print axioms queueStatus
end FutureWorkMateActiveCarrierExternalCommitmentReentryTemporalStatus

end SequentialFigure7
end ProofNetIR

def main : IO Unit :=
  IO.println "Figure-7 future-work mate queue status: kernel-green"
