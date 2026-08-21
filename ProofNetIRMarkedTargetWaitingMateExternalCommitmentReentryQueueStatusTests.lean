/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import
  ProofNetIR.SequentialFigure7MarkedTargetWaitingMateExternalCommitmentReentryQueueStatus

/-!
# Figure-7 waiting-parent external re-entry queue-status consumer

Reconstructs both public endpoint constructors, invokes the queue-status
transport through the public surface, checks its trust boundary, and emits a
kernel-green marker.
-/

namespace
  ProofNetIRMarkedTargetWaitingMateExternalCommitmentReentryQueueStatusTests

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
    (outcome :
      ActiveMateWaitingParentExternalCommitmentReentryQueueStatusOutcome
        tagHistory input component owned current consumer) :
    ActiveMateWaitingParentExternalCommitmentReentryQueueStatusOutcome
      tagHistory input component owned current consumer := by
  cases outcome with
  | olderFuture boundary work older outside commitmentSplit crossing reentry
      queueStatusTarget =>
      exact .olderFuture boundary work older outside commitmentSplit crossing
        reentry queueStatusTarget
  | olderMarked conclusionAge marked olderRepresentative outside
      commitmentSplit crossing reentry queueStatusTarget =>
      exact .olderMarked conclusionAge marked olderRepresentative outside
        commitmentSplit crossing reentry queueStatusTarget

example {certificate : Certificate} {state : ReservationState}
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
  exact outcome.queueStatusOutcome invariant componentLookup occurrence noTail

end
  ProofNetIRMarkedTargetWaitingMateExternalCommitmentReentryQueueStatusTests

namespace ProofNetIR
namespace SequentialFigure7

#print axioms
  ActiveMateWaitingParentExternalCommitmentReentryQueueStatusOutcome

namespace ActiveMateWaitingParentExternalCommitmentReentryTemporalOutcome
#print axioms queueStatusOutcome
end ActiveMateWaitingParentExternalCommitmentReentryTemporalOutcome

end SequentialFigure7
end ProofNetIR

def main : IO Unit :=
  IO.println
    "Figure-7 waiting-parent external re-entry queue status: kernel-green"
