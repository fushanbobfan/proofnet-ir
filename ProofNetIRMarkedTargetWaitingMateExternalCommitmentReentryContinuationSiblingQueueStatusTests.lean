/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import
  ProofNetIR.SequentialFigure7MarkedTargetWaitingMateExternalCommitmentReentryContinuationSiblingQueueStatus

/-!
# Figure-7 continuation sibling queue-status consumer

Reconstructs the public target, invokes the adapter, checks its trust boundary,
and emits a kernel-green marker.
-/

namespace
  ProofNetIRMarkedTargetWaitingMateExternalCommitmentReentryContinuationSiblingQueueStatusTests

open ProofNetIR
open ProofNetIR.SequentialSchedulerState
open ProofNetIR.SequentialSchedulerBridge
open ProofNetIR.SequentialFigure7

example {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {owned : List Vertex} {current : ConnectiveBelow certificate input.vertex}
    (target :
      ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitWaitingQueueStatusTarget
        tagHistory input component owned current) :
    ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitWaitingQueueStatusTarget
      tagHistory input component owned current := by
  rcases target with
    ⟨outerAge, outerEvent, path, directed, markedAge, pathStart, pathFinish,
      directedMembership, inbound, targetNeSelected, targetNeMate, targetMarked,
      targetEvent, targetRepresentative, targetConsumer, targetMateNeSelected,
      directedSource, conclusionOutside, exit⟩
  exact ⟨outerAge, outerEvent, path, directed, markedAge, pathStart, pathFinish,
    directedMembership, inbound, targetNeSelected, targetNeMate, targetMarked,
    targetEvent, targetRepresentative, targetConsumer, targetMateNeSelected,
    directedSource, conclusionOutside, exit⟩

example {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {usedLinks owned : List Nat}
    {current : ConnectiveBelow certificate input.vertex}
    (target :
      ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitWaitingTemporalTarget
        tagHistory input component owned current)
    (invariant : SchedulerInvariant certificate state)
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component usedLinks owned)
    (noTail :
      ¬ ∃ pending,
        pending ∈ input.readyTail ∧ pending ∉ certificate.conclusions) :
    ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitWaitingQueueStatusTarget
      tagHistory input component owned current := by
  exact target.queueStatusTarget invariant componentLookup occurrence noTail

end
  ProofNetIRMarkedTargetWaitingMateExternalCommitmentReentryContinuationSiblingQueueStatusTests

namespace ProofNetIR
namespace SequentialFigure7

#print axioms
  ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitWaitingQueueStatusTarget
namespace
  ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitWaitingTemporalTarget
#print axioms queueStatusTarget
end
  ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitWaitingTemporalTarget

end SequentialFigure7
end ProofNetIR

def main : IO Unit :=
  IO.println "Figure-7 continuation sibling queue status: kernel-green"
