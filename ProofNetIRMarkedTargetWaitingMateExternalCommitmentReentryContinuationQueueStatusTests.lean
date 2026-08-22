/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import
  ProofNetIR.SequentialFigure7MarkedTargetWaitingMateExternalCommitmentReentryContinuationQueueStatus

/-!
# Figure-7 continuation queue-status consumer

Reconstructs all three public outcome constructors, invokes the public adapter,
checks its trust boundary, and emits a kernel-green marker.
-/

namespace
  ProofNetIRMarkedTargetWaitingMateExternalCommitmentReentryContinuationQueueStatusTests

open ProofNetIR
open ProofNetIR.SequentialSchedulerState
open ProofNetIR.SequentialSchedulerBridge
open ProofNetIR.SequentialFigure7

example {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {owned : List Vertex} {current : ConnectiveBelow certificate input.vertex}
    {origin : Vertex}
    (outcome :
      ContinuationExitRawOrFutureActiveCarrierExternalCommitmentReentryQueueStatusOutcome
        certificate state tagHistory input component owned current origin) :
    ContinuationExitRawOrFutureActiveCarrierExternalCommitmentReentryQueueStatusOutcome
      certificate state tagHistory input component owned current origin := by
  cases outcome with
  | rawOutside chain terminalOutside consumer mateUnmarked mateOutside =>
      exact .rawOutside chain terminalOutside consumer mateUnmarked mateOutside
  | rawSelectedReturn chain terminalOutside consumer mateUnmarked mateSelected
      terminalCurrentMate conclusionCurrent =>
      exact .rawSelectedReturn chain terminalOutside consumer mateUnmarked
        mateSelected terminalCurrentMate conclusionCurrent
  | futureOlder chain terminalOutside consumer boundary work conclusionOutside
      boundaryOlder terminalAge mateAge terminalMarked mateMarked terminalEvent
      mateEvent terminalRepresentativeOlder mateStatus premiseOrder location =>
      exact .futureOlder chain terminalOutside consumer boundary work
        conclusionOutside boundaryOlder terminalAge mateAge terminalMarked
        mateMarked terminalEvent mateEvent terminalRepresentativeOlder
        mateStatus premiseOrder location

example {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {usedLinks owned : List Nat}
    {current : ConnectiveBelow certificate input.vertex} {origin : Vertex}
    (outcome :
      ContinuationExitRawOrFutureActiveCarrierExternalCommitmentReentryTemporalOutcome
        certificate state tagHistory input component owned current origin)
    (invariant : SchedulerInvariant certificate state)
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component usedLinks owned)
    (noTail :
      ¬ ∃ pending,
        pending ∈ input.readyTail ∧ pending ∉ certificate.conclusions) :
    ContinuationExitRawOrFutureActiveCarrierExternalCommitmentReentryQueueStatusOutcome
      certificate state tagHistory input component owned current origin := by
  exact outcome.queueStatusOutcome invariant componentLookup occurrence noTail

end
  ProofNetIRMarkedTargetWaitingMateExternalCommitmentReentryContinuationQueueStatusTests

namespace ProofNetIR
namespace SequentialFigure7

#print axioms
  ContinuationExitRawOrFutureActiveCarrierExternalCommitmentReentryQueueStatusOutcome

namespace
  ContinuationExitRawOrFutureActiveCarrierExternalCommitmentReentryTemporalOutcome
#print axioms queueStatusOutcome
end
  ContinuationExitRawOrFutureActiveCarrierExternalCommitmentReentryTemporalOutcome

end SequentialFigure7
end ProofNetIR

def main : IO Unit :=
  IO.println "Figure-7 continuation queue status: kernel-green"
