/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7MarkedTargetWaitingMateExternalCommitmentReentry

/-!
# Figure-7 active-mate waiting external commitment re-entry consumer

Consumes every public declaration in the waiting-mate external commitment
re-entry checkpoint, reconstructs both exact endpoint cases, and invokes the
failure-conditioned historical refinement.
-/

namespace ProofNetIRMarkedTargetWaitingMateExternalCommitmentReentryTests

open ProofNetIR
open ProofNetIR.SequentialSchedulerState
open ProofNetIR.SequentialSchedulerBridge
open ProofNetIR.SequentialFigure7

example {certificate : Certificate} {owned : List Vertex} {endpoint : Vertex}
    (crossing :
      ActiveCarrierExternalEndpointCrossing certificate owned endpoint) :
    ActiveCarrierExternalEndpointReentry certificate owned endpoint := by
  exact crossing.reentry

example {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {owned : List Vertex} {terminal : Vertex}
    {consumer : ConnectiveBelow certificate terminal}
    (outcome :
      ActiveMateWaitingParentExternalCommitmentReentryFailureOutcome
        tagHistory input component owned consumer) :
    ActiveMateWaitingParentExternalCommitmentReentryFailureOutcome tagHistory
      input component owned consumer := by
  cases outcome with
  | olderFuture boundary work older outside commitmentSplit crossing reentry
      failureStatus =>
      exact .olderFuture boundary work older outside commitmentSplit crossing
        reentry failureStatus
  | olderMarked conclusionAge marked olderRepresentative outside
      commitmentSplit crossing reentry failureStatus =>
      exact .olderMarked conclusionAge marked olderRepresentative outside
        commitmentSplit crossing reentry failureStatus

example {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {usedLinks owned : List Nat}
    {terminal : Vertex} {consumer : ConnectiveBelow certificate terminal}
    (outcome : ActiveMateWaitingParentExternalTemporalOutcome certificate state
      input owned consumer)
    (tagHistory : CanonicalTagHistory certificate history)
    (connected : certificate.ReferenceSwitchingConnected)
    (invariant : SchedulerInvariant certificate state)
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      certificate.ComponentOccurrenceWitness component usedLinks owned)
    (noTail :
      ¬ ∃ pending,
        pending ∈ input.readyTail ∧ pending ∉ certificate.conclusions) :
    ActiveMateWaitingParentExternalCommitmentReentryFailureOutcome tagHistory
      input component owned consumer := by
  exact outcome.commitmentReentryFailureOutcome tagHistory connected invariant
    componentLookup occurrence noTail

#print axioms ActiveCarrierExternalEndpointCrossing.reentry
#print axioms ActiveMateWaitingParentExternalCommitmentReentryFailureOutcome
#print axioms
  ActiveMateWaitingParentExternalTemporalOutcome.commitmentReentryFailureOutcome

end ProofNetIRMarkedTargetWaitingMateExternalCommitmentReentryTests

def main : IO Unit :=
  IO.println "Figure-7 active-mate waiting external commitment re-entry: kernel-green"
