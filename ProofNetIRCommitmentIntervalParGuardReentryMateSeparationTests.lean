/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7CommitmentIntervalParGuardReentryMateSeparation

/-!
# Figure-7 commitment-interval par-guard re-entry mate-separation consumer

Exercises the generic mate-separation theorem and both typed interval wrappers,
destructs every field of the public carrier, and audits the three public theorem
dependencies. The test imports only the production owner module.
-/

namespace ProofNetIR
namespace SequentialFigure7
namespace Consumer

open SequentialSchedulerState
open SequentialSchedulerBridge

private theorem separatedTargetRoundTrip
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {owned : List Vertex}
    {current : ConnectiveBelow certificate input.vertex}
    (target :
      ActiveCarrierExternalReentryMarkedMateSeparatedTarget tagHistory input
        component owned current) :
    ActiveCarrierExternalReentryMarkedMateSeparatedTarget tagHistory input
      component owned current := by
  rcases target with
    ⟨path, directed, markedAge, pathStarts, finishOwned, directedMembership,
      parentEdge, targetNeSelected, targetNeMate, targetMarked, authentic,
      representativeEq, targetConsumerMateNeSelected⟩
  exact ⟨path, directed, markedAge, pathStarts, finishOwned,
    directedMembership, parentEdge, targetNeSelected, targetNeMate,
    targetMarked, authentic, representativeEq, targetConsumerMateNeSelected⟩

private example
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {owned : List Vertex}
    (structural : certificate.StructurallyWellFormed)
    (current : ConnectiveBelow certificate input.vertex)
    (target :
      ActiveCarrierExternalReentryMarkedHistoricalTarget tagHistory input
        component owned current.mate) :
    ActiveCarrierExternalReentryMarkedMateSeparatedTarget tagHistory input
      component owned current := by
  exact separatedTargetRoundTrip
    (target.mateSeparated structural current)

private example
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    (connected : certificate.ReferenceSwitchingConnected)
    (tagHistory : CanonicalTagHistory certificate history)
    (invariant : SchedulerInvariant certificate before)
    (step : NopStep certificate before after)
    {component : UnificationComponent} {usedLinks owned : List Nat}
    (componentLookup :
      before.core.components[step.prepared.stackResult.rawAge]? =
        some (some component))
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component
        usedLinks owned)
    {position edgeCount : Nat} {first : RawTokenAge}
    (positive : 0 < edgeCount)
    (firstAt : before.stack.sigma[position]? = some first)
    (lastAt :
      before.stack.sigma[position + edgeCount]? =
        some step.prepared.stackResult.rawAge)
    (noTail :
      ¬ ∃ pending,
        pending ∈ step.prepared.stackResult.remainingTop ∧
          pending ∉ certificate.conclusions) :
    tagHistory.CommitmentIntervalParTraceOutcome
      step.prepared.readyHeadInput step.consumer position edgeCount first
        (step.consumer.mate ∉ owned ∧
          before.core.marks[step.consumer.mate]? = some none ∧
          ActiveCarrierExternalReentryMarkedMateSeparatedTarget tagHistory
            step.prepared.readyHeadInput component owned step.consumer) := by
  exact step.commitmentInterval_parTraceReentryMateSeparatedOutcome connected
    tagHistory invariant componentLookup occurrence positive firstAt lastAt
    noTail

private example
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    (connected : certificate.ReferenceSwitchingConnected)
    (tagHistory : CanonicalTagHistory certificate history)
    (invariant : SchedulerInvariant certificate before)
    (step : WaitStep certificate before after)
    {component : UnificationComponent} {usedLinks owned : List Nat}
    (componentLookup :
      before.core.components[step.prepared.stackResult.rawAge]? =
        some (some component))
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component
        usedLinks owned)
    {position edgeCount : Nat} {first : RawTokenAge}
    (positive : 0 < edgeCount)
    (firstAt : before.stack.sigma[position]? = some first)
    (lastAt :
      before.stack.sigma[position + edgeCount]? =
        some step.prepared.stackResult.rawAge)
    (noTail :
      ¬ ∃ pending,
        pending ∈ step.prepared.stackResult.remainingTop ∧
          pending ∉ certificate.conclusions) :
    tagHistory.CommitmentIntervalParTraceOutcome
      step.prepared.readyHeadInput step.consumer position edgeCount first
        (step.consumer.mate ∉ owned ∧
          before.core.marks[step.consumer.mate]? =
            some (some step.mateRawAge) ∧
          before.core.representative step.mateRawAge <
            step.prepared.stackResult.rawAge ∧
          ActiveCarrierExternalReentryMarkedMateSeparatedTarget tagHistory
            step.prepared.readyHeadInput component owned step.consumer) := by
  exact step.commitmentInterval_parTraceReentryMateSeparatedOutcome connected
    tagHistory invariant componentLookup occurrence positive firstAt lastAt
    noTail

#print axioms ActiveCarrierExternalReentryMarkedHistoricalTarget.mateSeparated
#print axioms NopStep.commitmentInterval_parTraceReentryMateSeparatedOutcome
#print axioms WaitStep.commitmentInterval_parTraceReentryMateSeparatedOutcome

end Consumer
end SequentialFigure7
end ProofNetIR

def main : IO Unit :=
  IO.println "Figure-7 par-guard re-entry mate separation: kernel-green"
