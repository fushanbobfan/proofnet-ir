/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7CommitmentIntervalParGuardReentryMarkedTargetTemporal

/-!
# Consumer for marked re-entry target temporal reduction

This consumer destructs the target-bound temporal trichotomy, invokes the
generic reduction and both typed wrappers, and audits their kernel axioms.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerBridge
open SequentialSchedulerState

private theorem observeTemporalTarget
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {owned : List Vertex}
    {current : ConnectiveBelow certificate input.vertex}
    (target :
      ActiveCarrierExternalReentryMarkedMateSeparatedTemporalTarget tagHistory
        input component owned current) :
    ActiveCarrierExternalReentryMarkedMateSeparatedTemporalTarget tagHistory
      input component owned current := by
  rcases target with
    ⟨path, directed, markedAge, pathStarts, finishOwned, directedMembership,
      parentEdge, targetNeSelected, targetNeMate, targetMarked, authentic,
      representativeEq, targetConsumer, mateNeSelected, sourceConsumer,
      conclusionOutside, raw | future | marked⟩
  · rcases raw with ⟨mateUnmarked, mateOutside⟩
    exact ⟨path, directed, markedAge, pathStarts, finishOwned,
      directedMembership, parentEdge, targetNeSelected, targetNeMate,
      targetMarked, authentic, representativeEq, targetConsumer,
      mateNeSelected, sourceConsumer, conclusionOutside,
      Or.inl ⟨mateUnmarked, mateOutside⟩⟩
  · rcases future with ⟨boundary, work, older⟩
    exact ⟨path, directed, markedAge, pathStarts, finishOwned,
      directedMembership, parentEdge, targetNeSelected, targetNeMate,
      targetMarked, authentic, representativeEq, targetConsumer,
      mateNeSelected, sourceConsumer, conclusionOutside,
      Or.inr (Or.inl ⟨boundary, work, older⟩)⟩
  · rcases marked with ⟨conclusionAge, conclusionMarked, older⟩
    exact ⟨path, directed, markedAge, pathStarts, finishOwned,
      directedMembership, parentEdge, targetNeSelected, targetNeMate,
      targetMarked, authentic, representativeEq, targetConsumer,
      mateNeSelected, sourceConsumer, conclusionOutside,
      Or.inr (Or.inr ⟨conclusionAge, conclusionMarked, older⟩)⟩

private theorem useGeneric
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {usedLinks owned : List Nat}
    (invariant : SchedulerInvariant certificate state)
    (current : ConnectiveBelow certificate input.vertex)
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component
        usedLinks owned)
    (target :
      ActiveCarrierExternalReentryMarkedMateSeparatedTarget tagHistory input
        component owned current)
    (noTail :
      ¬ ∃ pending,
        pending ∈ input.readyTail ∧ pending ∉ certificate.conclusions) :
    ActiveCarrierExternalReentryMarkedMateSeparatedTemporalTarget tagHistory
      input component owned current := by
  exact observeTemporalTarget
    (target.temporalTarget invariant current componentLookup occurrence noTail)

private theorem useNop
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
          ActiveCarrierExternalReentryMarkedMateSeparatedTemporalTarget
            tagHistory step.prepared.readyHeadInput component owned
              step.consumer) := by
  exact step.commitmentInterval_parTraceReentryMarkedTemporalOutcome connected
    tagHistory invariant componentLookup occurrence positive firstAt lastAt
    noTail

private theorem useWait
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
          ActiveCarrierExternalReentryMarkedMateSeparatedTemporalTarget
            tagHistory step.prepared.readyHeadInput component owned
              step.consumer) := by
  exact step.commitmentInterval_parTraceReentryMarkedTemporalOutcome connected
    tagHistory invariant componentLookup occurrence positive firstAt lastAt
    noTail

#print axioms
  ActiveCarrierExternalReentryMarkedMateSeparatedTarget.temporalTarget
#print axioms
  NopStep.commitmentInterval_parTraceReentryMarkedTemporalOutcome
#print axioms
  WaitStep.commitmentInterval_parTraceReentryMarkedTemporalOutcome

end SequentialFigure7
end ProofNetIR

def main : IO Unit :=
  IO.println "Figure-7 marked re-entry target temporal reduction: kernel-green"
