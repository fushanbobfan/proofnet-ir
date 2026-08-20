/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7CommitmentIntervalParGuardReentry

/-!
# Figure-7 commitment-interval par-guard re-entry consumer

The consumer invokes both typed-step theorems, reconstructs every common
interval branch, and destructs the exact external-mate re-entry target status.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerBridge
open SequentialSchedulerState

private theorem Consumer.observe
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state}
    {consumer : ConnectiveBelow certificate input.vertex}
    {position edgeCount : Nat} {first : RawTokenAge}
    {olderMateStatus : Prop}
    (consumeStatus : olderMateStatus → olderMateStatus)
    (outcome :
      tagHistory.CommitmentIntervalParTraceOutcome input consumer position
        edgeCount first olderMateStatus) :
    tagHistory.CommitmentIntervalParTraceOutcome input consumer position
      edgeCount first olderMateStatus := by
  cases outcome with
  | avoiding path =>
      exact .avoiding path
  | equalSelected offset parent child event offsetLt parentAt childAt
      notAvoiding membership eventAge childEq side beforeTrace afterTrace
      trace =>
      exact .equalSelected offset parent child event offsetLt parentAt childAt
        notAvoiding membership eventAge childEq side beforeTrace afterTrace
        trace
  | equalMate offset parent child event offsetLt parentAt childAt notAvoiding
      membership eventAge childEq side beforeTrace afterTrace trace =>
      exact .equalMate offset parent child event offsetLt parentAt childAt
        notAvoiding membership eventAge childEq side beforeTrace afterTrace
        trace
  | olderMate offset parent child event offsetLt parentAt childAt notAvoiding
      membership eventAge childOlder side beforeTrace afterTrace trace status =>
      exact .olderMate offset parent child event offsetLt parentAt childAt
        notAvoiding membership eventAge childOlder side beforeTrace afterTrace
        trace (consumeStatus status)

private theorem Consumer.observeTarget
    {certificate : Certificate} {state : ReservationState}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {owned : List Vertex} {endpoint : Vertex}
    (status : ActiveCarrierExternalReentryTargetStatus certificate state input
      component owned endpoint) :
    ActiveCarrierExternalReentryTargetStatus certificate state input component
      owned endpoint := by
  rcases status with
    ⟨path, directed, pathStarts, finishOwned, directedMem, parentEdge,
      selected | tail | marked⟩
  · rcases parentEdge with
      ⟨linkIndex, kind, storedLeft, storedRight, conclusion, sourceEq,
        targetFrontier, targetNotGlobal, linkLookup, targetPremise,
        conclusionOutside⟩
    exact ⟨path, directed, pathStarts, finishOwned, directedMem,
      ⟨linkIndex, kind, storedLeft, storedRight, conclusion, sourceEq,
        targetFrontier, targetNotGlobal, linkLookup, targetPremise,
        conclusionOutside⟩, Or.inl selected⟩
  · rcases parentEdge with
      ⟨linkIndex, kind, storedLeft, storedRight, conclusion, sourceEq,
        targetFrontier, targetNotGlobal, linkLookup, targetPremise,
        conclusionOutside⟩
    exact ⟨path, directed, pathStarts, finishOwned, directedMem,
      ⟨linkIndex, kind, storedLeft, storedRight, conclusion, sourceEq,
        targetFrontier, targetNotGlobal, linkLookup, targetPremise,
        conclusionOutside⟩, Or.inr (Or.inl tail)⟩
  · rcases parentEdge with
      ⟨linkIndex, kind, storedLeft, storedRight, conclusion, sourceEq,
        targetFrontier, targetNotGlobal, linkLookup, targetPremise,
        conclusionOutside⟩
    exact ⟨path, directed, pathStarts, finishOwned, directedMem,
      ⟨linkIndex, kind, storedLeft, storedRight, conclusion, sourceEq,
        targetFrontier, targetNotGlobal, linkLookup, targetPremise,
        conclusionOutside⟩, Or.inr (Or.inr marked)⟩

private theorem Consumer.nop
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
        some step.prepared.stackResult.rawAge) :
    tagHistory.CommitmentIntervalParTraceOutcome
      step.prepared.readyHeadInput step.consumer position edgeCount first
        (step.consumer.mate ∉ owned ∧
          before.core.marks[step.consumer.mate]? = some none ∧
          ActiveCarrierExternalReentryTargetStatus certificate before
            step.prepared.readyHeadInput component owned step.consumer.mate) := by
  apply Consumer.observe
    (consumeStatus := fun status => by
      rcases status with ⟨outside, unmarked, target⟩
      exact ⟨outside, unmarked, Consumer.observeTarget target⟩)
  exact step.commitmentInterval_parTraceReentryTargetOutcome connected
    tagHistory invariant componentLookup occurrence positive firstAt lastAt

private theorem Consumer.wait
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
        some step.prepared.stackResult.rawAge) :
    tagHistory.CommitmentIntervalParTraceOutcome
      step.prepared.readyHeadInput step.consumer position edgeCount first
        (step.consumer.mate ∉ owned ∧
          before.core.marks[step.consumer.mate]? =
            some (some step.mateRawAge) ∧
          before.core.representative step.mateRawAge <
            step.prepared.stackResult.rawAge ∧
          ActiveCarrierExternalReentryTargetStatus certificate before
            step.prepared.readyHeadInput component owned step.consumer.mate) := by
  apply Consumer.observe
    (consumeStatus := fun status => by
      rcases status with ⟨outside, marked, older, target⟩
      exact ⟨outside, marked, older, Consumer.observeTarget target⟩)
  exact step.commitmentInterval_parTraceReentryTargetOutcome connected
    tagHistory invariant componentLookup occurrence positive firstAt lastAt

#print axioms NopStep.commitmentInterval_parTraceReentryTargetOutcome
#print axioms WaitStep.commitmentInterval_parTraceReentryTargetOutcome

end SequentialFigure7
end ProofNetIR

def main : IO Unit :=
  IO.println "Figure-7 commitment-interval par-guard re-entry: kernel-green"
