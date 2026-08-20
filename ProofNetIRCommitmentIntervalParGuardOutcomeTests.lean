/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7CommitmentIntervalParGuardOutcome

/-!
# Figure-7 commitment-interval par-guard outcome consumer

The consumer invokes both typed-step theorems, reconstructs every common
interval branch, and destructs the exact Nop and Wait older-mate statuses.
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

private theorem Consumer.nop
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
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
          before.core.marks[step.consumer.mate]? = some none) := by
  apply Consumer.observe
    (consumeStatus := fun status => by
      rcases status with ⟨outside, unmarked⟩
      exact ⟨outside, unmarked⟩)
  exact step.commitmentInterval_parTraceOutcome tagHistory invariant
    componentLookup occurrence positive firstAt lastAt

private theorem Consumer.wait
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
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
            step.prepared.stackResult.rawAge) := by
  apply Consumer.observe
    (consumeStatus := fun status => by
      rcases status with ⟨outside, marked, older⟩
      exact ⟨outside, marked, older⟩)
  exact step.commitmentInterval_parTraceOutcome tagHistory invariant
    componentLookup occurrence positive firstAt lastAt

#print axioms CanonicalTagHistory.CommitmentIntervalParTraceOutcome
#print axioms NopStep.commitmentInterval_parTraceOutcome
#print axioms WaitStep.commitmentInterval_parTraceOutcome

end SequentialFigure7
end ProofNetIR

def main : IO Unit :=
  IO.println "Figure-7 commitment-interval par-guard outcome: kernel-green"
