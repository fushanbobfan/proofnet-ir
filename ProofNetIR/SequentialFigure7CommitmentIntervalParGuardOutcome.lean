/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7CommitmentIntervalParTraceLocalization
import ProofNetIR.SequentialFigure7PriorityEnabled

/-!
# Figure-7 commitment-interval par-guard outcome

Specializes the localized positive commitment-interval dichotomy to actual
Nop and Wait guards. The remaining strictly older stored-right mate is exactly
an external raw endpoint for Nop and an external marked endpoint with a
strictly older representative for Wait.

Equal-final selected/mate traces and the inclusive outer split remain. This
module does not derive a ready-tail payer, the history-tail law, or progress.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerBridge
open SequentialSchedulerState

namespace CanonicalTagHistory

/-- A positive commitment-interval par classification whose strictly older
mate branch carries a caller-selected exact status. -/
inductive CommitmentIntervalParTraceOutcome
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (input : ReadyHeadInput state)
    (consumer : ConnectiveBelow certificate input.vertex)
    (position edgeCount : Nat) (first : RawTokenAge)
    (olderMateStatus : Prop) : Prop where
  | avoiding
      (path :
        tagHistory.CommitmentEdgeTargetAvoidingPath first input.rawAge
          consumer.conclusion) :
      tagHistory.CommitmentIntervalParTraceOutcome input consumer position
        edgeCount first olderMateStatus
  | equalSelected
      (offset : Nat) (parent child : RawTokenAge)
      (event : ReservationEvent certificate)
      (offset_lt : offset < edgeCount)
      (parent_at :
        state.stack.sigma[position + offset]? = some parent)
      (child_at :
        state.stack.sigma[position + offset + 1]? = some child)
      (not_avoiding :
        ¬ tagHistory.CommitmentEdgeTargetAvoidingPath parent child
          consumer.conclusion)
      (event_mem : event ∈ tagHistory.reservationLedger)
      (event_age : event.rawAge = child)
      (child_eq : child = input.rawAge)
      (side : consumer.side = .storedLeft)
      (beforeTrace afterTrace : List Vertex)
      (trace :
        event.search.result.trace =
          beforeTrace ++ consumer.conclusion :: input.vertex :: afterTrace) :
      tagHistory.CommitmentIntervalParTraceOutcome input consumer position
        edgeCount first olderMateStatus
  | equalMate
      (offset : Nat) (parent child : RawTokenAge)
      (event : ReservationEvent certificate)
      (offset_lt : offset < edgeCount)
      (parent_at :
        state.stack.sigma[position + offset]? = some parent)
      (child_at :
        state.stack.sigma[position + offset + 1]? = some child)
      (not_avoiding :
        ¬ tagHistory.CommitmentEdgeTargetAvoidingPath parent child
          consumer.conclusion)
      (event_mem : event ∈ tagHistory.reservationLedger)
      (event_age : event.rawAge = child)
      (child_eq : child = input.rawAge)
      (side : consumer.side = .storedRight)
      (beforeTrace afterTrace : List Vertex)
      (trace :
        event.search.result.trace =
          beforeTrace ++ consumer.conclusion :: consumer.mate :: afterTrace) :
      tagHistory.CommitmentIntervalParTraceOutcome input consumer position
        edgeCount first olderMateStatus
  | olderMate
      (offset : Nat) (parent child : RawTokenAge)
      (event : ReservationEvent certificate)
      (offset_lt : offset < edgeCount)
      (parent_at :
        state.stack.sigma[position + offset]? = some parent)
      (child_at :
        state.stack.sigma[position + offset + 1]? = some child)
      (not_avoiding :
        ¬ tagHistory.CommitmentEdgeTargetAvoidingPath parent child
          consumer.conclusion)
      (event_mem : event ∈ tagHistory.reservationLedger)
      (event_age : event.rawAge = child)
      (child_lt : child < input.rawAge)
      (side : consumer.side = .storedRight)
      (beforeTrace afterTrace : List Vertex)
      (trace :
        event.search.result.trace =
          beforeTrace ++ consumer.conclusion :: consumer.mate :: afterTrace)
      (status : olderMateStatus) :
      tagHistory.CommitmentIntervalParTraceOutcome input consumer position
        edgeCount first olderMateStatus

end CanonicalTagHistory

/-- For Nop, a strictly older failed interval trace ends at an unmarked raw
mate outside the active occurrence carrier. -/
theorem NopStep.commitmentInterval_parTraceOutcome
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
  rcases tagHistory.commitmentInterval_parConclusion_localizedDichotomy
      invariant step.prepared.readyHeadInput step.consumer step.par_eq
      componentLookup occurrence positive firstAt lastAt with
    avoiding | obstruction
  · exact .avoiding avoiding
  · rcases obstruction with
      ⟨offset, parent, child, event, offsetLt, parentAt, childAt,
        notAvoiding, membership, eventAge, equalTrace | olderTrace⟩
    · rcases equalTrace with ⟨childEq, selectedTrace | mateTrace⟩
      · rcases selectedTrace with ⟨side, beforeTrace, afterTrace, trace⟩
        exact .equalSelected offset parent child event offsetLt parentAt
          childAt notAvoiding membership eventAge childEq side beforeTrace
          afterTrace trace
      · rcases mateTrace with ⟨side, beforeTrace, afterTrace, trace⟩
        exact .equalMate offset parent child event offsetLt parentAt childAt
          notAvoiding membership eventAge childEq side beforeTrace afterTrace
          trace
    · rcases olderTrace with
        ⟨childOlder, side, mateOutside, beforeTrace, afterTrace, trace⟩
      exact .olderMate offset parent child event offsetLt parentAt childAt
        notAvoiding membership eventAge childOlder side beforeTrace afterTrace
        trace ⟨mateOutside, step.mate_unmarked_before⟩

/-- For Wait, a strictly older failed interval trace ends at an external mate
whose concrete mark has a strictly older representative. -/
theorem WaitStep.commitmentInterval_parTraceOutcome
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
  rcases tagHistory.commitmentInterval_parConclusion_localizedDichotomy
      invariant step.prepared.readyHeadInput step.consumer step.par_eq
      componentLookup occurrence positive firstAt lastAt with
    avoiding | obstruction
  · exact .avoiding avoiding
  · rcases obstruction with
      ⟨offset, parent, child, event, offsetLt, parentAt, childAt,
        notAvoiding, membership, eventAge, equalTrace | olderTrace⟩
    · rcases equalTrace with ⟨childEq, selectedTrace | mateTrace⟩
      · rcases selectedTrace with ⟨side, beforeTrace, afterTrace, trace⟩
        exact .equalSelected offset parent child event offsetLt parentAt
          childAt notAvoiding membership eventAge childEq side beforeTrace
          afterTrace trace
      · rcases mateTrace with ⟨side, beforeTrace, afterTrace, trace⟩
        exact .equalMate offset parent child event offsetLt parentAt childAt
          notAvoiding membership eventAge childEq side beforeTrace afterTrace
          trace
    · rcases olderTrace with
        ⟨childOlder, side, mateOutside, beforeTrace, afterTrace, trace⟩
      have representativeLe :
          before.core.representative step.mateRawAge ≤ step.mateRawAge :=
        UnificationState.OrderedParents.representative_le
          invariant.core_orderedParents step.mateRawAge
      have representativeOlder :
          before.core.representative step.mateRawAge <
            step.prepared.stackResult.rawAge :=
        Nat.lt_of_le_of_lt representativeLe step.younger
      exact .olderMate offset parent child event offsetLt parentAt childAt
        notAvoiding membership eventAge childOlder side beforeTrace afterTrace
        trace ⟨mateOutside, step.mate_marked_before, representativeOlder⟩

end SequentialFigure7
end ProofNetIR
