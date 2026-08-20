/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7CommitmentIntervalParTraceLocalization

/-!
# Figure-7 commitment-interval par-trace localization consumer

The consumer invokes the public localization theorem, reconstructs the path
case, and destructs every field of the equal-boundary and older-external-mate
obstructions.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerBridge
open SequentialSchedulerState

private theorem Consumer.invoke
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (invariant : SchedulerInvariant certificate state)
    (input : ReadyHeadInput state)
    (consumer : ConnectiveBelow certificate input.vertex)
    (parEq : consumer.kind = .par)
    {component : UnificationComponent} {usedLinks owned : List Nat}
    (componentLookup :
      state.core.components[input.rawAge]? = some (some component))
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component
        usedLinks owned)
    {position edgeCount : Nat} {first : RawTokenAge}
    (positive : 0 < edgeCount)
    (firstAt : state.stack.sigma[position]? = some first)
    (lastAt :
      state.stack.sigma[position + edgeCount]? = some input.rawAge) :
    tagHistory.CommitmentEdgeTargetAvoidingPath first input.rawAge
        consumer.conclusion ∨
      ∃ offset parent child event,
        offset < edgeCount ∧
          state.stack.sigma[position + offset]? = some parent ∧
          state.stack.sigma[position + offset + 1]? = some child ∧
          ¬ tagHistory.CommitmentEdgeTargetAvoidingPath parent child
            consumer.conclusion ∧
          event ∈ tagHistory.reservationLedger ∧
          event.rawAge = child ∧
          ((child = input.rawAge ∧
              ((consumer.side = .storedLeft ∧
                  ∃ beforeTrace afterTrace,
                    event.search.result.trace =
                      beforeTrace ++ consumer.conclusion :: input.vertex ::
                        afterTrace) ∨
                (consumer.side = .storedRight ∧
                  ∃ beforeTrace afterTrace,
                    event.search.result.trace =
                      beforeTrace ++ consumer.conclusion :: consumer.mate ::
                        afterTrace))) ∨
            (child < input.rawAge ∧
              consumer.side = .storedRight ∧
              consumer.mate ∉ owned ∧
              ∃ beforeTrace afterTrace,
                event.search.result.trace =
                  beforeTrace ++ consumer.conclusion :: consumer.mate ::
                    afterTrace)) := by
  rcases tagHistory.commitmentInterval_parConclusion_localizedDichotomy
      invariant input consumer parEq componentLookup occurrence positive
      firstAt lastAt with avoiding | obstruction
  · rcases avoiding with
      ⟨firstEvent, lastEvent, path, firstLookup, lastLookup, pathStarts,
        pathFinishes, pathAvoids⟩
    exact Or.inl ⟨firstEvent, lastEvent, path, firstLookup, lastLookup,
      pathStarts, pathFinishes, pathAvoids⟩
  · rcases obstruction with
      ⟨offset, parent, child, event, offsetLt, parentAt, childAt,
        notAvoiding, membership, eventAge,
        equalTrace | olderMateTrace⟩
    · rcases equalTrace with ⟨childEq, selectedTrace | mateTrace⟩
      · rcases selectedTrace with
          ⟨side, beforeTrace, afterTrace, trace⟩
        exact Or.inr ⟨offset, parent, child, event, offsetLt, parentAt,
          childAt, notAvoiding, membership, eventAge,
          Or.inl ⟨childEq, Or.inl
            ⟨side, beforeTrace, afterTrace, trace⟩⟩⟩
      · rcases mateTrace with ⟨side, beforeTrace, afterTrace, trace⟩
        exact Or.inr ⟨offset, parent, child, event, offsetLt, parentAt,
          childAt, notAvoiding, membership, eventAge,
          Or.inl ⟨childEq, Or.inr
            ⟨side, beforeTrace, afterTrace, trace⟩⟩⟩
    · rcases olderMateTrace with
        ⟨childOlder, side, mateOutside, beforeTrace, afterTrace, trace⟩
      exact Or.inr ⟨offset, parent, child, event, offsetLt, parentAt,
        childAt, notAvoiding, membership, eventAge,
        Or.inr ⟨childOlder, side, mateOutside, beforeTrace, afterTrace,
          trace⟩⟩

#print axioms
  CanonicalTagHistory.commitmentInterval_parConclusion_localizedDichotomy

end SequentialFigure7
end ProofNetIR

def main : IO Unit :=
  IO.println "Figure-7 commitment-interval par-trace localization: kernel-green"
