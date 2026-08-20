/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7CommitmentIntervalParConclusionDichotomy

/-!
# Figure-7 commitment-interval par-conclusion dichotomy consumer

The consumer invokes the public interval theorem, reconstructs the composed
path case, and destructs every field of both exact trace orientations in the
localized obstruction case.
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
    {position edgeCount : Nat} {first last : RawTokenAge}
    (positive : 0 < edgeCount)
    (firstAt : state.stack.sigma[position]? = some first)
    (lastAt : state.stack.sigma[position + edgeCount]? = some last) :
    tagHistory.CommitmentEdgeTargetAvoidingPath first last
        consumer.conclusion ∨
      ∃ offset parent child event,
        offset < edgeCount ∧
          state.stack.sigma[position + offset]? = some parent ∧
          state.stack.sigma[position + offset + 1]? = some child ∧
          (child < last ∨ child = last) ∧
          ¬ tagHistory.CommitmentEdgeTargetAvoidingPath parent child
            consumer.conclusion ∧
          event ∈ tagHistory.reservationLedger ∧
          event.rawAge = child ∧
          ((consumer.side = .storedLeft ∧
              ∃ beforeTrace afterTrace,
                event.search.result.trace =
                  beforeTrace ++ consumer.conclusion :: input.vertex ::
                    afterTrace) ∨
            (consumer.side = .storedRight ∧
              ∃ beforeTrace afterTrace,
                event.search.result.trace =
                  beforeTrace ++ consumer.conclusion :: consumer.mate ::
                    afterTrace)) := by
  rcases tagHistory.commitmentInterval_parConclusion_dichotomy invariant input
      consumer parEq positive firstAt lastAt with avoiding | obstruction
  · rcases avoiding with
      ⟨firstEvent, lastEvent, path, firstLookup, lastLookup, pathStarts,
        pathFinishes, pathAvoids⟩
    exact Or.inl ⟨firstEvent, lastEvent, path, firstLookup, lastLookup,
      pathStarts, pathFinishes, pathAvoids⟩
  · rcases obstruction with
      ⟨offset, parent, child, event, offsetLt, parentAt, childAt, childOrder,
        notAvoiding, membership, rawAge, selectedTrace | mateTrace⟩
    · rcases selectedTrace with
        ⟨side, beforeTrace, afterTrace, trace⟩
      exact Or.inr ⟨offset, parent, child, event, offsetLt, parentAt, childAt,
        childOrder, notAvoiding, membership, rawAge,
        Or.inl ⟨side, beforeTrace, afterTrace, trace⟩⟩
    · rcases mateTrace with ⟨side, beforeTrace, afterTrace, trace⟩
      exact Or.inr ⟨offset, parent, child, event, offsetLt, parentAt, childAt,
        childOrder, notAvoiding, membership, rawAge,
        Or.inr ⟨side, beforeTrace, afterTrace, trace⟩⟩

#print axioms CanonicalTagHistory.commitmentInterval_parConclusion_dichotomy

end SequentialFigure7
end ProofNetIR

def main : IO Unit :=
  IO.println "Figure-7 commitment-interval par dichotomy: kernel-green"
