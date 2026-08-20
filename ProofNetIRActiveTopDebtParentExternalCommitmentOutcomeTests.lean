/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7ActiveTopDebtParentExternalCommitmentOutcome

/-!
# Active-top debt external parent commitment-outcome consumer

This runnable consumer applies the generic commitment split, normalizes all
three external temporal branches, reconstructs every public field, and audits
the four production declarations directly.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerBridge

namespace Consumer

private theorem commitmentSplitRoundTrip
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (invariant : SchedulerInvariant certificate state)
    {first active : RawTokenAge}
    (firstMembership : first ∈ state.stack.sigma)
    (activeTop : state.stack.sigma.getLast? = some active)
    (older : first < active) :
    tagHistory.StrictOlderCommitmentSplit first active := by
  rcases tagHistory.strictOlderCommitmentSplit_to_top invariant
      firstMembership activeTop older with
    ⟨position, edgeCount, predecessor, firstAt, predecessorAt, activeAt,
      representativeOlder, edgePath⟩
  exact ⟨position, edgeCount, predecessor, firstAt, predecessorAt, activeAt,
    representativeOlder, edgePath⟩

private theorem commitmentOutcomeRoundTrip
    {certificate : Certificate} {state : ReservationState}
    {activeRawAge : RawTokenAge} {owned : List Vertex}
    (outcome : ActiveCarrierParentExternalTemporalOutcome certificate state
      activeRawAge owned)
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (invariant : SchedulerInvariant certificate state)
    (activeTop : state.stack.sigma.getLast? = some activeRawAge) :
    ActiveCarrierParentExternalCommitmentOutcome tagHistory
      activeRawAge owned := by
  have normalized := outcome.commitmentOutcome tagHistory invariant activeTop
  cases normalized with
  | rawOutside sibling unmarked outside =>
      exact .rawOutside sibling unmarked outside
  | olderFuture conclusion boundary work older split outside =>
      exact .olderFuture conclusion boundary work older split outside
  | olderMarked conclusion age marked older split outside =>
      exact .olderMarked conclusion age marked older split outside

end Consumer

end SequentialFigure7
end ProofNetIR

#print axioms ProofNetIR.SequentialFigure7.CanonicalTagHistory.StrictOlderCommitmentSplit
#print axioms ProofNetIR.SequentialFigure7.CanonicalTagHistory.strictOlderCommitmentSplit_to_top
#print axioms ProofNetIR.SequentialFigure7.ActiveCarrierParentExternalCommitmentOutcome
#print axioms
  ProofNetIR.SequentialFigure7.ActiveCarrierParentExternalTemporalOutcome.commitmentOutcome

def main : IO Unit :=
  IO.println "active-top debt external parent commitment outcome: kernel-green"
