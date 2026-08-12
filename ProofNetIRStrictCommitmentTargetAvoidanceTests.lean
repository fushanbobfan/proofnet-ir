/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7StrictCommitmentTargetAvoidance

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerBridge

#check CanonicalTagHistory.commitmentEdge_referencePath_avoiding_of_strict
#check CanonicalTagHistory.commitmentInterval_referencePath_avoiding_of_lastOlder

example
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (invariant : SchedulerInvariant certificate state)
    (regionSeparated : OlderEventTouchSeparated tagHistory)
    (headSeparated : OlderEventFutureWorkTouchSeparated tagHistory)
    (candidate : FutureNewCandidateAt certificate state)
    {position : Nat} {parent child : RawTokenAge}
    (parentAt : state.stack.sigma[position]? = some parent)
    (childAt : state.stack.sigma[position + 1]? = some child)
    (childOlder :
      state.core.representative child <
        state.core.representative candidate.rawAge) :
    tagHistory.CommitmentEdgeTargetAvoidingPath parent child
      candidate.tensor.conclusion :=
  tagHistory.commitmentEdge_referencePath_avoiding_of_strict invariant
    regionSeparated headSeparated candidate parentAt childAt childOlder

example
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (invariant : SchedulerInvariant certificate state)
    (regionSeparated : OlderEventTouchSeparated tagHistory)
    (headSeparated : OlderEventFutureWorkTouchSeparated tagHistory)
    (candidate : FutureNewCandidateAt certificate state)
    {position edgeCount : Nat} {first last : RawTokenAge}
    (positive : 0 < edgeCount)
    (firstAt : state.stack.sigma[position]? = some first)
    (lastAt : state.stack.sigma[position + edgeCount]? = some last)
    (lastOlder :
      state.core.representative last <
        state.core.representative candidate.rawAge) :
    tagHistory.CommitmentEdgeTargetAvoidingPath first last
      candidate.tensor.conclusion :=
  tagHistory.commitmentInterval_referencePath_avoiding_of_lastOlder invariant
    regionSeparated headSeparated candidate positive firstAt lastAt lastOlder

example
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (invariant : SchedulerInvariant certificate state)
    (regionSeparated : OlderEventTouchSeparated tagHistory)
    (headSeparated : OlderEventFutureWorkTouchSeparated tagHistory)
    (candidate : FutureNewCandidateAt certificate state)
    {position : Nat} {parent child : RawTokenAge}
    (parentAt : state.stack.sigma[position]? = some parent)
    (childAt : state.stack.sigma[position + 1]? = some child)
    (childOlder :
      state.core.representative child <
        state.core.representative candidate.rawAge) :
    ∃ path : certificate.referenceSwitchingGraph.EdgeSimplePath,
      candidate.tensor.conclusion ∉ path.vertices := by
  rcases tagHistory.commitmentEdge_referencePath_avoiding_of_strict invariant
      regionSeparated headSeparated candidate parentAt childAt childOlder with
    ⟨_parentEvent, _childEvent, path, _parentAt, _childAt,
      _starts, _finishes, omits⟩
  exact ⟨path, omits⟩

end SequentialFigure7
end ProofNetIR

def main : IO Unit :=
  IO.println "Figure-7 strict commitment target-avoidance consumer passed."
