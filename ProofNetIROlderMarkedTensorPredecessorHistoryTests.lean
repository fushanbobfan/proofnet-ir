/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7OlderMarkedTensorPredecessorHistory

/-!
# Full-history older marked-tensor predecessor consumer

Checks all three public full-history declarations. The examples project every
field of the indexed predecessor carrier and destructure the exact dispatcher
result at an explicitly supplied reachable ready head. No example constructs a
`ReadyHeadInput` or claims dispatcher progress, totality, or completeness.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerBridge
open SequentialSchedulerState

#check CanonicalTagHistory.olderMarkedTensorPredecessorInvariant
#check ExecutedHistory.olderMarkedTensorPredecessorInvariant
#check ReachableByImplementedDispatcher.readyHead_dispatch

example
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect) :
    OlderMarkedTensorPredecessorInvariant certificate state := by
  exact tagHistory.olderMarkedTensorPredecessorInvariant correct

example
    {certificate : Certificate} {state : ReservationState}
    (history : ExecutedHistory certificate state)
    (correct : certificate.DeclarativelyCorrect)
    {candidateRawAge : RawTokenAge} {candidateVertex : Vertex}
    (work : FutureWorkAt state candidateRawAge candidateVertex)
    (consumer : ConnectiveBelow certificate candidateVertex)
    (tensorKind : consumer.kind = .tensor)
    {mateRawAge : RawTokenAge}
    (mateMarked :
      state.core.marks[consumer.mate]? = some (some mateRawAge))
    (older :
      state.core.representative mateRawAge <
        state.core.representative candidateRawAge) :
    ∃ position previousBoundary,
      state.stack.sigma[position]? = some previousBoundary ∧
        state.stack.sigma[position + 1]? = some candidateRawAge ∧
          sigmaBoundary? state.stack.sigma mateRawAge =
            some previousBoundary := by
  have allWork : OlderMarkedTensorPredecessorInvariant certificate state :=
    history.olderMarkedTensorPredecessorInvariant correct
  rcases allWork work consumer tensorKind mateMarked older with
    ⟨previousBoundary, ⟨predecessor⟩⟩
  exact ⟨predecessor.position, previousBoundary,
    predecessor.previous_at, predecessor.candidate_at,
    predecessor.mate_boundary⟩

example
    {certificate : Certificate} {before : ReservationState}
    (reachable : ReachableByImplementedDispatcher certificate before)
    (correct : certificate.DeclarativelyCorrect)
    (head : ReadyHeadInput before) :
    let invariant := reachable.schedulerInvariant correct.1
    ∃ kind after,
      dispatch? certificate before invariant = some ⟨kind, after⟩ := by
  let invariant := reachable.schedulerInvariant correct.1
  change ∃ kind after,
    dispatch? certificate before invariant = some ⟨kind, after⟩
  rcases reachable.readyHead_dispatch correct head with ⟨result, equation⟩
  exact ⟨result.kind, result.after, equation⟩

end SequentialFigure7
end ProofNetIR

def main : IO Unit :=
  IO.println "Full-history older marked-tensor predecessor consumer passed."
