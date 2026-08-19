/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7OlderMarkedTensorPredecessorWaitPreservation

/-!
# Older marked-tensor predecessor Wait-preservation consumer

Checks and applies the sole public theorem from the Wait-preservation module.
This consumer makes no claim about the remaining dispatcher branches, full
history closure, progress, maximality, or sequentialization.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerBridge
open SequentialSchedulerState

#check CanonicalTagHistory.wait_olderMarkedTensorPredecessorInvariant

example
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate before)
    (dispatch : DispatchStep certificate before invariant ⟨.wait, after⟩)
    (step : WaitStep certificate before after)
    (prior : OlderMarkedTensorPredecessorInvariant certificate before)
    {candidateRawAge : RawTokenAge} {candidateVertex : Vertex}
    (work : FutureWorkAt after candidateRawAge candidateVertex)
    (consumer : ConnectiveBelow certificate candidateVertex)
    (tensorKind : consumer.kind = .tensor)
    {mateRawAge : RawTokenAge}
    (mateMarked :
      after.core.marks[consumer.mate]? = some (some mateRawAge))
    (older :
      after.core.representative mateRawAge <
        after.core.representative candidateRawAge) :
    ∃ position previousBoundary,
      after.stack.sigma[position]? = some previousBoundary ∧
        after.stack.sigma[position + 1]? = some candidateRawAge ∧
          sigmaBoundary? after.stack.sigma mateRawAge =
            some previousBoundary := by
  have preserved : OlderMarkedTensorPredecessorInvariant certificate after :=
    tagHistory.wait_olderMarkedTensorPredecessorInvariant
      (invariant := invariant) (dispatch := dispatch) correct step prior
  rcases preserved work consumer tensorKind mateMarked older with
    ⟨previousBoundary, ⟨predecessor⟩⟩
  exact ⟨predecessor.position, previousBoundary,
    predecessor.previous_at, predecessor.candidate_at,
    predecessor.mate_boundary⟩

end SequentialFigure7
end ProofNetIR

def main : IO Unit :=
  IO.println
    "Older marked-tensor predecessor Wait-preservation consumer passed."
