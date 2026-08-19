/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7OlderMarkedTensorPredecessorForwardPreservation

/-!
# Older marked-tensor predecessor Forward-preservation consumer

Checks and applies the public child-anchor bridge and the public Forward
preservation theorem. This consumer makes no claim about branch applicability,
dispatcher progress or totality, full history closure, maximality, or
sequentialization.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerBridge
open SequentialSchedulerState

#check CanonicalTagHistory.markedMate_sigmaImmediatePredecessor_of_childAnchor
#check CanonicalTagHistory.forward_olderMarkedTensorPredecessorInvariant

example
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate state)
    {candidateRawAge : RawTokenAge} {candidateVertex : Vertex}
    (work : FutureWorkAt state candidateRawAge candidateVertex)
    (outer : TensorBelow)
    (outerValid :
      outer.Valid certificate certificate.consumerIndex candidateVertex)
    {mateRawAge : RawTokenAge}
    (mateMarked :
      state.core.marks[outer.mate]? = some (some mateRawAge))
    (older :
      state.core.representative mateRawAge <
        state.core.representative candidateRawAge)
    (headSeparated : ∀ event : ReservationEvent certificate,
      event ∈ tagHistory.reservationLedger →
      state.core.representative event.rawAge <
          state.core.representative candidateRawAge →
      ¬ event.Touched candidateVertex)
    (childAnchor : ∀ childEvent : ReservationEvent certificate,
      tagHistory.reservationLedger[candidateRawAge]? = some childEvent →
        ∃ path : certificate.referenceSwitchingGraph.EdgeSimplePath,
          path.start = childEvent.search.result.left ∧
            path.finish = candidateVertex ∧
              outer.conclusion ∉ path.vertices) :
    ∃ position,
      state.stack.sigma[position]? = some mateRawAge ∧
        state.stack.sigma[position + 1]? = some candidateRawAge ∧
          sigmaBoundary? state.stack.sigma mateRawAge = some mateRawAge := by
  rcases tagHistory.markedMate_sigmaImmediatePredecessor_of_childAnchor
      correct invariant work outer outerValid mateMarked older headSeparated
      childAnchor with
    ⟨predecessor⟩
  exact ⟨predecessor.position, predecessor.previous_at,
    predecessor.candidate_at, predecessor.mate_boundary⟩

example
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate before)
    (dispatch : DispatchStep certificate before invariant ⟨.forward, after⟩)
    (step : ForwardStep certificate before after)
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
    tagHistory.forward_olderMarkedTensorPredecessorInvariant
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
    "Older marked-tensor predecessor Forward-preservation consumer passed."
