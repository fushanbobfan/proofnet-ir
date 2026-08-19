/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7OlderMarkedTensorPredecessorNewPreservation
import ProofNetIR.SequentialFigure7ReadyHeadDispatchResidual

/-!
# Older marked-tensor predecessor branch-prefix consumer

Consumes the indexed carrier, active-ready projection, base cases, stable
branches, and the canonical `new` preservation theorem.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerBridge
open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState

#check SigmaImmediatePredecessorAt
#check OlderMarkedTensorPredecessorInvariant
#check OlderMarkedTensorPredecessorInvariant.readyHead_predecessor_of_boundary_lt
#check empty_olderMarkedTensorPredecessorInvariant
#check InitialReservationStep.olderMarkedTensorPredecessorInvariant
#check PreparedStep.olderMarkedTensorPredecessorInvariant
#check ConclStep.olderMarkedTensorPredecessorInvariant
#check NopStep.olderMarkedTensorPredecessorInvariant
#check CanonicalTagHistory.new_olderMarkedTensorPredecessorInvariant

example
    {sigma : List RawTokenAge}
    {candidateBoundary mateRawAge previousBoundary : RawTokenAge}
    (position : Nat)
    (previousAt : sigma[position]? = some previousBoundary)
    (candidateAt : sigma[position + 1]? = some candidateBoundary)
    (mateBoundary :
      sigmaBoundary? sigma mateRawAge = some previousBoundary) :
    SigmaImmediatePredecessorAt sigma candidateBoundary mateRawAge
      previousBoundary :=
  { position
    previous_at := previousAt
    candidate_at := candidateAt
    mate_boundary := mateBoundary }

example
    {certificate : Certificate} {state : ReservationState}
    (allWork :
      OlderMarkedTensorPredecessorInvariant certificate state)
    (invariant : SchedulerInvariant certificate state)
    (head : ReadyHeadInput state)
    (consumer : ConnectiveBelow certificate head.vertex)
    (tensorKind : consumer.kind = .tensor)
    {mateRawAge mateBoundary : RawTokenAge}
    (mateMarked :
      state.core.marks[consumer.mate]? = some (some mateRawAge))
    (mateBoundaryLookup :
      sigmaBoundary? state.stack.sigma mateRawAge = some mateBoundary)
    (mateBoundaryLt : mateBoundary < head.rawAge) :
    ∃ previousBoundary,
      Nonempty
        (SigmaPredecessorInput state.stack.sigma head.rawAge mateRawAge
          previousBoundary) :=
  allWork.readyHead_predecessor_of_boundary_lt invariant head consumer
    tensorKind mateMarked mateBoundaryLookup mateBoundaryLt

example
    {certificate : Certificate} {state : ReservationState}
    (allWork :
      OlderMarkedTensorPredecessorInvariant certificate state)
    (invariant : SchedulerInvariant certificate state)
    (head : ReadyHeadInput state)
    (gap : ReadyHeadMarkedTensorPredecessorGap certificate state head) :
    False := by
  rcases allWork.readyHead_predecessor_of_boundary_lt invariant head
      gap.consumer gap.tensor_kind gap.mate_marked gap.mate_boundary
      gap.mate_boundary_lt_active with
    ⟨previousBoundary, predecessor⟩
  exact gap.no_predecessor ⟨previousBoundary, predecessor⟩

example (certificate : Certificate) :
    OlderMarkedTensorPredecessorInvariant certificate
      (ReservationState.empty certificate) :=
  empty_olderMarkedTensorPredecessorInvariant certificate

example
    {certificate : Certificate} {after : ReservationState} {start : Vertex}
    (step : InitialReservationStep certificate after start) :
    OlderMarkedTensorPredecessorInvariant certificate after :=
  InitialReservationStep.olderMarkedTensorPredecessorInvariant step

example
    {certificate : Certificate} {before : ReservationState}
    (step : PreparedStep before)
    (invariant : SchedulerInvariant certificate before)
    (prior :
      OlderMarkedTensorPredecessorInvariant certificate before) :
    OlderMarkedTensorPredecessorInvariant certificate step.after :=
  step.olderMarkedTensorPredecessorInvariant invariant prior

example
    {certificate : Certificate} {before after : ReservationState}
    (step : ConclStep certificate before after)
    (invariant : SchedulerInvariant certificate before)
    (prior :
      OlderMarkedTensorPredecessorInvariant certificate before) :
    OlderMarkedTensorPredecessorInvariant certificate after :=
  step.olderMarkedTensorPredecessorInvariant invariant prior

example
    {certificate : Certificate} {before after : ReservationState}
    (step : NopStep certificate before after)
    (invariant : SchedulerInvariant certificate before)
    (prior :
      OlderMarkedTensorPredecessorInvariant certificate before) :
    OlderMarkedTensorPredecessorInvariant certificate after :=
  step.olderMarkedTensorPredecessorInvariant invariant prior

example
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate before)
    (step : NewStep certificate before after)
    (prior :
      OlderMarkedTensorPredecessorInvariant certificate before) :
    OlderMarkedTensorPredecessorInvariant certificate after :=
  tagHistory.new_olderMarkedTensorPredecessorInvariant correct invariant step
    prior

end SequentialFigure7
end ProofNetIR

def main : IO Unit :=
  IO.println
    "Older marked-tensor predecessor branch-prefix consumer passed."
