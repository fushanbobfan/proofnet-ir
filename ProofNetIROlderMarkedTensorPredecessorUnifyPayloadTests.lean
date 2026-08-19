/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7OlderMarkedTensorPredecessorUnifyPayloadPreservation

/-!
# Older marked-tensor predecessor UnifyPayload-preservation consumer

Checks and applies the carrier-free created-conclusion touch theorem, its
future-candidate wrapper, and the public UnifyPayload predecessor-preservation
theorem. This consumer makes no claim about branch applicability, dispatcher
progress or totality, full history closure, fallback removal, maximality, or
sequentialization.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerBridge
open SequentialSchedulerState

#check UnifyPayloadStep.createdConclusionTouchSeparated
#check UnifyPayloadStep.createdHeadTouchSeparated
#check CanonicalTagHistory.unifyPayload_olderMarkedTensorPredecessorInvariant

example
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    (step : UnifyPayloadStep certificate before after)
    (prior : CanonicalTagHistory certificate history)
    (structural : certificate.StructurallyWellFormed)
    {event : ReservationEvent certificate}
    (eventMembership : event ∈ prior.reservationLedger)
    (older :
      step.prepared.after.core.representative event.rawAge <
        step.prepared.after.core.representative step.previousBoundary)
    (touched : event.Touched step.consumer.conclusion) : False := by
  exact step.createdConclusionTouchSeparated prior structural event
    eventMembership older touched

example
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    (step : UnifyPayloadStep certificate before after)
    (prior : CanonicalTagHistory certificate history)
    (structural : certificate.StructurallyWellFormed)
    (created : UnifyPayloadCreatedCandidate certificate step)
    {event : ReservationEvent certificate}
    (eventMembership : event ∈ prior.reservationLedger)
    (older :
      step.prepared.after.core.representative event.rawAge <
        step.prepared.after.core.representative step.previousBoundary)
    (touched : event.Touched step.consumer.conclusion) : False := by
  have separated : UnifyPayloadCreatedHeadTouchSeparated prior step :=
    step.createdHeadTouchSeparated prior structural
  exact separated eventMembership created older touched

example
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate before)
    (dispatch :
      DispatchStep certificate before invariant ⟨.unifyPayload, after⟩)
    (step : UnifyPayloadStep certificate before after)
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
    tagHistory.unifyPayload_olderMarkedTensorPredecessorInvariant
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
    "Older marked-tensor predecessor UnifyPayload-preservation consumer passed."
