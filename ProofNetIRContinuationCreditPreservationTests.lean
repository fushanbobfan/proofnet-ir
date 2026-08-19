/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7ContinuationCreditPreservation

/-!
# Branch-local continuation-credit consumer

Exercises every public constructor and theorem from the independent
continuation-credit checkpoint, including elimination of all three receipt
forms. The consumer deliberately does not import branch-residual or unrelated
stronger-invariant modules.
-/

namespace ProofNetIR
namespace SequentialFigure7
namespace ContinuationCreditPreservationTests

open SequentialSchedulerBridge
open SequentialSchedulerState

/- Constructor-level consumption: each receipt alternative is usable without
unfolding the carrier. -/
example {certificate : Certificate} {state : ReservationState}
    {vertex : Vertex} (consumer : ConnectiveBelow certificate vertex)
    (mateUnmarked : state.core.marks[consumer.mate]? = some none) :
    ContinuationCredit certificate state vertex :=
  .rawMate consumer mateUnmarked

example {certificate : Certificate} {state : ReservationState}
    {vertex : Vertex} (consumer : ConnectiveBelow certificate vertex)
    {boundary : RawTokenAge}
    (work : FutureWorkAt state boundary consumer.conclusion) :
    ContinuationCredit certificate state vertex :=
  .futureConclusion consumer boundary work

example {certificate : Certificate} {state : ReservationState}
    {vertex : Vertex} (consumer : ConnectiveBelow certificate vertex)
    {rawAge : RawTokenAge}
    (marked :
      state.core.marks[consumer.conclusion]? = some (some rawAge)) :
    ContinuationCredit certificate state vertex :=
  .markedConclusion consumer rawAge marked

/- Eliminate all receipt alternatives and expose every constructor field. -/
example {certificate : Certificate} {state : ReservationState}
    {vertex : Vertex}
    (credit : ContinuationCredit certificate state vertex) :
    (∃ consumer : ConnectiveBelow certificate vertex,
        state.core.marks[consumer.mate]? = some none) ∨
      (∃ (consumer : ConnectiveBelow certificate vertex)
          (boundary : RawTokenAge),
        FutureWorkAt state boundary consumer.conclusion) ∨
      (∃ (consumer : ConnectiveBelow certificate vertex)
          (rawAge : RawTokenAge),
        state.core.marks[consumer.conclusion]? = some (some rawAge)) := by
  cases credit with
  | rawMate consumer mateUnmarked =>
      exact Or.inl ⟨consumer, mateUnmarked⟩
  | futureConclusion consumer boundary work =>
      exact Or.inr (Or.inl ⟨consumer, boundary, work⟩)
  | markedConclusion consumer rawAge marked =>
      exact Or.inr (Or.inr ⟨consumer, rawAge, marked⟩)

/- Predicate-level consumption. -/
example {certificate : Certificate} {state : ReservationState}
    (allCredits : MarkedNonconclusionContinuation certificate state)
    {rawAge : RawTokenAge} {vertex : Vertex}
    (marked : state.core.marks[vertex]? = some (some rawAge))
    (notConclusion : vertex ∉ certificate.conclusions) :
    ContinuationCredit certificate state vertex :=
  allCredits marked notConclusion

example (certificate : Certificate) :
    MarkedNonconclusionContinuation certificate
      (ReservationState.empty certificate) :=
  empty_markedNonconclusionContinuation certificate

example {certificate : Certificate} {after : ReservationState}
    {start : Vertex}
    (step : InitialReservationStep certificate after start) :
    MarkedNonconclusionContinuation certificate after :=
  SequentialFigure7.InitialReservationStep.markedNonconclusionContinuation step

example {before : ReservationState} (step : PreparedStep before)
    {rawAge : RawTokenAge} {vertex : Vertex}
    (work : FutureWorkAt before rawAge vertex) :
    vertex = step.stackResult.vertex ∨
      FutureWorkAt step.after rawAge vertex :=
  work.afterPreparedOrSelected step

example {certificate : Certificate} {before after : ReservationState}
    (step : NopStep certificate before after) :
    ContinuationCredit certificate after
      step.prepared.stackResult.vertex :=
  step.selectedContinuationCredit

example {certificate : Certificate} {before after : ReservationState}
    (step : NewStep certificate before after) :
    ContinuationCredit certificate after step.stackResult.vertex :=
  step.selectedContinuationCredit

example {certificate : Certificate} {before after : ReservationState}
    (step : WaitStep certificate before after) :
    ContinuationCredit certificate after
      step.prepared.stackResult.vertex :=
  step.selectedContinuationCredit

example {certificate : Certificate} {before after : ReservationState}
    (step : WaitStep certificate before after) :
    FutureWorkAt after step.destination.boundary
      step.consumer.conclusion :=
  step.createdConclusionFutureWorkAt

example {certificate : Certificate} {before after : ReservationState}
    (step : ForwardStep certificate before after) :
    ContinuationCredit certificate after
      step.prepared.stackResult.vertex :=
  step.selectedContinuationCredit

example {certificate : Certificate} {before after : ReservationState}
    (step : ForwardStep certificate before after) :
    FutureWorkAt after step.prepared.stackResult.rawAge
      step.consumer.conclusion :=
  step.createdConclusionFutureWorkAt

example {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after) :
    ContinuationCredit certificate after
      step.prepared.stackResult.vertex :=
  step.selectedContinuationCredit

example {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after) :
    FutureWorkAt after step.previousBoundary
      step.consumer.conclusion :=
  step.createdConclusionFutureWorkAt

example {certificate : Certificate} {before : ReservationState}
    {result : Figure7DispatchResult}
    (evidence : DispatchTagEvidence certificate before result)
    {rawAge : RawTokenAge} {vertex : Vertex}
    (event : evidence.RawMarked rawAge vertex)
    (notConclusion : vertex ∉ certificate.conclusions) :
    ContinuationCredit certificate result.after vertex :=
  evidence.newlyMarkedContinuationCredit event notConclusion

private def CreditObservation (certificate : Certificate)
    (state : ReservationState) (vertex : Vertex) : Prop :=
  (∃ consumer : ConnectiveBelow certificate vertex,
      state.core.marks[consumer.mate]? = some none) ∨
    (∃ (consumer : ConnectiveBelow certificate vertex)
        (boundary : RawTokenAge),
      FutureWorkAt state boundary consumer.conclusion) ∨
    (∃ (consumer : ConnectiveBelow certificate vertex)
        (rawAge : RawTokenAge),
      state.core.marks[consumer.conclusion]? = some (some rawAge))

private theorem observeCredit
    {certificate : Certificate} {state : ReservationState} {vertex : Vertex}
    (credit : ContinuationCredit certificate state vertex) :
    CreditObservation certificate state vertex := by
  cases credit with
  | rawMate consumer mateUnmarked =>
      exact Or.inl ⟨consumer, mateUnmarked⟩
  | futureConclusion consumer boundary work =>
      exact Or.inr (Or.inl ⟨consumer, boundary, work⟩)
  | markedConclusion consumer rawAge marked =>
      exact Or.inr (Or.inr ⟨consumer, rawAge, marked⟩)

example {certificate : Certificate} {before after : ReservationState}
    (step : ConclStep certificate before after)
    (invariant : SchedulerInvariant certificate before)
    {vertex : Vertex}
    (credit : ContinuationCredit certificate before vertex) :
    CreditObservation certificate after vertex :=
  observeCredit (step.continuationCredit invariant.structural credit)

example {certificate : Certificate} {before after : ReservationState}
    (step : NopStep certificate before after)
    (invariant : SchedulerInvariant certificate before)
    {vertex : Vertex} {rawAge : RawTokenAge}
    (ownerMarked : before.core.marks[vertex]? = some (some rawAge))
    (credit : ContinuationCredit certificate before vertex) :
    CreditObservation certificate after vertex :=
  observeCredit
    (step.continuationCredit invariant.structural ownerMarked credit)

example {certificate : Certificate} {before after : ReservationState}
    (step : NewStep certificate before after)
    (invariant : SchedulerInvariant certificate before)
    {vertex : Vertex} {rawAge : RawTokenAge}
    (ownerMarked : before.core.marks[vertex]? = some (some rawAge))
    (credit : ContinuationCredit certificate before vertex) :
    CreditObservation certificate after vertex :=
  observeCredit
    (step.continuationCredit invariant.structural ownerMarked credit)

example {certificate : Certificate} {before after : ReservationState}
    (step : WaitStep certificate before after)
    (invariant : SchedulerInvariant certificate before)
    {vertex : Vertex}
    (credit : ContinuationCredit certificate before vertex) :
    CreditObservation certificate after vertex :=
  observeCredit (step.continuationCredit invariant.structural credit)

example {certificate : Certificate} {before after : ReservationState}
    (step : ForwardStep certificate before after)
    (invariant : SchedulerInvariant certificate before)
    {vertex : Vertex}
    (credit : ContinuationCredit certificate before vertex) :
    CreditObservation certificate after vertex :=
  observeCredit (step.continuationCredit invariant.structural credit)

example {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after)
    (invariant : SchedulerInvariant certificate before)
    {vertex : Vertex}
    (credit : ContinuationCredit certificate before vertex) :
    CreditObservation certificate after vertex :=
  observeCredit (step.continuationCredit invariant.structural credit)

example {certificate : Certificate} {before : ReservationState}
    {result : Figure7DispatchResult}
    (evidence : DispatchTagEvidence certificate before result)
    (invariant : SchedulerInvariant certificate before)
    {vertex : Vertex} {rawAge : RawTokenAge}
    (ownerMarked : before.core.marks[vertex]? = some (some rawAge))
    (credit : ContinuationCredit certificate before vertex) :
    CreditObservation certificate result.after vertex :=
  observeCredit
    (evidence.oldContinuationCredit invariant.structural ownerMarked credit)

example {certificate : Certificate} {before : ReservationState}
    {result : Figure7DispatchResult}
    (evidence : DispatchTagEvidence certificate before result)
    (invariant : SchedulerInvariant certificate before)
    (prior : MarkedNonconclusionContinuation certificate before)
    {vertex : Vertex} {rawAge : RawTokenAge}
    (marked : result.after.core.marks[vertex]? = some (some rawAge))
    (notConclusion : vertex ∉ certificate.conclusions) :
    CreditObservation certificate result.after vertex :=
  observeCredit
    (evidence.markedNonconclusionContinuation invariant.structural prior
      marked notConclusion)

example {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    {vertex : Vertex} {rawAge : RawTokenAge}
    (marked : state.core.marks[vertex]? = some (some rawAge))
    (notConclusion : vertex ∉ certificate.conclusions) :
    CreditObservation certificate state vertex :=
  observeCredit
    (tagHistory.markedNonconclusionContinuation marked notConclusion)

#print axioms empty_markedNonconclusionContinuation
#print axioms InitialReservationStep.markedNonconclusionContinuation
#print axioms FutureWorkAt.afterPreparedOrSelected
#print axioms NopStep.selectedContinuationCredit
#print axioms WaitStep.createdConclusionFutureWorkAt
#print axioms WaitStep.selectedContinuationCredit
#print axioms NewStep.selectedContinuationCredit
#print axioms ForwardStep.createdConclusionFutureWorkAt
#print axioms ForwardStep.selectedContinuationCredit
#print axioms UnifyPayloadStep.createdConclusionFutureWorkAt
#print axioms UnifyPayloadStep.selectedContinuationCredit
#print axioms DispatchTagEvidence.newlyMarkedContinuationCredit
#print axioms ConclStep.continuationCredit
#print axioms NopStep.continuationCredit
#print axioms NewStep.continuationCredit
#print axioms WaitStep.continuationCredit
#print axioms ForwardStep.continuationCredit
#print axioms UnifyPayloadStep.continuationCredit
#print axioms DispatchTagEvidence.oldContinuationCredit
#print axioms DispatchTagEvidence.markedNonconclusionContinuation
#print axioms CanonicalTagHistory.markedNonconclusionContinuation

end ContinuationCreditPreservationTests
end SequentialFigure7
end ProofNetIR

/- Run the standalone branch-local continuation-credit API consumer. -/
def main : IO Unit :=
  IO.println "Figure-7 continuation-credit preservation consumer: kernel-green"
