/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7CrossRepresentativeInvariant
import ProofNetIR.SequentialFigure7RawMarkHistory

/-!
# Branch-local continuation credit

This file introduces a deliberately weaker replacement for active-top raw
debt.  Every concrete raw mark on a non-conclusion receives one local receipt:
an unmarked mate, scheduled parent work, or an already marked parent.  The
fresh-event layer is exact for all six dispatcher constructors; preservation
of receipts inherited from an older state remains a separate theorem.

Nothing here establishes `ActiveTopMarkedNonconclusionDebt`, dispatcher
progress, totality, or a full canonical-history invariant.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge

/-- A branch-local receipt for a vertex: its opposite premise is still raw,
its connective conclusion is scheduled, or that conclusion is already
raw-marked. This carrier alone does not assert that the vertex is marked or
that it is a non-conclusion. -/
inductive ContinuationCredit (certificate : Certificate)
    (state : ReservationState) (vertex : Vertex) : Prop where
  | rawMate (consumer : ConnectiveBelow certificate vertex)
      (mate_unmarked :
        state.core.marks[consumer.mate]? = some none) :
      ContinuationCredit certificate state vertex
  | futureConclusion (consumer : ConnectiveBelow certificate vertex)
      (boundary : RawTokenAge)
      (work : FutureWorkAt state boundary consumer.conclusion) :
      ContinuationCredit certificate state vertex
  | markedConclusion (consumer : ConnectiveBelow certificate vertex)
      (rawAge : RawTokenAge)
      (marked :
        state.core.marks[consumer.conclusion]? = some (some rawAge)) :
      ContinuationCredit certificate state vertex

/-- Every concretely raw-marked non-conclusion in a state has a continuation
receipt. This predicate does not include inherited-credit transport or a
canonical-history theorem. -/
def MarkedNonconclusionContinuation
    (certificate : Certificate) (state : ReservationState) : Prop :=
  ∀ {rawAge : RawTokenAge} {vertex : Vertex},
    state.core.marks[vertex]? = some (some rawAge) →
      vertex ∉ certificate.conclusions →
        ContinuationCredit certificate state vertex

/-- The empty reservation state has no marked non-conclusion requiring a
continuation receipt. -/
theorem empty_markedNonconclusionContinuation
    (certificate : Certificate) :
    MarkedNonconclusionContinuation certificate
      (ReservationState.empty certificate) := by
  intro rawAge vertex marked _notConclusion
  change (Array.replicate certificate.formulas.size none)[vertex]? =
    some (some rawAge) at marked
  rw [Array.getElem?_replicate] at marked
  split at marked <;> simp at marked

/-- An initial reservation step has no marked non-conclusion requiring a
continuation receipt. -/
theorem InitialReservationStep.markedNonconclusionContinuation
    {certificate : Certificate} {after : ReservationState} {start : Vertex}
    (step : InitialReservationStep certificate after start) :
    MarkedNonconclusionContinuation certificate after := by
  intro rawAge vertex marked _notConclusion
  have afterCore : after.core = step.coreAfter :=
    congrArg ReservationState.core step.output_eq
  rcases certificate.reserveAxiomAt?_exact step.core_eq with
    ⟨_left, _right, _component, _link, _ready, _componentLookup,
      _frontier, marksEq, _parents, _components, _started, _fired⟩
  rw [afterCore, marksEq] at marked
  change (Array.replicate certificate.formulas.size none)[vertex]? =
    some (some rawAge) at marked
  rw [Array.getElem?_replicate] at marked
  split at marked <;> simp at marked

/-- Transport queued work across the prepared prefix, except that the selected
head may be the work itself. This is prefix-local and does not transport a
complete inherited continuation receipt across a dispatcher branch. -/
theorem FutureWorkAt.afterPreparedOrSelected
    {before : ReservationState} (step : PreparedStep before)
    {rawAge : RawTokenAge} {vertex : Vertex}
    (work : FutureWorkAt before rawAge vertex) :
    vertex = step.stackResult.vertex ∨
      FutureWorkAt step.after rawAge vertex := by
  rcases SequentialStackState.popReadyMark?_exact step.stack_eq with
    ⟨topEquation, _sigmaTop, _unmarked, _marks, _nextAge,
      sigmaEquation, readyEquation, waitingEquation, _marked⟩
  rcases List.getLast?_eq_some_iff.mp topEquation with
    ⟨readyPrefix, readyDecomposition⟩
  have afterReady :
      step.after.stack.ready =
        readyPrefix ++ [step.stackResult.remainingTop] := by
    change step.stackResult.after.ready = _
    rw [readyEquation, readyDecomposition]
    simp
  have afterSigma : step.after.stack.sigma = before.stack.sigma := by
    change step.stackResult.after.sigma = before.stack.sigma
    exact sigmaEquation
  have afterWaiting : step.after.stack.waiting = before.stack.waiting := by
    change step.stackResult.after.waiting = before.stack.waiting
    exact waitingEquation
  cases work with
  | @ready position _ bucket _ sigmaAt readyAt member =>
      have positionBound :
          position < (readyPrefix ++
            [step.stackResult.vertex ::
              step.stackResult.remainingTop]).length := by
        rw [← readyDecomposition]
        exact (List.getElem?_eq_some_iff.mp readyAt).1
      by_cases inPrefix : position < readyPrefix.length
      · right
        apply FutureWorkAt.ready
        · rw [afterSigma]
          exact sigmaAt
        · rw [afterReady, List.getElem?_append_left inPrefix]
          rw [readyDecomposition, List.getElem?_append_left inPrefix] at readyAt
          exact readyAt
        · exact member
      · have positionTop : position = readyPrefix.length := by
          simp at positionBound
          omega
        subst position
        have bucketEquation :
            bucket = step.stackResult.vertex ::
              step.stackResult.remainingTop := by
          rw [readyDecomposition] at readyAt
          simp at readyAt
          exact readyAt.symm
        subst bucket
        simp only [List.mem_cons] at member
        rcases member with selected | tail
        · exact Or.inl selected
        · right
          apply FutureWorkAt.ready
            (bucket := step.stackResult.remainingTop)
          · rw [afterSigma]
            exact sigmaAt
          · rw [afterReady]
            simp
          · exact tail
  | @waiting _ payload _ waitingAt member =>
      right
      apply FutureWorkAt.waiting
      · rw [afterWaiting]
        exact waitingAt
      · exact member

/-- The fresh selected mark of a `nop` step has raw-mate continuation credit. -/
theorem NopStep.selectedContinuationCredit
    {certificate : Certificate} {before after : ReservationState}
    (step : NopStep certificate before after) :
    ContinuationCredit certificate after
      step.prepared.stackResult.vertex := by
  apply ContinuationCredit.rawMate step.consumer
  have coreEq : after.core = step.prepared.coreMarked := by
    simpa [PreparedStep.after] using
      congrArg ReservationState.core step.output_eq
  rw [coreEq]
  exact step.mate_unmarked

/-- A `wait` step schedules its selected connective conclusion at the
destination waiting boundary. -/
theorem WaitStep.createdConclusionFutureWorkAt
    {certificate : Certificate} {before after : ReservationState}
    (step : WaitStep certificate before after) :
    FutureWorkAt after step.destination.boundary
      step.consumer.conclusion := by
  rcases step.destination.exact with
    ⟨payload, _old, inserted, _marks, _nextAge, _sigma, _ready,
      _core, _tags⟩
  exact FutureWorkAt.waiting inserted (by simp)

/-- The fresh selected mark of a `wait` step has future-conclusion credit. -/
theorem WaitStep.selectedContinuationCredit
    {certificate : Certificate} {before after : ReservationState}
    (step : WaitStep certificate before after) :
    ContinuationCredit certificate after
      step.prepared.stackResult.vertex := by
  exact .futureConclusion step.consumer step.destination.boundary
    step.createdConclusionFutureWorkAt

private def NewStep.connectiveConsumer
    {certificate : Certificate} {before after : ReservationState}
    (step : NewStep certificate before after) :
    ConnectiveBelow certificate step.stackResult.vertex where
  linkIndex := step.tensor.linkIndex
  kind := .tensor
  storedLeft := step.tensor.storedLeft
  storedRight := step.tensor.storedRight
  conclusion := step.tensor.conclusion
  side := step.tensor.side
  consumer_eq := step.tensorValid.1
  link_eq := by
    simpa [SequentialConnectiveKind.asLink] using step.tensorValid.2.1
  wellFormed := by
    simpa [SequentialConnectiveKind.asLink] using step.tensorValid.2.2.1
  premise_eq := step.tensorValid.2.2.2

/-- The fresh selected mark of a `new` step has raw-mate continuation credit. -/
theorem NewStep.selectedContinuationCredit
    {certificate : Certificate} {before after : ReservationState}
    (step : NewStep certificate before after) :
    ContinuationCredit certificate after step.stackResult.vertex := by
  let consumer := step.connectiveConsumer
  apply ContinuationCredit.rawMate consumer
  have afterCore : after.core = step.coreAfter :=
    congrArg ReservationState.core step.output_eq
  rcases certificate.reserveAxiomAt?_exact step.core_reserve_eq with
    ⟨_left, _right, _component, _link, _ready, _componentLookup,
      _frontier, marksEq, _parents, _components, _started, _fired⟩
  change after.core.marks[step.tensor.mate]? = some none
  rw [afterCore, marksEq]
  exact step.mate_unmarked

/-- A `forward` step schedules its selected connective conclusion at the
selected raw boundary. -/
theorem ForwardStep.createdConclusionFutureWorkAt
    {certificate : Certificate} {before after : ReservationState}
    (step : ForwardStep certificate before after) :
    FutureWorkAt after step.prepared.stackResult.rawAge
      step.consumer.conclusion := by
  have afterStack : after.stack = step.stackAfter :=
    congrArg ReservationState.stack step.output_eq
  have middleInvariant :
      ReservationInvariant certificate step.prepared.after :=
    step.prepared.reservationInvariant step.before_invariant
  rcases SequentialStackState.popReadyMark?_exact step.prepared.stack_eq with
    ⟨_top, sigmaTop, _unmarked, _marks, _nextAge, sigmaEquation,
      _ready, _waiting, _marked⟩
  have middleSigmaTop :
      step.prepared.after.stack.sigma.getLast? =
        some step.prepared.stackResult.rawAge := by
    change step.prepared.stackResult.after.sigma.getLast? = _
    rw [sigmaEquation]
    exact sigmaTop
  rcases List.getLast?_eq_some_iff.mp middleSigmaTop with
    ⟨sigmaPrefix, sigmaDecomposition⟩
  have prefixLengths :
      step.prependStep.readyPrefix.length = sigmaPrefix.length := by
    have aligned := middleInvariant.stack_wellShaped.ready_aligned
    change
      step.prepared.stackResult.after.ready.length =
        step.prepared.stackResult.after.sigma.length at aligned
    rw [step.prependStep.ready_eq] at aligned
    change step.prepared.stackResult.after.sigma =
      sigmaPrefix ++ [step.prepared.stackResult.rawAge] at sigmaDecomposition
    rw [sigmaDecomposition] at aligned
    simp at aligned
    omega
  have afterSigma :
      after.stack.sigma = step.prepared.after.stack.sigma := by
    have prependSigma :
        step.stackAfter.sigma = step.prepared.after.stack.sigma := by
      simpa [PreparedStep.after] using
        congrArg SequentialStackState.sigma step.prependStep.after_eq
    exact (congrArg SequentialStackState.sigma afterStack).trans prependSigma
  have afterReady :
      after.stack.ready = step.prependStep.readyPrefix ++
        [step.consumer.conclusion :: step.prependStep.activeReady] := by
    calc
      after.stack.ready = step.stackAfter.ready :=
        congrArg SequentialStackState.ready afterStack
      _ = _ := congrArg SequentialStackState.ready step.prependStep.after_eq
  apply FutureWorkAt.ready
    (position := step.prependStep.readyPrefix.length)
    (bucket := step.consumer.conclusion :: step.prependStep.activeReady)
  · rw [afterSigma, sigmaDecomposition, prefixLengths]
    simp
  · rw [afterReady]
    simp
  · simp

/-- The fresh selected mark of a `forward` step has future-conclusion credit. -/
theorem ForwardStep.selectedContinuationCredit
    {certificate : Certificate} {before after : ReservationState}
    (step : ForwardStep certificate before after) :
    ContinuationCredit certificate after
      step.prepared.stackResult.vertex := by
  exact ContinuationCredit.futureConclusion step.consumer
    step.prepared.stackResult.rawAge
    step.createdConclusionFutureWorkAt

/-- A `unifyPayload` step schedules its selected connective conclusion at the
previous active boundary. -/
theorem UnifyPayloadStep.createdConclusionFutureWorkAt
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after) :
    FutureWorkAt after step.previousBoundary
      step.consumer.conclusion := by
  have afterStack : after.stack = step.stackAfter :=
    congrArg ReservationState.stack step.output_eq
  have afterSigma :
      after.stack.sigma = step.mergeStep.sigmaPrefix ++
        [step.previousBoundary] := by
    rw [afterStack]
    exact step.exact.1
  have afterReady :
      after.stack.ready = step.mergeStep.readyPrefix ++
        [step.consumer.conclusion ::
          (step.payload ++ step.mergeStep.previousReady ++
            step.mergeStep.activeReady)] := by
    rw [afterStack]
    exact step.exact.2.1
  have prefixLengths :
      step.mergeStep.sigmaPrefix.length =
        step.mergeStep.readyPrefix.length := by
    have middleInvariant :
        ReservationInvariant certificate step.prepared.after :=
      step.prepared.reservationInvariant step.before_invariant
    have aligned := middleInvariant.stack_wellShaped.ready_aligned
    change
      step.prepared.stackResult.after.ready.length =
        step.prepared.stackResult.after.sigma.length at aligned
    rw [step.mergeStep.ready_eq, step.mergeStep.sigma_eq] at aligned
    simp at aligned
    omega
  apply FutureWorkAt.ready
    (position := step.mergeStep.sigmaPrefix.length)
    (bucket := step.consumer.conclusion ::
      (step.payload ++ step.mergeStep.previousReady ++
        step.mergeStep.activeReady))
  · rw [afterSigma]
    simp
  · rw [afterReady, prefixLengths]
    simp
  · simp

/-- The fresh selected mark of a `unifyPayload` step has
future-conclusion credit. -/
theorem UnifyPayloadStep.selectedContinuationCredit
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after) :
    ContinuationCredit certificate after
      step.prepared.stackResult.vertex := by
  let consumer :
      ConnectiveBelow certificate step.prepared.stackResult.vertex := {
    linkIndex := step.consumer.linkIndex
    kind := .tensor
    storedLeft := step.consumer.storedLeft
    storedRight := step.consumer.storedRight
    conclusion := step.consumer.conclusion
    side := step.consumer.side
    consumer_eq :=
      Certificate.tensorBelow?_consumer step.consumer_eq
    link_eq := by
      simpa [SequentialConnectiveKind.asLink] using
        Certificate.tensorBelow?_link step.consumer_eq
    wellFormed := by
      simpa [SequentialConnectiveKind.asLink] using
        Certificate.tensorBelow?_wellFormed step.consumer_eq
    premise_eq := Certificate.tensorBelow?_premise step.consumer_eq }
  exact ContinuationCredit.futureConclusion consumer step.previousBoundary
    step.createdConclusionFutureWorkAt

/-- Every fresh non-conclusion raw-mark event receives a branch-local
continuation receipt. This is only the new-event case; it does not transport
inherited receipts or establish a canonical-history invariant. -/
theorem DispatchTagEvidence.newlyMarkedContinuationCredit
    {certificate : Certificate} {before : ReservationState}
    {result : Figure7DispatchResult}
    (evidence : DispatchTagEvidence certificate before result)
    {rawAge : RawTokenAge} {vertex : Vertex}
    (event : evidence.RawMarked rawAge vertex)
    (notConclusion : vertex ∉ certificate.conclusions) :
    ContinuationCredit certificate result.after vertex := by
  cases evidence with
  | concl step =>
      rcases event with ⟨_rfl, rfl⟩
      exact False.elim (notConclusion step.boundary.boundary)
  | nop step =>
      rcases event with ⟨_rfl, rfl⟩
      exact step.selectedContinuationCredit
  | new step =>
      rcases event with ⟨_rfl, rfl⟩
      exact step.selectedContinuationCredit
  | wait step =>
      rcases event with ⟨_rfl, rfl⟩
      exact step.selectedContinuationCredit
  | forward step =>
      rcases event with ⟨_rfl, rfl⟩
      exact step.selectedContinuationCredit
  | unifyPayload step =>
      rcases event with ⟨_rfl, rfl⟩
      exact step.selectedContinuationCredit

end SequentialFigure7
end ProofNetIR
