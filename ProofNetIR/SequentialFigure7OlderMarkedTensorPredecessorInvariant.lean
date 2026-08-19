/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7TensorAdjacency
import ProofNetIR.SequentialFigure7CrossRepresentativeStablePreservation

/-!
# Older marked-tensor predecessor invariant

Defines an indexed, all-future-work adjacency invariant and projects its
active-ready instance to the existing `SigmaPredecessorInput` API. The
invariant is established for the empty and initialized states and preserved
by the synchronized prepared prefix and the stable `concl` and `nop`
branches.

This module does not claim preservation by `new`, `wait`, `forward`, or
`unifyPayload`, nor full canonical-history availability.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialUnification
open SequentialSchedulerBridge
open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState

/-- Indexed evidence that a marked tensor mate resolves to the sigma boundary
immediately preceding one future-work boundary. -/
structure SigmaImmediatePredecessorAt
    (sigma : List RawTokenAge)
    (candidateBoundary mateRawAge previousBoundary : RawTokenAge) : Type where
  position : Nat
  previous_at : sigma[position]? = some previousBoundary
  candidate_at : sigma[position + 1]? = some candidateBoundary
  mate_boundary :
    sigmaBoundary? sigma mateRawAge = some previousBoundary

/-- Every marked tensor mate whose current representative is strictly below
that of a ready or waiting future-work occurrence has an indexed immediate
sigma predecessor. -/
def OlderMarkedTensorPredecessorInvariant
    (certificate : Certificate) (state : ReservationState) : Prop :=
  ∀ {candidateRawAge candidateVertex},
    FutureWorkAt state candidateRawAge candidateVertex →
      ∀ (consumer : ConnectiveBelow certificate candidateVertex),
        consumer.kind = .tensor →
          ∀ {mateRawAge},
            state.core.marks[consumer.mate]? = some (some mateRawAge) →
              state.core.representative mateRawAge <
                  state.core.representative candidateRawAge →
                ∃ previousBoundary,
                  Nonempty
                    (SigmaImmediatePredecessorAt state.stack.sigma
                      candidateRawAge mateRawAge previousBoundary)



namespace OlderMarkedTensorPredecessorInvariant

/-- Internal projection once the representative order is already known. -/
private theorem readyHead_predecessor_of_older
    {certificate : Certificate} {state : ReservationState}
    (allWork :
      OlderMarkedTensorPredecessorInvariant certificate state)
    (invariant : SchedulerInvariant certificate state)
    (head : ReadyHeadInput state)
    (consumer : ConnectiveBelow certificate head.vertex)
    (tensorKind : consumer.kind = .tensor)
    {mateRawAge : RawTokenAge}
    (mateMarked :
      state.core.marks[consumer.mate]? = some (some mateRawAge))
    (older :
      state.core.representative mateRawAge <
        state.core.representative head.rawAge) :
    ∃ previousBoundary,
      Nonempty
        (SigmaPredecessorInput state.stack.sigma head.rawAge mateRawAge
          previousBoundary) := by
  rcases allWork (head.futureWorkAt invariant) consumer tensorKind
      mateMarked older with
    ⟨previousBoundary, ⟨predecessor⟩⟩
  have candidatePositionBound :
      predecessor.position + 1 < state.stack.sigma.length :=
    (List.getElem?_eq_some_iff.mp predecessor.candidate_at).choose
  have lastLookup :
      state.stack.sigma[state.stack.sigma.length - 1]? =
        some head.rawAge := by
    rw [← List.getLast?_eq_getElem?]
    exact head.sigma_top
  rcases List.getElem?_eq_some_iff.mp predecessor.candidate_at with
    ⟨candidateBound, candidateValue⟩
  rcases List.getElem?_eq_some_iff.mp lastLookup with
    ⟨lastBound, lastValue⟩
  have candidatePosition :
      predecessor.position + 1 = state.stack.sigma.length - 1 := by
    have candidateLe :
        predecessor.position + 1 ≤ state.stack.sigma.length - 1 := by
      omega
    have lastLeCandidate :
        state.stack.sigma.length - 1 ≤ predecessor.position + 1 := by
      by_cases le : state.stack.sigma.length - 1 ≤ predecessor.position + 1
      · exact le
      · have candidateLtLast :
            predecessor.position + 1 < state.stack.sigma.length - 1 :=
          Nat.lt_of_not_ge le
        have strict :=
          (List.pairwise_iff_getElem.mp
            invariant.stack_wellShaped.sigma_partition.strictIncreasing)
              (predecessor.position + 1)
              (state.stack.sigma.length - 1)
              candidateBound lastBound candidateLtLast
        rw [candidateValue, lastValue] at strict
        exact False.elim (Nat.lt_irrefl _ strict)
    exact Nat.le_antisymm candidateLe lastLeCandidate
  have sigmaLengthGtOne : 1 < state.stack.sigma.length := by
    omega
  have previousPosition :
      predecessor.position = state.stack.sigma.length - 2 := by
    omega
  refine ⟨previousBoundary, ⟨{
    active_top := head.sigma_top
    previous_top := ?_
    mate_boundary := predecessor.mate_boundary }⟩⟩
  rw [List.getLast?_dropLast, if_neg (Nat.not_le_of_gt sigmaLengthGtOne)]
  simpa [previousPosition] using predecessor.previous_at

/-- Project the invariant from the strict sigma-boundary evidence carried by
the current ready-head dispatch residual. -/
theorem readyHead_predecessor_of_boundary_lt
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
          previousBoundary) := by
  have stackMateMarked :
      state.stack.marks[consumer.mate]? = some (some mateRawAge) := by
    rw [← invariant.realizesSigma.marks_eq]
    exact mateMarked
  have mateAgeBound : mateRawAge < state.stack.nextAge :=
    invariant.stack_wellShaped.assigned_age_bound
      consumer.mate mateRawAge stackMateMarked
  have mateRealized :=
    invariant.realizesSigma.representative_eq_boundary mateAgeBound
  have mateRepresentative :
      state.core.representative mateRawAge = mateBoundary :=
    Option.some.inj (mateRealized.symm.trans mateBoundaryLookup)
  have headRepresentative :
      state.core.representative head.rawAge = head.rawAge :=
    (head.futureWorkAt invariant).representative_eq_rawAge invariant
  have representativeLt :
      state.core.representative mateRawAge <
        state.core.representative head.rawAge := by
    rw [mateRepresentative, headRepresentative]
    exact mateBoundaryLt
  exact allWork.readyHead_predecessor_of_older invariant head consumer
    tensorKind mateMarked representativeLt

end OlderMarkedTensorPredecessorInvariant

/-- The empty reservation state satisfies the invariant vacuously. -/
theorem empty_olderMarkedTensorPredecessorInvariant
    (certificate : Certificate) :
    OlderMarkedTensorPredecessorInvariant certificate
      (ReservationState.empty certificate) := by
  intro candidateRawAge candidateVertex work
  cases work with
  | ready sigmaAt _readyAt _member =>
      simp [ReservationState.empty, SequentialStackState.empty] at sigmaAt
  | waiting waitingAt _member =>
      by_cases ageBound : candidateRawAge < certificate.formulas.size <;>
        simp [ReservationState.empty, SequentialStackState.empty,
          ageBound] at waitingAt

/-- Initial reservation preserves the empty raw-mark array and establishes
the invariant. -/
theorem InitialReservationStep.olderMarkedTensorPredecessorInvariant
    {certificate : Certificate} {after : ReservationState}
    {start : Vertex}
    (step : InitialReservationStep certificate after start) :
    OlderMarkedTensorPredecessorInvariant certificate after := by
  intro candidateRawAge candidateVertex _work consumer _tensorKind
    mateRawAge mateMarked _older
  rw [step.output_eq] at mateMarked
  change step.coreAfter.marks[consumer.mate]? =
    some (some mateRawAge) at mateMarked
  rcases certificate.reserveAxiomAt?_exact step.core_eq with
    ⟨_left, _right, _component, _link, _ready, _componentEq, _frontier,
      marksEq, _parents, _components, _started, _fired⟩
  rw [marksEq] at mateMarked
  by_cases vertexBound : consumer.mate < certificate.formulas.size <;>
    simp [ReservationState.empty, Certificate.initialUnificationState,
      vertexBound] at mateMarked

private theorem PreparedStep.selected_not_strictly_older_than_work
    {certificate : Certificate} {before : ReservationState}
    (step : PreparedStep before)
    (invariant : SchedulerInvariant certificate before)
    {candidateRawAge candidateVertex}
    (work : FutureWorkAt step.after candidateRawAge candidateVertex) :
    ¬ step.after.core.representative step.stackResult.rawAge <
        step.after.core.representative candidateRawAge := by
  intro older
  have afterInvariant : SchedulerInvariant certificate step.after :=
    step.schedulerInvariant invariant
  rcases SequentialStackState.popReadyMark?_exact step.stack_eq with
    ⟨_topReady, sigmaTopBefore, _selectedUnmarked, _stackMarks,
      _nextAge, sigmaEq, _readyEq, _waitingEq, stackSelectedMarked⟩
  have sigmaTopAfter :
      step.stackResult.after.sigma.getLast? =
        some step.stackResult.rawAge := by
    rw [sigmaEq]
    exact sigmaTopBefore
  have activeAgeBound :
      step.stackResult.rawAge < step.stackResult.after.nextAge :=
    afterInvariant.stack_wellShaped.assigned_age_bound
      step.stackResult.vertex step.stackResult.rawAge stackSelectedMarked
  have activeBoundary :=
    afterInvariant.stack_wellShaped.sigma_partition.sigmaBoundary?_eq_top
      sigmaTopAfter
  have activeRealized :=
    afterInvariant.realizesSigma.representative_eq_boundary activeAgeBound
  have activeRoot :
      step.after.core.representative step.stackResult.rawAge =
        step.stackResult.rawAge := by
    exact Option.some.inj (activeRealized.symm.trans activeBoundary)
  have candidateAgeBound :
      candidateRawAge < step.after.stack.nextAge :=
    work.rawAge_lt_nextAge afterInvariant
  have candidateRoot :
      step.after.core.representative candidateRawAge = candidateRawAge :=
    work.representative_eq_rawAge afterInvariant
  have candidateLeActive :
      candidateRawAge ≤ step.stackResult.rawAge := by
    by_cases candidateLe : candidateRawAge ≤ step.stackResult.rawAge
    · exact candidateLe
    · have activeLtCandidate :
          step.stackResult.rawAge < candidateRawAge :=
        Nat.lt_of_not_ge candidateLe
      have topLookup :=
        afterInvariant.stack_wellShaped.sigma_partition
          |>.sigmaBoundary?_eq_top_of_le sigmaTopAfter
            (Nat.le_of_lt activeLtCandidate) candidateAgeBound
      have candidateRealized :=
        afterInvariant.realizesSigma.representative_eq_boundary
          candidateAgeBound
      have representativeEq :
          step.after.core.representative candidateRawAge =
            step.stackResult.rawAge :=
        Option.some.inj (candidateRealized.symm.trans topLookup)
      have candidateEq :
          candidateRawAge = step.stackResult.rawAge :=
        candidateRoot.symm.trans representativeEq
      exact False.elim
        ((Nat.ne_of_lt activeLtCandidate) candidateEq.symm)
  rw [activeRoot, candidateRoot] at older
  exact (Nat.not_lt_of_ge candidateLeActive) older

/-- The pop/raw-mark prefix preserves the invariant. The scheduler invariant
rules out the newly selected mark as a strictly older mate of retained work. -/
theorem PreparedStep.olderMarkedTensorPredecessorInvariant
    {certificate : Certificate} {before : ReservationState}
    (step : PreparedStep before)
    (invariant : SchedulerInvariant certificate before)
    (prior :
      OlderMarkedTensorPredecessorInvariant certificate before) :
    OlderMarkedTensorPredecessorInvariant certificate step.after := by
  intro candidateRawAge candidateVertex work consumer tensorKind
    mateRawAge mateMarkedAfter representativeLt
  have oldWork : FutureWorkAt before candidateRawAge candidateVertex :=
    work.beforePrepared step
  rcases UnificationState.markReadyRaw?_exact step.core_mark_eq with
    ⟨_selectedUnmarked, afterMarks, _parents, _components, _started,
      _fired, selectedMarked⟩
  by_cases selectedEq : step.stackResult.vertex = consumer.mate
  · have mateMarkedSelected :
        step.after.core.marks[step.stackResult.vertex]? =
          some (some mateRawAge) := by
      simpa [selectedEq] using mateMarkedAfter
    have mateAgeEq : mateRawAge = step.stackResult.rawAge := by
      exact
        Option.some.inj
          (Option.some.inj (mateMarkedSelected.symm.trans selectedMarked))
    subst mateRawAge
    exact False.elim
      (step.selected_not_strictly_older_than_work invariant work
        representativeLt)
  · have beforeMarked :
        before.core.marks[consumer.mate]? =
          some (some mateRawAge) := by
      change step.coreMarked.marks[consumer.mate]? =
        some (some mateRawAge) at mateMarkedAfter
      rw [afterMarks] at mateMarkedAfter
      simpa [Array.getElem?_setIfInBounds, selectedEq] using mateMarkedAfter
    have representativeLtBefore :
        before.core.representative mateRawAge <
          before.core.representative candidateRawAge := by
      rw [← step.after_representative_eq_before mateRawAge,
        ← step.after_representative_eq_before candidateRawAge]
      exact representativeLt
    rcases prior oldWork consumer tensorKind beforeMarked
        representativeLtBefore with
      ⟨previousBoundary, ⟨predecessor⟩⟩
    have sigmaEq :
        step.stackResult.after.sigma = before.stack.sigma :=
      (SequentialStackState.popReadyMark?_exact step.stack_eq)
        |>.2.2.2.2.2.1
    refine ⟨previousBoundary, ⟨?_⟩⟩
    simpa [PreparedStep.after, sigmaEq] using predecessor

/-- A successful `concl` branch preserves the invariant through its prepared
prefix. -/
theorem ConclStep.olderMarkedTensorPredecessorInvariant
    {certificate : Certificate} {before after : ReservationState}
    (step : ConclStep certificate before after)
    (invariant : SchedulerInvariant certificate before)
    (prior :
      OlderMarkedTensorPredecessorInvariant certificate before) :
    OlderMarkedTensorPredecessorInvariant certificate after := by
  rw [step.output_eq]
  exact step.prepared.olderMarkedTensorPredecessorInvariant invariant prior

/-- A successful `nop` branch preserves the invariant through its prepared
prefix. -/
theorem NopStep.olderMarkedTensorPredecessorInvariant
    {certificate : Certificate} {before after : ReservationState}
    (step : NopStep certificate before after)
    (invariant : SchedulerInvariant certificate before)
    (prior :
      OlderMarkedTensorPredecessorInvariant certificate before) :
    OlderMarkedTensorPredecessorInvariant certificate after := by
  rw [step.output_eq]
  exact step.prepared.olderMarkedTensorPredecessorInvariant invariant prior


end SequentialFigure7
end ProofNetIR
