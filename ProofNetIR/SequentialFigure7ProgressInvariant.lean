import ProofNetIR.SequentialFigure7Dispatcher

namespace ProofNetIR

/-!
# A separate future-waiting storage invariant

This module records that every fixed-capacity waiting cell at or beyond the
currently allocated raw-age horizon is still the paper-level undefined value
`⊥`.  The predicate is deliberately separate from `SchedulerInvariant`:
the existing state-only invariant constrains the allocated waiting domain but
does not constrain unused future storage.

The results below establish the predicate for the exact empty and initialized
states and preserve it through each already-successful Figure-7 rule and the
certified dispatcher history.  They do not prove that a rule is enabled,
dispatcher progress, pure-worklist completeness, fallback removal, or any
complexity bound.
-/

namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge

/-- Every in-bounds waiting cell outside the allocated raw-age horizon remains
the paper-level undefined value `⊥`.

This predicate is intentionally not a field of `SchedulerInvariant` and says
nothing about allocated ages below `nextAge`. -/
def FutureWaitingUndefined (state : ReservationState) : Prop :=
  ∀ age,
    state.stack.nextAge ≤ age →
    age < state.stack.waiting.size →
    state.stack.waiting[age]? = some .undefined

private theorem futureWaitingUndefined_of_same
    {before after : ReservationState}
    (future : FutureWaitingUndefined before)
    (nextAgeEq : after.stack.nextAge = before.stack.nextAge)
    (waitingEq : after.stack.waiting = before.stack.waiting) :
    FutureWaitingUndefined after := by
  intro age ageAfter ageBound
  rw [nextAgeEq] at ageAfter
  rw [waitingEq] at ageBound ⊢
  exact future age ageAfter ageBound

private theorem futureWaitingUndefined_of_set_allocated
    {before after : ReservationState} {index : RawTokenAge}
    {cell : WaitingCell}
    (future : FutureWaitingUndefined before)
    (indexAllocated : index < before.stack.nextAge)
    (nextAgeEq : after.stack.nextAge = before.stack.nextAge)
    (waitingEq :
      after.stack.waiting =
        before.stack.waiting.setIfInBounds index cell) :
    FutureWaitingUndefined after := by
  intro age ageAfter ageBound
  rw [nextAgeEq] at ageAfter
  rw [waitingEq] at ageBound ⊢
  have oldAgeBound : age < before.stack.waiting.size := by
    simpa using ageBound
  have indexNeAge : index ≠ age :=
    Nat.ne_of_lt (Nat.lt_of_lt_of_le indexAllocated ageAfter)
  rw [Array.getElem?_setIfInBounds_ne indexNeAge]
  exact future age ageAfter oldAgeBound

private theorem futureWaitingUndefined_of_increment_set_allocated
    {before after : ReservationState} {index : RawTokenAge}
    {cell : WaitingCell}
    (future : FutureWaitingUndefined before)
    (indexAllocated : index < before.stack.nextAge)
    (nextAgeEq : after.stack.nextAge = before.stack.nextAge + 1)
    (waitingEq :
      after.stack.waiting =
        before.stack.waiting.setIfInBounds index cell) :
    FutureWaitingUndefined after := by
  intro age ageAfter ageBound
  rw [nextAgeEq] at ageAfter
  rw [waitingEq] at ageBound ⊢
  have oldAgeBound : age < before.stack.waiting.size := by
    simpa using ageBound
  have oldAgeAfter : before.stack.nextAge ≤ age :=
    Nat.le_trans (Nat.le_succ before.stack.nextAge) ageAfter
  have indexNeAge : index ≠ age :=
    Nat.ne_of_lt (Nat.lt_of_lt_of_le indexAllocated oldAgeAfter)
  rw [Array.getElem?_setIfInBounds_ne indexNeAge]
  exact future age oldAgeAfter oldAgeBound

/-- The exact empty reservation state has clean future waiting storage. -/
theorem empty_futureWaitingUndefined (certificate : Certificate) :
    FutureWaitingUndefined (ReservationState.empty certificate) := by
  intro age _ ageBound
  have carrierBound : age < certificate.formulas.size := by
    simpa [ReservationState.empty, SequentialStackState.empty] using ageBound
  simp [ReservationState.empty, SequentialStackState.empty, carrierBound]

/-- Every successful exact initialization has clean future waiting storage. -/
theorem InitialReservationStep.futureWaitingUndefined
    {certificate : Certificate} {after : ReservationState} {start : Vertex}
    (step : InitialReservationStep certificate after start) :
    FutureWaitingUndefined after := by
  have ready := (SequentialStackState.initEnqueue?_some_iff.mp step.stack_eq).1
  rcases ready with
    ⟨nextAgeZero, sigmaEmpty, readyEmpty, allMarks, allWaiting,
      waitingPositive, reachedBound, partnerBound, distinct⟩
  rcases SequentialStackState.initEnqueue?_exact step.stack_eq with
    ⟨marksEq, nextAgeEq, sigmaEq, readyEq, waitingEq, activeUndefined⟩
  rw [step.output_eq]
  intro age ageAfter ageBound
  change step.stackAfter.nextAge ≤ age at ageAfter
  change age < step.stackAfter.waiting.size at ageBound
  change step.stackAfter.waiting[age]? = some .undefined
  rw [nextAgeEq] at ageAfter
  rw [waitingEq] at ageBound ⊢
  exact allWaiting.lookup ageBound

/-- The synchronized pop/raw-mark prefix leaves the horizon and waiting array
unchanged. -/
theorem PreparedStep.futureWaitingUndefined
    {before : ReservationState} (step : PreparedStep before)
    (future : FutureWaitingUndefined before) :
    FutureWaitingUndefined step.after := by
  rcases SequentialStackState.popReadyMark?_exact step.stack_eq with
    ⟨topEq, sigmaTopEq, unmarked, marksEq, nextAgeEq, sigmaEq, readyEq,
      waitingEq, marked⟩
  apply futureWaitingUndefined_of_same future
  · simpa [PreparedStep.after] using nextAgeEq
  · simpa [PreparedStep.after] using waitingEq

/-- Successful `concl` preserves clean future waiting storage. -/
theorem ConclStep.futureWaitingUndefined
    {certificate : Certificate} {before after : ReservationState}
    (step : ConclStep certificate before after)
    (future : FutureWaitingUndefined before) :
    FutureWaitingUndefined after := by
  rw [step.output_eq]
  exact step.prepared.futureWaitingUndefined future

/-- Successful `nop` preserves clean future waiting storage. -/
theorem NopStep.futureWaitingUndefined
    {certificate : Certificate} {before after : ReservationState}
    (step : NopStep certificate before after)
    (future : FutureWaitingUndefined before) :
    FutureWaitingUndefined after := by
  rw [step.output_eq]
  exact step.prepared.futureWaitingUndefined future

/-- Successful operational `new` preserves clean future waiting storage. -/
theorem NewStep.futureWaitingUndefined
    {certificate : Certificate} {before after : ReservationState}
    (step : NewStep certificate before after)
    (future : FutureWaitingUndefined before) :
    FutureWaitingUndefined after := by
  let prepared : PreparedStep before := {
    stackResult := step.stackResult
    coreMarked := step.coreMarked
    stack_eq := step.stack_eq
    core_mark_eq := step.core_mark_eq }
  have middleFuture : FutureWaitingUndefined prepared.after :=
    PreparedStep.futureWaitingUndefined prepared future
  rcases
      SequentialStackState.operationalNewEnqueue?_some_iff.mp
        step.stack_enqueue_eq with
    ⟨enqueue⟩
  have activeAllocated :
      enqueue.active < step.stackResult.after.nextAge :=
    enqueue.ready.2.2.1
  have outputStackEq : after.stack = step.stackAfter :=
    congrArg (fun state => state.stack) step.output_eq
  have enqueueNextAgeEq :
      step.stackAfter.nextAge = step.stackResult.after.nextAge + 1 :=
    congrArg (fun state => state.nextAge) enqueue.after_eq
  have enqueueWaitingEq :
      step.stackAfter.waiting =
        step.stackResult.after.waiting.setIfInBounds enqueue.active
          (.initialized []) :=
    congrArg (fun state => state.waiting) enqueue.after_eq
  apply futureWaitingUndefined_of_increment_set_allocated
      (before := prepared.after) (index := enqueue.active)
      (cell := .initialized []) middleFuture activeAllocated
  · exact (congrArg (fun state => state.nextAge) outputStackEq).trans
      enqueueNextAgeEq
  · exact (congrArg (fun state => state.waiting) outputStackEq).trans
      enqueueWaitingEq

/-- Successful `wait` writes only an already allocated waiting boundary. -/
theorem WaitStep.futureWaitingUndefined
    {certificate : Certificate} {before after : ReservationState}
    (step : WaitStep certificate before after)
    (future : FutureWaitingUndefined before) :
    FutureWaitingUndefined after := by
  have middleFuture := step.prepared.futureWaitingUndefined future
  have middleInvariant :
      ReservationInvariant certificate step.prepared.after :=
    step.prepared.reservationInvariant step.before_invariant
  have boundaryAllocated :
      step.destination.boundary < step.prepared.after.stack.nextAge :=
    middleInvariant.stack_wellShaped.sigma_partition.boundary_lt
      step.destination.boundary
      (sigmaBoundary?_mem step.destination.boundary_eq)
  rcases
      SequentialStackState.prependWaiting?_some_iff.mp
        step.destination.stack_eq with
    ⟨prepend⟩
  have outputStackEq : after.stack = step.destination.stackAfter :=
    congrArg (fun state => state.stack) step.destination.output_eq
  have prependNextAgeEq :
      step.destination.stackAfter.nextAge =
        step.prepared.after.stack.nextAge := by
    simpa [PreparedStep.after] using
      congrArg (fun state => state.nextAge) prepend.after_eq
  have prependWaitingEq :
      step.destination.stackAfter.waiting =
        step.prepared.after.stack.waiting.setIfInBounds
          step.destination.boundary
          (.initialized (step.consumer.conclusion :: prepend.payload)) := by
    simpa [PreparedStep.after] using
      congrArg (fun state => state.waiting) prepend.after_eq
  apply futureWaitingUndefined_of_set_allocated
      (before := step.prepared.after) (index := step.destination.boundary)
      (cell := .initialized (step.consumer.conclusion :: prepend.payload))
      middleFuture boundaryAllocated
  · exact (congrArg (fun state => state.nextAge) outputStackEq).trans
      prependNextAgeEq
  · exact (congrArg (fun state => state.waiting) outputStackEq).trans
      prependWaitingEq

/-- Successful `forward` changes only production data and the ready top after
the common prefix. -/
theorem ForwardStep.futureWaitingUndefined
    {certificate : Certificate} {before after : ReservationState}
    (step : ForwardStep certificate before after)
    (future : FutureWaitingUndefined before) :
    FutureWaitingUndefined after := by
  have middleFuture := step.prepared.futureWaitingUndefined future
  have outputStackEq : after.stack = step.stackAfter :=
    congrArg (fun state => state.stack) step.output_eq
  have prependNextAgeEq :
      step.stackAfter.nextAge = step.prepared.after.stack.nextAge := by
    simpa [PreparedStep.after] using
      congrArg (fun state => state.nextAge) step.prependStep.after_eq
  have prependWaitingEq :
      step.stackAfter.waiting = step.prepared.after.stack.waiting := by
    simpa [PreparedStep.after] using
      congrArg (fun state => state.waiting) step.prependStep.after_eq
  apply futureWaitingUndefined_of_same
      (before := step.prepared.after) middleFuture
  · exact (congrArg (fun state => state.nextAge) outputStackEq).trans
      prependNextAgeEq
  · exact (congrArg (fun state => state.waiting) outputStackEq).trans
      prependWaitingEq

/-- Successful arbitrary-payload `unify` clears only an allocated previous
boundary and therefore preserves clean future storage. -/
theorem UnifyPayloadStep.futureWaitingUndefined
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after)
    (future : FutureWaitingUndefined before) :
    FutureWaitingUndefined after := by
  have middleFuture := step.prepared.futureWaitingUndefined future
  have middleInvariant :
      ReservationInvariant certificate step.prepared.after :=
    step.prepared.reservationInvariant step.before_invariant
  have previousMembership :
      step.previousBoundary ∈ step.prepared.after.stack.sigma := by
    change step.previousBoundary ∈ step.prepared.stackResult.after.sigma
    rw [step.mergeStep.sigma_eq]
    simp
  have previousAllocated :
      step.previousBoundary < step.prepared.after.stack.nextAge :=
    middleInvariant.stack_wellShaped.sigma_partition.boundary_lt
      step.previousBoundary previousMembership
  have outputStackEq : after.stack = step.stackAfter :=
    congrArg (fun state => state.stack) step.output_eq
  have mergeNextAgeEq :
      step.stackAfter.nextAge = step.prepared.after.stack.nextAge := by
    simpa [PreparedStep.after] using
      congrArg (fun state => state.nextAge) step.mergeStep.after_eq
  have mergeWaitingEq :
      step.stackAfter.waiting =
        step.prepared.after.stack.waiting.setIfInBounds
          step.previousBoundary .undefined := by
    simpa [PreparedStep.after] using
      congrArg (fun state => state.waiting) step.mergeStep.after_eq
  apply futureWaitingUndefined_of_set_allocated
      (before := step.prepared.after) (index := step.previousBoundary)
      (cell := .undefined) middleFuture previousAllocated
  · exact (congrArg (fun state => state.nextAge) outputStackEq).trans
      mergeNextAgeEq
  · exact (congrArg (fun state => state.waiting) outputStackEq).trans
      mergeWaitingEq

/-- Every typed successful canonical rule preserves clean future storage. -/
theorem Figure7SuccessfulStep.futureWaitingUndefined
    {certificate : Certificate} {before after : ReservationState}
    (step : Figure7SuccessfulStep certificate before after)
    (future : FutureWaitingUndefined before) :
    FutureWaitingUndefined after := by
  cases step with
  | concl step => exact step.futureWaitingUndefined future
  | nop step => exact step.futureWaitingUndefined future
  | new step => exact step.futureWaitingUndefined future
  | wait step => exact step.futureWaitingUndefined future
  | forward step => exact step.futureWaitingUndefined future
  | unifyPayload step => exact step.futureWaitingUndefined future

/-- Every exact priority-aware dispatcher success preserves clean future
storage. -/
theorem DispatchStep.futureWaitingUndefined
    {certificate : Certificate} {before : ReservationState}
    {invariant : SchedulerInvariant certificate before}
    {result : Figure7DispatchResult}
    (step : DispatchStep certificate before invariant result)
    (future : FutureWaitingUndefined before) :
    FutureWaitingUndefined result.after := by
  rcases step.toSuccessfulStep with ⟨successful⟩
  exact successful.futureWaitingUndefined future

/-- Every exact canonical dispatcher history has clean future waiting storage.

This is a history induction over already-successful steps, not a dispatcher
enabledness or progress theorem. -/
theorem ExecutedHistory.futureWaitingUndefined
    {certificate : Certificate} {state : ReservationState}
    (history : ExecutedHistory certificate state) :
    FutureWaitingUndefined state := by
  induction history with
  | empty => exact empty_futureWaitingUndefined certificate
  | init step =>
      exact InitialReservationStep.futureWaitingUndefined step
  | later history invariant step induction =>
      exact step.futureWaitingUndefined induction

/-- Certified dispatcher reachability implies clean future waiting storage. -/
theorem ReachableByImplementedDispatcher.futureWaitingUndefined
    {certificate : Certificate} {state : ReservationState}
    (reachable : ReachableByImplementedDispatcher certificate state) :
    FutureWaitingUndefined state := by
  rcases reachable with ⟨history⟩
  exact history.futureWaitingUndefined

end SequentialFigure7

end ProofNetIR
