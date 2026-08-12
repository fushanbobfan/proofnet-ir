import ProofNetIR.SequentialFigure7ReservationLedger

namespace ProofNetIR

/-!
# Canonical Figure-7 commitment spine

This module recovers the allocation event behind every adjacent pair of raw
ages retained in a canonical scheduler state's `sigma` stack.  Stable rules
leave the stack unchanged, `new` appends one exact parent-child commitment,
and `unifyPayload` removes only the active top boundary.

The result is allocation ancestry for the current `sigma` stack only.  It
does not provide vertex paths, target avoidance, raw-mark separation,
enabledness, progress, worklist completeness, fallback removal, or a
complexity bound.
-/

namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge

namespace ReservationEvent

/-- One historical `new` event commits the then-active boundary to the fresh
raw age allocated by that exact dependent step. -/
inductive Commits {certificate : Certificate} :
    ReservationEvent certificate → RawTokenAge → RawTokenAge → Prop where
  /-- The selected active age is the parent of the event's fresh raw age. -/
  | new {before after : ReservationState}
      (step : NewStep certificate before after) :
      Commits (.new step) step.stackResult.rawAge
        (ReservationEvent.new step).rawAge

end ReservationEvent

namespace CanonicalTagHistory

/-- Every adjacent pair of retained `sigma` boundaries is justified by the
exact `new` event stored at the child's chronological raw-age slot. -/
def CommitmentSpine
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history) : Prop :=
  ∀ position parent child,
    state.stack.sigma[position]? = some parent →
    state.stack.sigma[position + 1]? = some child →
    ∃ event : ReservationEvent certificate,
      tagHistory.reservationLedger[child]? = some event ∧
        event.Commits parent child

private theorem prepared_sigma_eq_before
    {before : ReservationState} (step : PreparedStep before) :
    step.after.stack.sigma = before.stack.sigma := by
  change step.stackResult.after.sigma = before.stack.sigma
  rcases SequentialStackState.popReadyMark?_exact step.stack_eq with
    ⟨_top, _sigmaTop, _unmarked, _marks, _nextAge, sigma, _ready,
      _waiting, _marked⟩
  exact sigma

private theorem concl_sigma_eq_before
    {certificate : Certificate} {before after : ReservationState}
    (step : ConclStep certificate before after) :
    after.stack.sigma = before.stack.sigma := by
  rw [step.output_eq]
  exact prepared_sigma_eq_before step.prepared

private theorem nop_sigma_eq_before
    {certificate : Certificate} {before after : ReservationState}
    (step : NopStep certificate before after) :
    after.stack.sigma = before.stack.sigma := by
  rw [step.output_eq]
  exact prepared_sigma_eq_before step.prepared

private theorem wait_sigma_eq_before
    {certificate : Certificate} {before after : ReservationState}
    (step : WaitStep certificate before after) :
    after.stack.sigma = before.stack.sigma := by
  rcases step.destination.exact with
    ⟨_payload, _initialized, _updated, _marks, _nextAge, sigma,
      _ready, _core, _tags⟩
  exact sigma.trans (prepared_sigma_eq_before step.prepared)

private theorem forward_sigma_eq_before
    {certificate : Certificate} {before after : ReservationState}
    (step : ForwardStep certificate before after) :
    after.stack.sigma = before.stack.sigma := by
  have outputStack : after.stack = step.stackAfter :=
    congrArg (fun state : ReservationState ↦ state.stack) step.output_eq
  have prependSigma :
      step.stackAfter.sigma = step.prepared.stackResult.after.sigma := by
    simpa using congrArg
      (fun stack : SequentialStackState ↦ stack.sigma)
      step.prependStep.after_eq
  exact
    (congrArg (fun stack : SequentialStackState ↦ stack.sigma) outputStack)
      |>.trans (prependSigma.trans
        (prepared_sigma_eq_before step.prepared))

private theorem new_sigma_eq_before_append
    {certificate : Certificate} {before after : ReservationState}
    (step : NewStep certificate before after) :
    after.stack.sigma = before.stack.sigma ++ [before.stack.nextAge] := by
  rcases SequentialStackState.popReadyMark?_exact step.stack_eq with
    ⟨_top, _sigmaTop, _unmarked, _marks, nextAge, sigma, _ready,
      _waiting, _marked⟩
  rcases SequentialStackState.operationalNewEnqueue?_exact
      step.stack_enqueue_eq with
    ⟨_active, _activeEq, _activeLt, _marks, _nextAge, appended,
      _ready, _waiting, _activeInitialized, _freshUndefined⟩
  have outputStack : after.stack = step.stackAfter :=
    congrArg (fun state : ReservationState ↦ state.stack) step.output_eq
  calc
    after.stack.sigma = step.stackAfter.sigma :=
      congrArg (fun stack : SequentialStackState ↦ stack.sigma) outputStack
    _ = step.stackResult.after.sigma ++
          [step.stackResult.after.nextAge] := appended
    _ = before.stack.sigma ++ [before.stack.nextAge] := by
      rw [sigma, nextAge]

private theorem new_parent_top
    {certificate : Certificate} {before after : ReservationState}
    (step : NewStep certificate before after) :
    before.stack.sigma.getLast? = some step.stackResult.rawAge := by
  rcases SequentialStackState.popReadyMark?_exact step.stack_eq with
    ⟨_top, sigmaTop, _unmarked, _marks, _nextAge, _sigma, _ready,
      _waiting, _marked⟩
  exact sigmaTop

private theorem unify_before_sigma_eq_after_append_active
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after) :
    before.stack.sigma =
      after.stack.sigma ++ [step.mergeStep.activeBoundary] := by
  have middleSigma :
      step.prepared.after.stack.sigma =
        step.mergeStep.sigmaPrefix ++
          [step.previousBoundary, step.mergeStep.activeBoundary] := by
    simpa [PreparedStep.after] using step.mergeStep.sigma_eq
  have beforeSigma :
      before.stack.sigma =
        step.mergeStep.sigmaPrefix ++
          [step.previousBoundary, step.mergeStep.activeBoundary] :=
    (prepared_sigma_eq_before step.prepared).symm.trans middleSigma
  have outputStack : after.stack = step.stackAfter :=
    congrArg (fun state : ReservationState ↦ state.stack) step.output_eq
  have afterSigma :
      after.stack.sigma =
        step.mergeStep.sigmaPrefix ++ [step.previousBoundary] := by
    calc
      after.stack.sigma = step.stackAfter.sigma :=
        congrArg (fun stack : SequentialStackState ↦ stack.sigma)
          outputStack
      _ = step.mergeStep.sigmaPrefix ++ [step.previousBoundary] := by
        simpa using congrArg
          (fun stack : SequentialStackState ↦ stack.sigma)
          step.mergeStep.after_eq
  rw [beforeSigma, afterSigma]
  simp [List.append_assoc]

private theorem empty_commitmentSpine :
    (CanonicalTagHistory.empty
      (certificate := certificate)).CommitmentSpine := by
  intro position parent child _first second
  have bound := (List.getElem?_eq_some_iff.mp second).choose
  simp [ReservationState.empty, SequentialStackState.empty] at bound

private theorem init_commitmentSpine
    {certificate : Certificate} {after : ReservationState} {start : Vertex}
    (step : InitialReservationStep certificate after start) :
    (CanonicalTagHistory.init step).CommitmentSpine := by
  intro position parent child _first second
  rcases SequentialStackState.initEnqueue?_exact step.stack_eq with
    ⟨_marks, _nextAge, sigma, _ready, _waiting, _activeUndefined⟩
  have outputStack : after.stack = step.stackAfter :=
    congrArg (fun state : ReservationState ↦ state.stack) step.output_eq
  have afterSigma : after.stack.sigma = [0] :=
    (congrArg (fun stack : SequentialStackState ↦ stack.sigma) outputStack)
      |>.trans sigma
  rw [afterSigma] at second
  have bound := (List.getElem?_eq_some_iff.mp second).choose
  simp at bound

private theorem later_stable_commitmentSpine
    {certificate : Certificate} {before : ReservationState}
    {result : Figure7DispatchResult}
    {history : ExecutedHistory certificate before}
    {invariant : SchedulerInvariant certificate before}
    {dispatch : DispatchStep certificate before invariant result}
    (prior : CanonicalTagHistory certificate history)
    (evidence : DispatchTagEvidence certificate before result)
    (priorSpine : prior.CommitmentSpine)
    (sigmaEq : result.after.stack.sigma = before.stack.sigma)
    (eventsEq : evidence.reservationEvents = []) :
    (CanonicalTagHistory.later
      (invariant := invariant) (dispatch := dispatch)
      prior evidence).CommitmentSpine := by
  intro position parent child first second
  have oldFirst : before.stack.sigma[position]? = some parent := by
    rw [← sigmaEq]
    exact first
  have oldSecond :
      before.stack.sigma[position + 1]? = some child := by
    rw [← sigmaEq]
    exact second
  rcases priorSpine position parent child oldFirst oldSecond with
    ⟨event, lookup, commits⟩
  refine ⟨event, ?_, commits⟩
  simpa [reservationLedger, eventsEq] using lookup

private theorem later_concl_commitmentSpine
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    {invariant : SchedulerInvariant certificate before}
    {dispatch :
      DispatchStep certificate before invariant ⟨.concl, after⟩}
    (prior : CanonicalTagHistory certificate history)
    (step : ConclStep certificate before after)
    (priorSpine : prior.CommitmentSpine) :
    (CanonicalTagHistory.later
      (invariant := invariant) (dispatch := dispatch)
      prior (.concl step)).CommitmentSpine :=
  later_stable_commitmentSpine prior (.concl step) priorSpine
    (concl_sigma_eq_before step) rfl

private theorem later_nop_commitmentSpine
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    {invariant : SchedulerInvariant certificate before}
    {dispatch : DispatchStep certificate before invariant ⟨.nop, after⟩}
    (prior : CanonicalTagHistory certificate history)
    (step : NopStep certificate before after)
    (priorSpine : prior.CommitmentSpine) :
    (CanonicalTagHistory.later
      (invariant := invariant) (dispatch := dispatch)
      prior (.nop step)).CommitmentSpine :=
  later_stable_commitmentSpine prior (.nop step) priorSpine
    (nop_sigma_eq_before step) rfl

private theorem later_wait_commitmentSpine
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    {invariant : SchedulerInvariant certificate before}
    {dispatch : DispatchStep certificate before invariant ⟨.wait, after⟩}
    (prior : CanonicalTagHistory certificate history)
    (step : WaitStep certificate before after)
    (priorSpine : prior.CommitmentSpine) :
    (CanonicalTagHistory.later
      (invariant := invariant) (dispatch := dispatch)
      prior (.wait step)).CommitmentSpine :=
  later_stable_commitmentSpine prior (.wait step) priorSpine
    (wait_sigma_eq_before step) rfl

private theorem later_forward_commitmentSpine
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    {invariant : SchedulerInvariant certificate before}
    {dispatch : DispatchStep certificate before invariant ⟨.forward, after⟩}
    (prior : CanonicalTagHistory certificate history)
    (step : ForwardStep certificate before after)
    (priorSpine : prior.CommitmentSpine) :
    (CanonicalTagHistory.later
      (invariant := invariant) (dispatch := dispatch)
      prior (.forward step)).CommitmentSpine :=
  later_stable_commitmentSpine prior (.forward step) priorSpine
    (forward_sigma_eq_before step) rfl

private theorem later_new_commitmentSpine
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    {invariant : SchedulerInvariant certificate before}
    {dispatch : DispatchStep certificate before invariant ⟨.new, after⟩}
    (prior : CanonicalTagHistory certificate history)
    (step : NewStep certificate before after)
    (priorSpine : prior.CommitmentSpine) :
    (CanonicalTagHistory.later
      (invariant := invariant) (dispatch := dispatch)
      prior (.new step)).CommitmentSpine := by
  intro position parent child first second
  have afterSigma := new_sigma_eq_before_append step
  rw [afterSigma] at first second
  have secondBound :
      position + 1 <
        (before.stack.sigma ++ [before.stack.nextAge]).length :=
    (List.getElem?_eq_some_iff.mp second).choose
  by_cases oldSecond : position + 1 < before.stack.sigma.length
  · have oldFirstBound : position < before.stack.sigma.length := by
      omega
    have oldFirst : before.stack.sigma[position]? = some parent := by
      rw [List.getElem?_append_left oldFirstBound] at first
      exact first
    have oldSecondLookup :
        before.stack.sigma[position + 1]? = some child := by
      rw [List.getElem?_append_left oldSecond] at second
      exact second
    rcases priorSpine position parent child oldFirst oldSecondLookup with
      ⟨event, lookup, commits⟩
    have eventBound : child < prior.reservationLedger.length :=
      (List.getElem?_eq_some_iff.mp lookup).choose
    refine ⟨event, ?_, commits⟩
    change
      (prior.reservationLedger ++ [.new step])[child]? = some event
    rw [List.getElem?_append_left eventBound]
    exact lookup
  · have lastPosition :
        position + 1 = before.stack.sigma.length := by
      simp only [List.length_append, List.length_singleton] at secondBound
      omega
    have childEq : child = before.stack.nextAge := by
      rw [List.getElem?_append_right (by omega)] at second
      simp [lastPosition] at second
      exact second.symm
    rcases List.getLast?_eq_some_iff.mp (new_parent_top step) with
      ⟨sigmaPrefix, sigmaEq⟩
    have positionEq : position = sigmaPrefix.length := by
      rw [sigmaEq] at lastPosition
      simp at lastPosition
      omega
    have oldFirstBound : position < before.stack.sigma.length := by
      omega
    have parentEq : parent = step.stackResult.rawAge := by
      rw [List.getElem?_append_left oldFirstBound] at first
      rw [sigmaEq, positionEq,
        List.getElem?_append_right (Nat.le_refl _)] at first
      simp at first
      exact first.symm
    subst parent
    subst child
    refine ⟨.new step, ?_, ReservationEvent.Commits.new step⟩
    change
      (prior.reservationLedger ++ [.new step])[before.stack.nextAge]? =
        some (.new step)
    rw [List.getElem?_append_right]
    · simp [prior.reservationLedger_length]
    · rw [prior.reservationLedger_length]
      exact Nat.le_refl _

private theorem later_unifyPayload_commitmentSpine
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    {invariant : SchedulerInvariant certificate before}
    {dispatch :
      DispatchStep certificate before invariant ⟨.unifyPayload, after⟩}
    (prior : CanonicalTagHistory certificate history)
    (step : UnifyPayloadStep certificate before after)
    (priorSpine : prior.CommitmentSpine) :
    (CanonicalTagHistory.later
      (invariant := invariant) (dispatch := dispatch)
      prior (.unifyPayload step)).CommitmentSpine := by
  intro position parent child first second
  have firstBound : position < after.stack.sigma.length :=
    (List.getElem?_eq_some_iff.mp first).choose
  have secondBound : position + 1 < after.stack.sigma.length :=
    (List.getElem?_eq_some_iff.mp second).choose
  have beforeSigma := unify_before_sigma_eq_after_append_active step
  have oldFirst : before.stack.sigma[position]? = some parent := by
    rw [beforeSigma, List.getElem?_append_left firstBound]
    exact first
  have oldSecond :
      before.stack.sigma[position + 1]? = some child := by
    rw [beforeSigma, List.getElem?_append_left secondBound]
    exact second
  rcases priorSpine position parent child oldFirst oldSecond with
    ⟨event, lookup, commits⟩
  exact ⟨event, by
    simpa [reservationLedger,
      DispatchTagEvidence.reservationEvents] using lookup, commits⟩

/-- One exact canonical dispatcher event preserves the commitment spine.
The existing branch evidence supplies every typed transition witness needed
for the stable, append, and pop cases. -/
private theorem later_commitmentSpine
    {certificate : Certificate} {before : ReservationState}
    {result : Figure7DispatchResult}
    {history : ExecutedHistory certificate before}
    {invariant : SchedulerInvariant certificate before}
    {dispatch : DispatchStep certificate before invariant result}
    (prior : CanonicalTagHistory certificate history)
    (evidence : DispatchTagEvidence certificate before result)
    (priorSpine : prior.CommitmentSpine) :
    (CanonicalTagHistory.later
      (invariant := invariant) (dispatch := dispatch)
      prior evidence).CommitmentSpine := by
  cases evidence with
  | concl step =>
      exact later_concl_commitmentSpine prior step priorSpine
  | nop step =>
      exact later_nop_commitmentSpine prior step priorSpine
  | new step =>
      exact later_new_commitmentSpine prior step priorSpine
  | wait step =>
      exact later_wait_commitmentSpine prior step priorSpine
  | forward step =>
      exact later_forward_commitmentSpine prior step priorSpine
  | unifyPayload step =>
      exact later_unifyPayload_commitmentSpine prior step priorSpine

/-- Every canonical dispatcher tag history carries the exact commitment
spine for its final retained `sigma` stack. -/
theorem commitmentSpine
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history) :
    tagHistory.CommitmentSpine := by
  induction tagHistory with
  | empty =>
      exact empty_commitmentSpine
  | init step =>
      exact init_commitmentSpine step
  | later prior evidence induction =>
      exact later_commitmentSpine prior evidence induction

end CanonicalTagHistory

end SequentialFigure7
end ProofNetIR
