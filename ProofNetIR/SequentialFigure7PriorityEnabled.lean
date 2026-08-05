import ProofNetIR.SequentialFigure7Dispatcher
import ProofNetIR.SequentialFigure7StableEnabled
import ProofNetIR.SequentialFigure7UnifyPayloadEnabled
import ProofNetIR.SequentialFigure7NewEnabledCore

namespace ProofNetIR

/-!
# Priority-aware applicability for the canonical Figure-7 dispatcher

This module connects all six input-only applicability predicates to their
executors, then records the canonical dispatcher's fixed precedence.  Reverse
applicability is reconstructed from typed successful steps; no positive or
negative priority field stores an executor equation or post-state.

The `new` branch now stores `NewEnabled`, whose exact correspondence with
executor success requires the supplied `SchedulerInvariant`. Consequently
`PriorityEnabled` remains an exact classification of the existing dispatcher,
not a proof that every invariant state has a branch. No progress, reachability,
completeness, termination, scheduling, or complexity theorem is claimed here.
-/

namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge

namespace PreparedStep

/-- Recover the shared input-only ready-head data from a typed common-prefix
success.  Only queries of the original state are retained. -/
def readyHeadInput {before : ReservationState}
    (prepared : PreparedStep before) : ReadyHeadInput before where
  vertex := prepared.stackResult.vertex
  readyTail := prepared.stackResult.remainingTop
  rawAge := prepared.stackResult.rawAge
  top_ready :=
    (SequentialStackState.popReadyMark?_exact prepared.stack_eq).1
  sigma_top :=
    (SequentialStackState.popReadyMark?_exact prepared.stack_eq).2.1

end PreparedStep

private def submittedParInput
    {certificate : Certificate} {vertex : Vertex}
    (consumer : ConnectiveBelow certificate vertex)
    (parEquation : consumer.kind = .par) :
    SubmittedParInput certificate vertex where
  linkIndex := consumer.linkIndex
  storedLeft := consumer.storedLeft
  storedRight := consumer.storedRight
  conclusion := consumer.conclusion
  side := consumer.side
  link_eq := by
    simpa [parEquation, SequentialConnectiveKind.asLink] using
      consumer.link_eq
  premise_eq := consumer.premise_eq

namespace ConclStep

/-- A typed executable `concl` success reconstructs the pure input-only
applicability witness. -/
theorem enabled
    {certificate : Certificate} {before after : ReservationState}
    (step : ConclStep certificate before after) :
    ConclEnabled certificate before := by
  refine ⟨{
    head := step.prepared.readyHeadInput
    boundary := ?_ }⟩
  simpa [PreparedStep.readyHeadInput] using step.boundary.boundary

end ConclStep

namespace NopStep

/-- A typed executable `nop` success reconstructs the pure input-only
applicability witness. -/
theorem enabled
    {certificate : Certificate} {before after : ReservationState}
    (step : NopStep certificate before after) :
    NopEnabled certificate before := by
  let par := submittedParInput step.consumer step.par_eq
  refine ⟨{
    head := step.prepared.readyHeadInput
    par := ?_
    mate_unmarked := ?_ }⟩
  · simpa [PreparedStep.readyHeadInput] using par
  simpa [par, submittedParInput, SubmittedParInput.mate,
    ConnectiveBelow.mate, PreparedStep.readyHeadInput] using
      step.mate_unmarked_before

end NopStep

namespace WaitStep

/-- A typed executable `wait` success reconstructs the pure input-only
applicability witness. -/
theorem enabled
    {certificate : Certificate} {before after : ReservationState}
    (step : WaitStep certificate before after) :
    WaitEnabled certificate before := by
  let par := submittedParInput step.consumer step.par_eq
  refine ⟨{
    head := step.prepared.readyHeadInput
    par := ?_
    mateRawAge := step.mateRawAge
    mate_marked := ?_
    younger := ?_ }⟩
  · simpa [PreparedStep.readyHeadInput] using par
  simpa [par, submittedParInput, SubmittedParInput.mate,
    ConnectiveBelow.mate, PreparedStep.readyHeadInput] using
      step.mate_marked_before
  · simpa [PreparedStep.readyHeadInput] using step.younger

end WaitStep

namespace ForwardStep

/-- A typed executable `forward` success reconstructs the pure input-only
applicability witness. -/
theorem enabled
    {certificate : Certificate} {before after : ReservationState}
    (step : ForwardStep certificate before after) :
    ForwardEnabled certificate before := by
  let par := submittedParInput step.consumer step.par_eq
  refine ⟨{
    head := step.prepared.readyHeadInput
    par := ?_
    mateRawAge := step.mateRawAge
    mate_marked := ?_
    not_older := ?_ }⟩
  · simpa [PreparedStep.readyHeadInput] using par
  simpa [par, submittedParInput, SubmittedParInput.mate,
    ConnectiveBelow.mate, PreparedStep.readyHeadInput] using
      step.mate_marked_before
  · simpa [PreparedStep.readyHeadInput] using step.not_older

end ForwardStep

namespace UnifyPayloadStep

/-- A typed executable arbitrary-payload unification reconstructs its pure
input-only applicability witness. -/
theorem enabled
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after) :
    UnifyPayloadEnabled certificate before := by
  rcases SequentialStackState.popReadyMark?_exact step.prepared.stack_eq with
    ⟨topReady, sigmaTop, _, _, _, sigmaAfter, _, _, _⟩
  have mergeTop :
      step.prepared.stackResult.after.sigma.getLast? =
        some step.mergeStep.activeBoundary := by
    rw [step.mergeStep.sigma_eq]
    simp
  have preparedTop :
      step.prepared.stackResult.after.sigma.getLast? =
        some step.prepared.stackResult.rawAge := by
    rw [sigmaAfter]
    exact sigmaTop
  have activeEquation :
      step.mergeStep.activeBoundary =
        step.prepared.stackResult.rawAge :=
    Option.some.inj (mergeTop.symm.trans preparedTop)
  refine ⟨{
    vertex := step.prepared.stackResult.vertex
    readyTail := step.prepared.stackResult.remainingTop
    consumer := step.consumer
    mateRawAge := step.mateRawAge
    sigmaPrefix := step.mergeStep.sigmaPrefix
    previousBoundary := step.previousBoundary
    activeBoundary := step.prepared.stackResult.rawAge
    top_ready := topReady
    sigma_two_levels := ?_
    consumer_valid := Certificate.tensorBelow?_eq_some_iff.mp step.consumer_eq
    mate_marked := step.mate_marked_before
    lower := step.lower
    upper := step.upper }⟩
  calc
    before.stack.sigma = step.prepared.stackResult.after.sigma :=
      sigmaAfter.symm
    _ = step.mergeStep.sigmaPrefix ++
          [step.previousBoundary, step.mergeStep.activeBoundary] :=
      step.mergeStep.sigma_eq
    _ = step.mergeStep.sigmaPrefix ++
          [step.previousBoundary, step.prepared.stackResult.rawAge] := by
      rw [activeEquation]

end UnifyPayloadStep

/-- Existential `concl` executor success is exactly input-only
`ConclEnabled`, under the complete scheduler invariant. -/
theorem concl?_success_iff_enabled
    {certificate : Certificate} {before : ReservationState}
    (invariant : SchedulerInvariant certificate before) :
    (∃ after,
      concl? certificate before invariant.toReservationInvariant =
        some after) ↔
      ConclEnabled certificate before := by
  constructor
  · rintro ⟨after, equation⟩
    rcases
        (concl?_some_iff invariant.toReservationInvariant).mp equation with
      ⟨step⟩
    exact step.enabled
  · exact concl?_exists_of_enabled invariant

/-- Existential `nop` executor success is exactly input-only `NopEnabled`,
under the complete scheduler invariant. -/
theorem nop?_success_iff_enabled
    {certificate : Certificate} {before : ReservationState}
    (invariant : SchedulerInvariant certificate before) :
    (∃ after,
      nop? certificate before invariant.toReservationInvariant =
        some after) ↔
      NopEnabled certificate before := by
  constructor
  · rintro ⟨after, equation⟩
    rcases
        (nop?_some_iff invariant.toReservationInvariant).mp equation with
      ⟨step⟩
    exact step.enabled
  · exact nop?_exists_of_enabled invariant

/-- Existential `wait` executor success is exactly input-only `WaitEnabled`,
under the complete scheduler invariant. -/
theorem wait?_success_iff_enabled
    {certificate : Certificate} {before : ReservationState}
    (invariant : SchedulerInvariant certificate before) :
    (∃ after,
      wait? certificate before invariant.toReservationInvariant =
        some after) ↔
      WaitEnabled certificate before := by
  constructor
  · rintro ⟨after, equation⟩
    rcases
        (wait?_some_iff invariant.toReservationInvariant).mp equation with
      ⟨step⟩
    exact step.enabled
  · exact wait?_exists_of_enabled invariant

/-- Existential `forward` executor success is exactly input-only
`ForwardEnabled`, under the complete scheduler invariant. -/
theorem forward?_success_iff_enabled
    {certificate : Certificate} {before : ReservationState}
    (invariant : SchedulerInvariant certificate before) :
    (∃ after,
      forward? certificate before invariant.toReservationInvariant =
        some after) ↔
      ForwardEnabled certificate before := by
  constructor
  · rintro ⟨after, equation⟩
    rcases
        (forward?_some_iff invariant.toReservationInvariant).mp equation with
      ⟨step⟩
    exact step.enabled
  · exact forward?_exists_of_enabled invariant

/-- Existential arbitrary-payload unification executor success is exactly
input-only `UnifyPayloadEnabled`, under the complete scheduler invariant. -/
theorem unifyPayload?_success_iff_enabled
    {certificate : Certificate} {before : ReservationState}
    (invariant : SchedulerInvariant certificate before) :
    (∃ after,
      unifyPayload? certificate before invariant.toReservationInvariant =
        some after) ↔
      UnifyPayloadEnabled certificate before := by
  constructor
  · rintro ⟨after, equation⟩
    rcases
        (unifyPayload?_some_iff invariant.toReservationInvariant).mp
            equation with
      ⟨step⟩
    exact step.enabled
  · exact unifyPayload?_exists_of_enabled invariant

private theorem executor_none_of_not_success
    {executor : Option α}
    (failure : ¬ ∃ output, executor = some output) : executor = none := by
  cases equation : executor with
  | none => rfl
  | some output => exact False.elim (failure ⟨output, equation⟩)

/-- Exact fixed-precedence applicability classification for the canonical
dispatcher.  Later constructors retain negations of every earlier branch.

Every positive field and every stored earlier-branch negation is input-only. -/
inductive PriorityEnabled (certificate : Certificate)
    (before : ReservationState)
    (invariant : SchedulerInvariant certificate before) :
    Figure7RuleKind → Prop where
  | concl (enabled : ConclEnabled certificate before) :
      PriorityEnabled certificate before invariant .concl
  | nop
      (concl_disabled : ¬ ConclEnabled certificate before)
      (enabled : NopEnabled certificate before) :
      PriorityEnabled certificate before invariant .nop
  | new
      (concl_disabled : ¬ ConclEnabled certificate before)
      (nop_disabled : ¬ NopEnabled certificate before)
      (enabled : NewEnabled certificate before) :
      PriorityEnabled certificate before invariant .new
  | wait
      (concl_disabled : ¬ ConclEnabled certificate before)
      (nop_disabled : ¬ NopEnabled certificate before)
      (new_disabled : ¬ NewEnabled certificate before)
      (enabled : WaitEnabled certificate before) :
      PriorityEnabled certificate before invariant .wait
  | forward
      (concl_disabled : ¬ ConclEnabled certificate before)
      (nop_disabled : ¬ NopEnabled certificate before)
      (new_disabled : ¬ NewEnabled certificate before)
      (wait_disabled : ¬ WaitEnabled certificate before)
      (enabled : ForwardEnabled certificate before) :
      PriorityEnabled certificate before invariant .forward
  | unifyPayload
      (concl_disabled : ¬ ConclEnabled certificate before)
      (nop_disabled : ¬ NopEnabled certificate before)
      (new_disabled : ¬ NewEnabled certificate before)
      (wait_disabled : ¬ WaitEnabled certificate before)
      (forward_disabled : ¬ ForwardEnabled certificate before)
      (enabled : UnifyPayloadEnabled certificate before) :
      PriorityEnabled certificate before invariant .unifyPayload

/-- A priority-selected `new` branch exposes its complete input-only
applicability witness directly. -/
theorem PriorityEnabled.newEnabled
    {certificate : Certificate} {before : ReservationState}
    {invariant : SchedulerInvariant certificate before}
    (enabled : PriorityEnabled certificate before invariant .new) :
    NewEnabled certificate before := by
  cases enabled with
  | new _ _ input => exact input

/-- Compatibility constructor for callers that still hold the historical
operational enabledness proposition. -/
theorem PriorityEnabled.new_of_executable
    {certificate : Certificate} {before : ReservationState}
    {invariant : SchedulerInvariant certificate before}
    (concl_disabled : ¬ ConclEnabled certificate before)
    (nop_disabled : ¬ NopEnabled certificate before)
    (enabled : NewExecutableEnabled certificate before invariant) :
    PriorityEnabled certificate before invariant .new :=
  PriorityEnabled.new concl_disabled nop_disabled
    (NewExecutableEnabled.iff_newEnabled.mp enabled)

/-- An exact dispatcher-selected branch satisfies its corresponding
fixed-precedence applicability proposition. -/
theorem DispatchStep.priorityEnabled
    {certificate : Certificate} {before : ReservationState}
    {invariant : SchedulerInvariant certificate before}
    {result : Figure7DispatchResult}
    (step : DispatchStep certificate before invariant result) :
    PriorityEnabled certificate before invariant result.kind := by
  cases step with
  | concl equation =>
      exact PriorityEnabled.concl
        ((concl?_success_iff_enabled invariant).mp ⟨_, equation⟩)
  | nop conclNone equation =>
      apply PriorityEnabled.nop
      · intro enabled
        rcases concl?_exists_of_enabled invariant enabled with
          ⟨after, success⟩
        rw [conclNone] at success
        simp at success
      · exact (nop?_success_iff_enabled invariant).mp ⟨_, equation⟩
  | new conclNone nopNone equation =>
      apply PriorityEnabled.new
      · intro enabled
        rcases concl?_exists_of_enabled invariant enabled with
          ⟨after, success⟩
        rw [conclNone] at success
        simp at success
      · intro enabled
        rcases nop?_exists_of_enabled invariant enabled with
          ⟨after, success⟩
        rw [nopNone] at success
        simp at success
      · exact (new?_success_iff_enabled invariant).mp ⟨_, equation⟩
  | wait conclNone nopNone newNone equation =>
      apply PriorityEnabled.wait
      · intro enabled
        rcases concl?_exists_of_enabled invariant enabled with
          ⟨after, success⟩
        rw [conclNone] at success
        simp at success
      · intro enabled
        rcases nop?_exists_of_enabled invariant enabled with
          ⟨after, success⟩
        rw [nopNone] at success
        simp at success
      · intro enabled
        rcases new?_exists_of_enabled invariant enabled with
          ⟨after, success⟩
        rw [newNone] at success
        simp at success
      · exact (wait?_success_iff_enabled invariant).mp ⟨_, equation⟩
  | forward conclNone nopNone newNone waitNone equation =>
      apply PriorityEnabled.forward
      · intro enabled
        rcases concl?_exists_of_enabled invariant enabled with
          ⟨after, success⟩
        rw [conclNone] at success
        simp at success
      · intro enabled
        rcases nop?_exists_of_enabled invariant enabled with
          ⟨after, success⟩
        rw [nopNone] at success
        simp at success
      · intro enabled
        rcases new?_exists_of_enabled invariant enabled with
          ⟨after, success⟩
        rw [newNone] at success
        simp at success
      · intro enabled
        rcases wait?_exists_of_enabled invariant enabled with
          ⟨after, success⟩
        rw [waitNone] at success
        simp at success
      · exact
          (forward?_success_iff_enabled invariant).mp ⟨_, equation⟩
  | unifyPayload conclNone nopNone newNone waitNone forwardNone equation =>
      apply PriorityEnabled.unifyPayload
      · intro enabled
        rcases concl?_exists_of_enabled invariant enabled with
          ⟨after, success⟩
        rw [conclNone] at success
        simp at success
      · intro enabled
        rcases nop?_exists_of_enabled invariant enabled with
          ⟨after, success⟩
        rw [nopNone] at success
        simp at success
      · intro enabled
        rcases new?_exists_of_enabled invariant enabled with
          ⟨after, success⟩
        rw [newNone] at success
        simp at success
      · intro enabled
        rcases wait?_exists_of_enabled invariant enabled with
          ⟨after, success⟩
        rw [waitNone] at success
        simp at success
      · intro enabled
        rcases forward?_exists_of_enabled invariant enabled with
          ⟨after, success⟩
        rw [forwardNone] at success
        simp at success
      · exact
          (unifyPayload?_success_iff_enabled invariant).mp ⟨_, equation⟩

/-- Fixed-precedence applicability produces one exact typed dispatcher branch
of the indexed rule kind. -/
theorem PriorityEnabled.exists_dispatchStep
    {certificate : Certificate} {before : ReservationState}
    {invariant : SchedulerInvariant certificate before}
    {kind : Figure7RuleKind}
    (enabled : PriorityEnabled certificate before invariant kind) :
    ∃ after,
      Nonempty
        (DispatchStep certificate before invariant ⟨kind, after⟩) := by
  cases enabled with
  | concl enabled =>
      rcases concl?_exists_of_enabled invariant enabled with
        ⟨after, equation⟩
      exact ⟨after, ⟨DispatchStep.concl equation⟩⟩
  | nop conclDisabled enabled =>
      have conclNone := executor_none_of_not_success
        (fun success => conclDisabled
          ((concl?_success_iff_enabled invariant).mp success))
      rcases nop?_exists_of_enabled invariant enabled with
        ⟨after, equation⟩
      exact ⟨after, ⟨DispatchStep.nop conclNone equation⟩⟩
  | new conclDisabled nopDisabled enabled =>
      have conclNone := executor_none_of_not_success
        (fun success => conclDisabled
          ((concl?_success_iff_enabled invariant).mp success))
      have nopNone := executor_none_of_not_success
        (fun success => nopDisabled
          ((nop?_success_iff_enabled invariant).mp success))
      rcases new?_exists_of_enabled invariant enabled with
        ⟨after, equation⟩
      exact ⟨after, ⟨DispatchStep.new conclNone nopNone equation⟩⟩
  | wait conclDisabled nopDisabled newDisabled enabled =>
      have conclNone := executor_none_of_not_success
        (fun success => conclDisabled
          ((concl?_success_iff_enabled invariant).mp success))
      have nopNone := executor_none_of_not_success
        (fun success => nopDisabled
          ((nop?_success_iff_enabled invariant).mp success))
      have newNone := executor_none_of_not_success
        (fun success => newDisabled
          ((new?_success_iff_enabled invariant).mp success))
      rcases wait?_exists_of_enabled invariant enabled with
        ⟨after, equation⟩
      exact ⟨after,
        ⟨DispatchStep.wait conclNone nopNone newNone equation⟩⟩
  | forward conclDisabled nopDisabled newDisabled waitDisabled enabled =>
      have conclNone := executor_none_of_not_success
        (fun success => conclDisabled
          ((concl?_success_iff_enabled invariant).mp success))
      have nopNone := executor_none_of_not_success
        (fun success => nopDisabled
          ((nop?_success_iff_enabled invariant).mp success))
      have newNone := executor_none_of_not_success
        (fun success => newDisabled
          ((new?_success_iff_enabled invariant).mp success))
      have waitNone := executor_none_of_not_success
        (fun success => waitDisabled
          ((wait?_success_iff_enabled invariant).mp success))
      rcases forward?_exists_of_enabled invariant enabled with
        ⟨after, equation⟩
      exact ⟨after,
        ⟨DispatchStep.forward conclNone nopNone newNone waitNone equation⟩⟩
  | unifyPayload conclDisabled nopDisabled newDisabled waitDisabled
      forwardDisabled enabled =>
      have conclNone := executor_none_of_not_success
        (fun success => conclDisabled
          ((concl?_success_iff_enabled invariant).mp success))
      have nopNone := executor_none_of_not_success
        (fun success => nopDisabled
          ((nop?_success_iff_enabled invariant).mp success))
      have newNone := executor_none_of_not_success
        (fun success => newDisabled
          ((new?_success_iff_enabled invariant).mp success))
      have waitNone := executor_none_of_not_success
        (fun success => waitDisabled
          ((wait?_success_iff_enabled invariant).mp success))
      have forwardNone := executor_none_of_not_success
        (fun success => forwardDisabled
          ((forward?_success_iff_enabled invariant).mp success))
      rcases unifyPayload?_exists_of_enabled invariant enabled with
        ⟨after, equation⟩
      exact ⟨after, ⟨DispatchStep.unifyPayload conclNone nopNone newNone
        waitNone forwardNone equation⟩⟩

/-- The canonical dispatcher selects an exact rule kind iff that kind's
fixed-precedence applicability proposition holds. -/
theorem dispatch?_kind_success_iff_priorityEnabled
    {certificate : Certificate} {before : ReservationState}
    (invariant : SchedulerInvariant certificate before)
    (kind : Figure7RuleKind) :
    (∃ after, dispatch? certificate before invariant = some ⟨kind, after⟩) ↔
      PriorityEnabled certificate before invariant kind := by
  constructor
  · rintro ⟨after, equation⟩
    rcases (dispatch?_some_iff invariant).mp equation with ⟨step⟩
    exact step.priorityEnabled
  · intro enabled
    rcases enabled.exists_dispatchStep with ⟨after, step⟩
    exact ⟨after, (dispatch?_some_iff invariant).mpr step⟩

/-- Dispatcher failure is exactly the absence of every fixed-precedence
branch.  This classifies the existing dispatcher only; it is not progress. -/
theorem dispatch?_eq_none_iff_forall_not_priorityEnabled
    {certificate : Certificate} {before : ReservationState}
    (invariant : SchedulerInvariant certificate before) :
    dispatch? certificate before invariant = none ↔
      ∀ kind, ¬ PriorityEnabled certificate before invariant kind := by
  constructor
  · intro dispatchNone kind enabled
    rcases
        (dispatch?_kind_success_iff_priorityEnabled invariant kind).mpr
          enabled with
      ⟨after, equation⟩
    rw [dispatchNone] at equation
    simp at equation
  · intro disabled
    apply executor_none_of_not_success
    rintro ⟨result, equation⟩
    exact disabled result.kind
      ((dispatch?_kind_success_iff_priorityEnabled invariant result.kind).mp
        ⟨result.after, by simpa using equation⟩)

/-- At most one rule kind satisfies the fixed-precedence applicability
classification for a fixed input and invariant witness. -/
theorem PriorityEnabled.kind_unique
    {certificate : Certificate} {before : ReservationState}
    {invariant : SchedulerInvariant certificate before}
    {first second : Figure7RuleKind}
    (left : PriorityEnabled certificate before invariant first)
    (right : PriorityEnabled certificate before invariant second) :
    first = second := by
  rcases left.exists_dispatchStep with ⟨leftAfter, ⟨leftStep⟩⟩
  rcases right.exists_dispatchStep with ⟨rightAfter, ⟨rightStep⟩⟩
  exact congrArg Figure7DispatchResult.kind
    (DispatchStep.output_unique leftStep rightStep)

end SequentialFigure7

end ProofNetIR
