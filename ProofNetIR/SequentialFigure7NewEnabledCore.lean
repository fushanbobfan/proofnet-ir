import ProofNetIR.SequentialFigure7NewInputCore

namespace ProofNetIR

/-!
# Core input-only applicability for Figure-7 `new`

`NewEnabledInput` records exactly the read-only data needed by the current
deterministic `new?` implementation: a shallow tensor/ready-head guard, one
proof-relevant production `FreshSourceLeftRun`, and the operational enqueue
guard at the selected head's existing raw age.  It stores no executor result,
success equation, output state, transition history, or reachability witness.

Under the complete state-only `SchedulerInvariant`, this local input predicate
is equivalent to existential `new?` success.  The theorem is only a local rule
correspondence.  It does not say that every reachable nonterminal state enables
`new`, prove later-call totality, dispatcher progress, pure-worklist
completeness, fallback removal, or whole-program linearity.

The historical operational proposition `NewExecutableEnabled` remains here as
a compatibility API.  It is no longer stored by `PriorityEnabled`.
-/

namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge

/-- Complete input-only data for the currently implemented Figure-7 `new`
rule.  The enqueue age is fixed to `guard.head.rawAge`; there is no redundant
existential active-age witness. -/
structure NewEnabledInput (certificate : Certificate)
    (before : ReservationState) : Type where
  guard : NewGuard certificate before
  trace : List Vertex
  reached : Vertex
  partner : Vertex
  linkIndex : Nat
  run :
    SequentialUnification.FreshSourceLeftRun certificate
      guard.head.markedCore certificate.formulas.size before.tags
      guard.tensor.mate trace reached partner linkIndex
  enqueueReady :
    OperationalNewReadyAt guard.head.markedStack guard.head.rawAge
      reached partner

/-- Input-only applicability predicate for the current local Figure-7 `new`
executor. -/
def NewEnabled (certificate : Certificate)
    (before : ReservationState) : Prop :=
  Nonempty (NewEnabledInput certificate before)

/-- Historical operational compatibility proposition for Figure-7 `new`.

The priority classifier no longer stores this existential executor-success
view; it remains public so downstream callers can migrate through the exact
`iff_newEnabled` theorem below. -/
def NewExecutableEnabled (certificate : Certificate)
    (before : ReservationState)
    (invariant : SchedulerInvariant certificate before) : Prop :=
  ∃ after,
    new? certificate before invariant.toReservationInvariant = some after

namespace NewEnabledInput

/-- The complete input-only witness directly contains the older one-way
necessary predicate. -/
def inputNecessary
    {certificate : Certificate} {before : ReservationState}
    (input : NewEnabledInput certificate before) :
    NewInput certificate before where
  guard := input.guard
  route := input.run.toFreshSourceLeftRoute (Nat.le_refl _)

end NewEnabledInput

/-- Proposition-level input-only enabledness implies the older necessary
predicate without choosing any executor output. -/
theorem NewEnabled.inputNecessary
    {certificate : Certificate} {before : ReservationState}
    (enabled : NewEnabled certificate before) :
    NewInputNecessary certificate before := by
  rcases enabled with ⟨input⟩
  exact ⟨input.inputNecessary⟩

/-- A satisfied operational enqueue guard produces one exact stack output. -/
theorem operationalNewEnqueue?_exists_of_ready
    {state : SequentialStackState} {active : RawTokenAge}
    {reached partner : Vertex}
    (ready : OperationalNewReadyAt state active reached partner) :
    ∃ after,
      state.operationalNewEnqueue? reached partner = some after := by
  unfold SequentialStackState.operationalNewEnqueue?
  rw [ready.2.1]
  simp [ready]

/-- A typed executable `new` success reconstructs the exact proof-relevant
input-only enabled witness. -/
theorem NewStep.newEnabled
    {certificate : Certificate} {before after : ReservationState}
    (step : NewStep certificate before after) :
    NewEnabled certificate before := by
  have execution :
      SequentialUnification.FreshSourceLeftRun.FreshSourceLeftExecution
        certificate step.coreMarked certificate.formulas.size before.tags
        step.tensor.mate step.search.trace step.reached step.partner
        step.search.linkIndex :=
    ⟨step.search, by
      simpa [SequentialUnification.nextAxiom?] using step.search_eq,
      rfl, rfl, step.oriented_eq⟩
  rcases
      (SequentialUnification.FreshSourceLeftRun.execution_iff_nonempty).mp
        execution with
    ⟨run⟩
  rcases operationalNewEnqueue?_some_iff.mp step.stack_enqueue_eq with
    ⟨enqueue⟩
  let guard := step.guard
  have stackEquation :
      step.stackResult.after = guard.head.markedStack := by
    change step.stackResult.after = step.readyHeadInput.markedStack
    exact step.stackAfter_eq_readyHeadInput
  have runInput :
      SequentialUnification.FreshSourceLeftRun certificate
        guard.head.markedCore certificate.formulas.size before.tags
        guard.tensor.mate step.search.trace step.reached step.partner
        step.search.linkIndex := by
    change
      SequentialUnification.FreshSourceLeftRun certificate
        step.readyHeadInput.markedCore certificate.formulas.size before.tags
        step.tensor.mate step.search.trace step.reached step.partner
        step.search.linkIndex
    rw [← step.coreMarked_eq_readyHeadInput]
    exact run
  have stackReady :
      OperationalNewReadyAt guard.head.markedStack enqueue.active
        step.reached step.partner := by
    simpa [stackEquation] using enqueue.ready
  have selectedTop :
      guard.head.markedStack.sigma.getLast? =
        some guard.head.rawAge := by
    change step.readyHeadInput.markedStack.sigma.getLast? =
      some step.readyHeadInput.rawAge
    simpa [ReadyHeadInput.markedStack] using step.readyHeadInput.sigma_top
  have activeEquation : enqueue.active = guard.head.rawAge :=
    Option.some.inj (stackReady.2.1.symm.trans selectedTop)
  have enqueueInput :
      OperationalNewReadyAt guard.head.markedStack guard.head.rawAge
        step.reached step.partner := by
    simpa [activeEquation] using stackReady
  exact ⟨{
    guard := guard
    trace := step.search.trace
    reached := step.reached
    partner := step.partner
    linkIndex := step.search.linkIndex
    run := runInput
    enqueueReady := enqueueInput }⟩

/-- Executable success implies input-only local enabledness. -/
theorem new?_success_implies_enabled
    {certificate : Certificate} {before after : ReservationState}
    (invariant : SchedulerInvariant certificate before)
    (equation :
      new? certificate before invariant.toReservationInvariant =
        some after) :
    NewEnabled certificate before := by
  rcases
      (new?_some_iff invariant.toReservationInvariant).mp equation with
    ⟨step⟩
  exact step.newEnabled

/-- Complete input-only local enabledness supplies an exact executable output
under the full state-only scheduler invariant. -/
theorem new?_exists_of_enabled
    {certificate : Certificate} {before : ReservationState}
    (invariant : SchedulerInvariant certificate before)
    (enabled : NewEnabled certificate before) :
    ∃ after,
      new? certificate before invariant.toReservationInvariant =
        some after := by
  rcases enabled with ⟨input⟩
  rcases input.run.execution with
    ⟨search, searchEquation, traceEquation, linkEquation,
      orientedEquation⟩
  have searchEquation' :
      SequentialUnification.nextAxiom? certificate
          input.guard.head.markedCore
          (SequentialUnification.sourceIndex certificate)
          (SequentialUnification.sourceIndex_sound certificate)
          before.tags input.guard.tensor.mate = some search := by
    simpa [SequentialUnification.nextAxiom?] using searchEquation
  rcases operationalNewEnqueue?_exists_of_ready input.enqueueReady with
    ⟨stackAfter, stackEquation⟩
  have carriersAligned :
      input.guard.head.markedCore.components.size =
        input.guard.head.markedCore.parents.size :=
    input.guard.head.markedCore_carriers_aligned invariant
  rcases input.run.terminalAxiom.exists_reserveAxiomAt
      invariant.structural carriersAligned with
    ⟨coreAfter, coreEquation⟩
  have coreEquation' :
      certificate.reserveAxiomAt? input.guard.head.markedCore
          search.linkIndex = some coreAfter := by
    simpa [linkEquation] using coreEquation
  let output : ReservationState := {
    stack := stackAfter
    core := coreAfter
    tags := search.tags }
  refine ⟨output,
    (new?_some_iff invariant.toReservationInvariant).mpr ?_⟩
  exact ⟨{
    before_invariant := invariant.toReservationInvariant
    stackResult := input.guard.head.stackResult
    coreMarked := input.guard.head.markedCore
    tensor := input.guard.tensor
    search := search
    reached := input.reached
    partner := input.partner
    stackAfter := stackAfter
    coreAfter := coreAfter
    stack_eq := input.guard.head.stack_pop_eq invariant
    core_mark_eq := input.guard.head.core_mark_eq invariant
    tensor_eq := input.guard.tensor_eq
    search_eq := searchEquation'
    oriented_eq := orientedEquation
    stack_enqueue_eq := stackEquation
    core_reserve_eq := coreEquation'
    output_eq := rfl }⟩

/-- Under the complete state-only scheduler invariant, the input-only
predicate is exactly existential success of the current `new?` executor. -/
theorem new?_success_iff_enabled
    {certificate : Certificate} {before : ReservationState}
    (invariant : SchedulerInvariant certificate before) :
    (∃ after,
      new? certificate before invariant.toReservationInvariant =
        some after) ↔
      NewEnabled certificate before := by
  constructor
  · rintro ⟨after, equation⟩
    exact new?_success_implies_enabled invariant equation
  · exact new?_exists_of_enabled invariant

/-- Compatibility: the older operational enabledness proposition is exactly
the input-only predicate.  The priority classifier itself stores the latter. -/
theorem NewExecutableEnabled.iff_newEnabled
    {certificate : Certificate} {before : ReservationState}
    {invariant : SchedulerInvariant certificate before} :
    NewExecutableEnabled certificate before invariant ↔
      NewEnabled certificate before :=
  new?_success_iff_enabled invariant

/-- The historical operational compatibility proposition implies the weaker
input-only necessary projection. -/
theorem NewExecutableEnabled.inputNecessary
    {certificate : Certificate} {before : ReservationState}
    {invariant : SchedulerInvariant certificate before}
    (enabled : NewExecutableEnabled certificate before invariant) :
    NewInputNecessary certificate before :=
  NewEnabled.inputNecessary
    (NewExecutableEnabled.iff_newEnabled.mp enabled)

/-- Every input-only enabled state has an invariant-preserving executable
output. -/
theorem new?_exists_schedulerInvariant_of_enabled
    {certificate : Certificate} {before : ReservationState}
    (invariant : SchedulerInvariant certificate before)
    (enabled : NewEnabled certificate before) :
    ∃ after,
      new? certificate before invariant.toReservationInvariant = some after ∧
        SchedulerInvariant certificate after := by
  rcases new?_exists_of_enabled invariant enabled with
    ⟨after, equation⟩
  exact ⟨after, equation, new?_schedulerInvariant invariant equation⟩

end SequentialFigure7

end ProofNetIR
