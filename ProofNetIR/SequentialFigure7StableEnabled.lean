import ProofNetIR.SequentialSchedulerInvariant

namespace ProofNetIR

/-!
# Input-only applicability for the stable Figure-7 rules

This module gives `concl`, `nop`, `wait`, and `forward` shared, read-only
applicability witnesses.  An enabled witness stores no post-state, rule result,
or equation asserting that a rule executor succeeds.  The complete scheduler
invariant supplies the synchronized pop/raw-mark preconditions and the
representation-only freshness required by `forward`.

The theorems are conditional applicability results.  They do not assert that
one of these predicates holds in every invariant state, establish dispatcher
priority, or prove reachability, progress, completeness, or complexity.
-/

namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge

/-- Shared read-only selection of the active ready occurrence and raw age.

The witness fixes only queries of the input scheduler state.  In particular,
it contains no prepared state, post-state, executor result, or executor success
equation. -/
structure ReadyHeadInput (before : ReservationState) : Type where
  vertex : Vertex
  readyTail : List Vertex
  rawAge : RawTokenAge
  top_ready :
    before.stack.ready.getLast? = some (vertex :: readyTail)
  sigma_top : before.stack.sigma.getLast? = some rawAge

namespace ReadyHeadInput

/-- Production state obtained by the deterministic raw-mark update described
by a ready-head input.  This is a pure expression, not a stored result. -/
def markedCore {before : ReservationState}
    (input : ReadyHeadInput before) : UnificationState := {
  before.core with
  marks := before.core.marks.setIfInBounds input.vertex (some input.rawAge) }

/-- Scheduler stack obtained by the deterministic pop/raw-mark update
described by a ready-head input. -/
def markedStack {before : ReservationState}
    (input : ReadyHeadInput before) : SequentialStackState := {
  before.stack with
  marks := before.stack.marks.setIfInBounds input.vertex (some input.rawAge)
  ready := before.stack.ready.dropLast ++ [input.readyTail] }

/-- Pure synchronized middle state determined by the input state and selected
ready head. -/
def middle {before : ReservationState}
    (input : ReadyHeadInput before) : ReservationState where
  stack := input.markedStack
  core := input.markedCore
  tags := before.tags

private theorem vertex_mem_ready
    {before : ReservationState} (input : ReadyHeadInput before) :
    input.vertex ∈ before.stack.ready.flatten := by
  apply List.mem_flatten.mpr
  exact ⟨input.vertex :: input.readyTail,
    List.mem_of_getLast? input.top_ready, by simp⟩

private theorem vertex_mem_queued
    {before : ReservationState} (input : ReadyHeadInput before) :
    input.vertex ∈ before.stack.queuedVertices := by
  unfold SequentialStackState.queuedVertices
  exact List.mem_append_left _ input.vertex_mem_ready

private theorem core_vertex_unmarked
    {certificate : Certificate} {before : ReservationState}
    (input : ReadyHeadInput before)
    (invariant : SchedulerInvariant certificate before) :
    before.core.marks[input.vertex]? = some none :=
  invariant.queued_vertices_unmarked input.vertex input.vertex_mem_queued

private theorem stack_vertex_unmarked
    {certificate : Certificate} {before : ReservationState}
    (input : ReadyHeadInput before)
    (invariant : SchedulerInvariant certificate before) :
    before.stack.marks[input.vertex]? = some none := by
  rw [← invariant.realizesSigma.marks_eq]
  exact input.core_vertex_unmarked invariant

private def stackResult
    {before : ReservationState} (input : ReadyHeadInput before) :
    PopReadyMarkResult where
  vertex := input.vertex
  rawAge := input.rawAge
  remainingTop := input.readyTail
  after := input.markedStack

private theorem stack_pop_eq
    {certificate : Certificate} {before : ReservationState}
    (input : ReadyHeadInput before)
    (invariant : SchedulerInvariant certificate before) :
    before.stack.popReadyMark? = .ok input.stackResult := by
  simp [SequentialStackState.popReadyMark?, input.top_ready,
    input.sigma_top, input.stack_vertex_unmarked invariant,
    stackResult, markedStack]

private theorem core_mark_eq
    {certificate : Certificate} {before : ReservationState}
    (input : ReadyHeadInput before)
    (invariant : SchedulerInvariant certificate before) :
    before.core.markReadyRaw? input.vertex input.rawAge =
      .ok input.markedCore := by
  unfold UnificationState.markReadyRaw?
  rw [input.core_vertex_unmarked invariant]
  rfl

private def prepared
    {certificate : Certificate} {before : ReservationState}
    (input : ReadyHeadInput before)
    (invariant : SchedulerInvariant certificate before) :
    PreparedStep before where
  stackResult := input.stackResult
  coreMarked := input.markedCore
  stack_eq := input.stack_pop_eq invariant
  core_mark_eq := input.core_mark_eq invariant

private theorem prepare_eq
    {certificate : Certificate} {before : ReservationState}
    (input : ReadyHeadInput before)
    (invariant : SchedulerInvariant certificate before) :
    prepare? before = some (input.prepared invariant) := by
  unfold prepare?
  split
  next stackError stackFailure =>
    rw [input.stack_pop_eq invariant] at stackFailure
    simp at stackFailure
  next actualStack stackSuccess =>
    have actualStackEq : actualStack = input.stackResult :=
      Except.ok.inj (stackSuccess.symm.trans (input.stack_pop_eq invariant))
    subst actualStack
    split
    next coreError coreFailure =>
      change
        before.core.markReadyRaw? input.vertex input.rawAge =
          .error coreError at coreFailure
      rw [input.core_mark_eq invariant] at coreFailure
      simp at coreFailure
    next actualCore coreSuccess =>
      change
        before.core.markReadyRaw? input.vertex input.rawAge =
          .ok actualCore at coreSuccess
      have actualCoreEq : actualCore = input.markedCore :=
        Except.ok.inj (coreSuccess.symm.trans (input.core_mark_eq invariant))
      subst actualCore
      congr 2

/-- The shared input realizes the direct synchronized prefix once the complete
scheduler invariant supplies the two input-mark facts. -/
theorem rulePrefix
    {certificate : Certificate} {before : ReservationState}
    (input : ReadyHeadInput before)
    (invariant : SchedulerInvariant certificate before) :
    RulePrefixAt before input.middle input.vertex input.rawAge := by
  have prefixRule := RulePrefix.ofPrepared (input.prepared invariant)
  simpa [prepared, stackResult, PreparedStep.after, middle, markedStack,
    markedCore] using prefixRule

private theorem middleInvariant
    {certificate : Certificate} {before : ReservationState}
    (input : ReadyHeadInput before)
    (invariant : SchedulerInvariant certificate before) :
    SchedulerInvariant certificate input.middle := by
  simpa [prepared, stackResult, PreparedStep.after, middle, markedStack,
    markedCore] using (input.prepared invariant).schedulerInvariant invariant

private theorem selected_marked
    {certificate : Certificate} {before : ReservationState}
    (input : ReadyHeadInput before)
    (invariant : SchedulerInvariant certificate before) :
    input.markedCore.marks[input.vertex]? = some (some input.rawAge) := by
  exact (UnificationState.markReadyRaw?_exact
    (input.prepared invariant).core_mark_eq).2.2.2.2.2.2

private theorem selected_token
    {certificate : Certificate} {before : ReservationState}
    (input : ReadyHeadInput before)
    (invariant : SchedulerInvariant certificate before) :
    input.markedCore.tokenAt? input.vertex = some input.rawAge := by
  have middleInvariant := input.middleInvariant invariant
  have stackMarked :
      input.middle.stack.marks[input.vertex]? = some (some input.rawAge) := by
    rw [← middleInvariant.realizesSigma.marks_eq]
    exact input.selected_marked invariant
  have ageBound : input.rawAge < input.middle.stack.nextAge :=
    middleInvariant.stack_wellShaped.assigned_age_bound
      input.vertex input.rawAge stackMarked
  have boundaryLookup :
      sigmaBoundary? input.middle.stack.sigma input.rawAge =
        some input.rawAge := by
    apply middleInvariant.stack_wellShaped.sigma_partition
      |>.sigmaBoundary?_eq_top
    simpa [middle, markedStack] using input.sigma_top
  have realized :
      sigmaBoundary? input.middle.stack.sigma input.rawAge =
        some (input.markedCore.representative input.rawAge) :=
    middleInvariant.realizesSigma.representative_eq_boundary ageBound
  have root : input.markedCore.representative input.rawAge = input.rawAge :=
    Option.some.inj (realized.symm.trans boundaryLookup)
  unfold UnificationState.tokenAt?
  rw [input.selected_marked invariant]
  simp [root]

end ReadyHeadInput

/-- Read-only applicability data for the stable `concl` rule. -/
structure ConclInput (certificate : Certificate)
    (before : ReservationState) : Type where
  head : ReadyHeadInput before
  boundary : head.vertex ∈ certificate.conclusions

/-- Input-only applicability predicate for `concl`. -/
def ConclEnabled (certificate : Certificate)
    (before : ReservationState) : Prop :=
  Nonempty (ConclInput certificate before)

namespace ConclInput

private theorem executor_exists
    {certificate : Certificate} {before : ReservationState}
    (input : ConclInput certificate before)
    (invariant : SchedulerInvariant certificate before) :
    ∃ next,
      concl? certificate before invariant.toReservationInvariant = some next := by
  let next := input.head.middle
  have rule : ConclRule certificate before next :=
    ⟨input.head.vertex, input.head.rawAge,
      input.head.rulePrefix invariant, input.boundary⟩
  exact ⟨next, concl?_complete_of_structural invariant.structural
    invariant.toReservationInvariant rule⟩

end ConclInput

/-- Complete scheduler validity turns `ConclEnabled` into executable success. -/
theorem concl?_exists_of_enabled
    {certificate : Certificate} {before : ReservationState}
    (invariant : SchedulerInvariant certificate before)
    (enabled : ConclEnabled certificate before) :
    ∃ next,
      concl? certificate before invariant.toReservationInvariant = some next := by
  rcases enabled with ⟨input⟩
  exact input.executor_exists invariant

/-- `concl` enabledness yields an executor output carrying the complete
scheduler invariant. -/
theorem concl?_exists_schedulerInvariant_of_enabled
    {certificate : Certificate} {before : ReservationState}
    (invariant : SchedulerInvariant certificate before)
    (enabled : ConclEnabled certificate before) :
    ∃ next,
      concl? certificate before invariant.toReservationInvariant = some next ∧
        SchedulerInvariant certificate next := by
  rcases concl?_exists_of_enabled invariant enabled with ⟨next, equation⟩
  exact ⟨next, equation, concl?_schedulerInvariant invariant equation⟩

/-- Exact submitted par slot and stored premise orientation selected by one
ready occurrence.  The witness is entirely about the input certificate. -/
structure SubmittedParInput (certificate : Certificate)
    (vertex : Vertex) : Type where
  linkIndex : Nat
  storedLeft : Vertex
  storedRight : Vertex
  conclusion : Vertex
  side : TensorPremiseSide
  link_eq :
    certificate.links[linkIndex]? =
      some (.par storedLeft storedRight conclusion)
  premise_eq : vertex = side.premise storedLeft storedRight

namespace SubmittedParInput

/-- Opposite submitted premise selected by an exact par input. -/
def mate {certificate : Certificate} {vertex : Vertex}
    (input : SubmittedParInput certificate vertex) : Vertex :=
  input.side.mate input.storedLeft input.storedRight

private theorem wellFormed
    {certificate : Certificate} {vertex : Vertex}
    (input : SubmittedParInput certificate vertex)
    (structural : certificate.StructurallyWellFormed) :
    certificate.LinkWellFormed
      (.par input.storedLeft input.storedRight input.conclusion) :=
  structural.2.2.2.2.1 _ (List.mem_of_getElem? input.link_eq)

private theorem mate_ne
    {certificate : Certificate} {vertex : Vertex}
    (input : SubmittedParInput certificate vertex)
    (structural : certificate.StructurallyWellFormed) :
    input.mate ≠ vertex := by
  have different := (input.wellFormed structural).1
  have premiseEquation := input.premise_eq
  cases sideEquation : input.side with
  | storedLeft =>
      simp [mate, TensorPremiseSide.mate, TensorPremiseSide.premise,
        sideEquation] at premiseEquation ⊢
      exact fun same => different (premiseEquation.symm.trans same.symm)
  | storedRight =>
      simp [mate, TensorPremiseSide.mate, TensorPremiseSide.premise,
        sideEquation] at premiseEquation ⊢
      exact fun same => different (same.trans premiseEquation)

private theorem mate_bound
    {certificate : Certificate} {vertex : Vertex}
    (input : SubmittedParInput certificate vertex)
    (structural : certificate.StructurallyWellFormed) :
    input.mate < certificate.formulas.size := by
  have wellFormed := input.wellFormed structural
  cases sideEquation : input.side with
  | storedLeft =>
      simpa [mate, TensorPremiseSide.mate, sideEquation] using
        wellFormed.2.2.2.2.1
  | storedRight =>
      simpa [mate, TensorPremiseSide.mate, sideEquation] using
        wellFormed.2.2.2.1

private theorem premise_orientation
    {certificate : Certificate} {vertex : Vertex}
    (input : SubmittedParInput certificate vertex) :
    (input.mate = input.storedLeft ∧ vertex = input.storedRight) ∨
      (input.mate = input.storedRight ∧ vertex = input.storedLeft) := by
  cases sideEquation : input.side with
  | storedLeft =>
      right
      constructor
      · simp [mate, TensorPremiseSide.mate, sideEquation]
      · simpa [TensorPremiseSide.premise, sideEquation] using
          input.premise_eq
  | storedRight =>
      left
      constructor
      · simp [mate, TensorPremiseSide.mate, sideEquation]
      · simpa [TensorPremiseSide.premise, sideEquation] using
          input.premise_eq

end SubmittedParInput

/-- Read-only applicability data for the stable `nop` rule. -/
structure NopInput (certificate : Certificate)
    (before : ReservationState) : Type where
  head : ReadyHeadInput before
  par : SubmittedParInput certificate head.vertex
  mate_unmarked : before.core.marks[par.mate]? = some none

/-- Input-only applicability predicate for `nop`. -/
def NopEnabled (certificate : Certificate)
    (before : ReservationState) : Prop :=
  Nonempty (NopInput certificate before)

namespace NopInput

private theorem directRule
    {certificate : Certificate} {before : ReservationState}
    (input : NopInput certificate before)
    (invariant : SchedulerInvariant certificate before) :
    NopRule certificate before input.head.middle := by
  refine ⟨input.head.vertex, input.head.rawAge, input.par.linkIndex,
    input.par.storedLeft, input.par.storedRight,
    input.par.conclusion, input.par.side,
    input.head.rulePrefix invariant, input.par.link_eq,
    input.par.premise_eq, input.mate_unmarked⟩

private theorem executor_exists
    {certificate : Certificate} {before : ReservationState}
    (input : NopInput certificate before)
    (invariant : SchedulerInvariant certificate before) :
    ∃ next,
      nop? certificate before invariant.toReservationInvariant = some next := by
  exact ⟨input.head.middle,
    nop?_complete_of_structural invariant.structural
      invariant.toReservationInvariant (input.directRule invariant)⟩

end NopInput

/-- Complete scheduler validity turns `NopEnabled` into executable success. -/
theorem nop?_exists_of_enabled
    {certificate : Certificate} {before : ReservationState}
    (invariant : SchedulerInvariant certificate before)
    (enabled : NopEnabled certificate before) :
    ∃ next,
      nop? certificate before invariant.toReservationInvariant = some next := by
  rcases enabled with ⟨input⟩
  exact input.executor_exists invariant

/-- `nop` enabledness yields an executor output carrying the complete
scheduler invariant. -/
theorem nop?_exists_schedulerInvariant_of_enabled
    {certificate : Certificate} {before : ReservationState}
    (invariant : SchedulerInvariant certificate before)
    (enabled : NopEnabled certificate before) :
    ∃ next,
      nop? certificate before invariant.toReservationInvariant = some next ∧
        SchedulerInvariant certificate next := by
  rcases nop?_exists_of_enabled invariant enabled with ⟨next, equation⟩
  exact ⟨next, equation, nop?_schedulerInvariant invariant equation⟩

/-- Read-only applicability data for the stable `wait` rule. -/
structure WaitInput (certificate : Certificate)
    (before : ReservationState) : Type where
  head : ReadyHeadInput before
  par : SubmittedParInput certificate head.vertex
  mateRawAge : RawTokenAge
  mate_marked :
    before.core.marks[par.mate]? = some (some mateRawAge)
  younger : mateRawAge < head.rawAge

/-- Input-only applicability predicate for `wait`. -/
def WaitEnabled (certificate : Certificate)
    (before : ReservationState) : Prop :=
  Nonempty (WaitInput certificate before)

namespace WaitInput

private theorem mate_age_bound
    {certificate : Certificate} {before : ReservationState}
    (input : WaitInput certificate before)
    (invariant : SchedulerInvariant certificate before) :
    input.mateRawAge < before.stack.nextAge := by
  have stackMarked :
      before.stack.marks[input.par.mate]? =
        some (some input.mateRawAge) := by
    rw [← invariant.realizesSigma.marks_eq]
    exact input.mate_marked
  exact invariant.stack_wellShaped.assigned_age_bound
    input.par.mate input.mateRawAge stackMarked

private theorem destination_exists
    {certificate : Certificate} {before : ReservationState}
    (input : WaitInput certificate before)
    (invariant : SchedulerInvariant certificate before) :
    ∃ boundary payload,
      sigmaBoundary? before.stack.sigma input.mateRawAge = some boundary ∧
        before.stack.waiting[boundary]? = some (.initialized payload) := by
  rcases invariant.stack_wellShaped.sigma_partition.boundary_exists
      (input.mate_age_bound invariant) with
    ⟨boundary, boundaryLookup⟩
  have boundaryMembership : boundary ∈ before.stack.sigma :=
    sigmaBoundary?_mem boundaryLookup
  have boundaryLtActive : boundary < input.head.rawAge :=
    Nat.lt_of_le_of_lt (sigmaBoundary?_le boundaryLookup) input.younger
  have boundaryBound : boundary < before.stack.nextAge :=
    invariant.stack_wellShaped.sigma_partition.boundary_lt
      boundary boundaryMembership
  have inactiveMembership : boundary ∈ before.stack.sigma.dropLast := by
    rcases List.getLast?_eq_some_iff.mp input.head.sigma_top with
      ⟨sigmaPrefix, sigmaEquation⟩
    rw [sigmaEquation] at boundaryMembership ⊢
    simp only [List.mem_append, List.mem_singleton] at boundaryMembership
    rcases boundaryMembership with inPrefix | atActive
    · simpa using inPrefix
    · subst boundary
      exact False.elim (Nat.lt_irrefl _ boundaryLtActive)
  rcases
      (invariant.stack_operationalWaitingDomain
        |>.initialized_iff_inactive boundaryBound).mpr inactiveMembership with
    ⟨payload, waitingLookup⟩
  exact ⟨boundary, payload, boundaryLookup, waitingLookup⟩

private def next
    {certificate : Certificate} {before : ReservationState}
    (input : WaitInput certificate before)
    (boundary : RawTokenAge) (payload : List Vertex) : ReservationState where
  stack := {
    input.head.middle.stack with
    waiting := input.head.middle.stack.waiting.setIfInBounds boundary
      (.initialized (input.par.conclusion :: payload)) }
  core := input.head.middle.core
  tags := input.head.middle.tags

private theorem directRule
    {certificate : Certificate} {before : ReservationState}
    (input : WaitInput certificate before)
    (invariant : SchedulerInvariant certificate before)
    (boundary : RawTokenAge) (payload : List Vertex)
    (boundaryLookup :
      sigmaBoundary? before.stack.sigma input.mateRawAge = some boundary)
    (waitingLookup :
      before.stack.waiting[boundary]? = some (.initialized payload)) :
    WaitRule certificate before (input.next boundary payload) := by
  refine ⟨input.head.vertex, input.head.rawAge, input.par.linkIndex,
    input.par.storedLeft, input.par.storedRight, input.par.conclusion,
    input.par.side, input.head.middle, input.mateRawAge, boundary,
    input.head.rulePrefix invariant, input.par.link_eq,
    input.par.premise_eq, input.mate_marked, input.younger, ?_, ?_⟩
  · simpa [ReadyHeadInput.middle, ReadyHeadInput.markedStack] using
      boundaryLookup
  · refine ⟨payload, ?_, rfl, rfl, rfl⟩
    simpa [ReadyHeadInput.middle, ReadyHeadInput.markedStack] using
      waitingLookup

private theorem executor_exists
    {certificate : Certificate} {before : ReservationState}
    (input : WaitInput certificate before)
    (invariant : SchedulerInvariant certificate before) :
    ∃ next,
      wait? certificate before invariant.toReservationInvariant = some next := by
  rcases input.destination_exists invariant with
    ⟨boundary, payload, boundaryLookup, waitingLookup⟩
  exact ⟨input.next boundary payload,
    wait?_complete_of_structural invariant.structural
      invariant.toReservationInvariant
      (input.directRule invariant boundary payload
        boundaryLookup waitingLookup)⟩

end WaitInput

/-- Complete scheduler validity turns `WaitEnabled` into executable success. -/
theorem wait?_exists_of_enabled
    {certificate : Certificate} {before : ReservationState}
    (invariant : SchedulerInvariant certificate before)
    (enabled : WaitEnabled certificate before) :
    ∃ next,
      wait? certificate before invariant.toReservationInvariant = some next := by
  rcases enabled with ⟨input⟩
  exact input.executor_exists invariant

/-- `wait` enabledness yields an executor output carrying the complete
scheduler invariant. -/
theorem wait?_exists_schedulerInvariant_of_enabled
    {certificate : Certificate} {before : ReservationState}
    (invariant : SchedulerInvariant certificate before)
    (enabled : WaitEnabled certificate before) :
    ∃ next,
      wait? certificate before invariant.toReservationInvariant = some next ∧
        SchedulerInvariant certificate next := by
  rcases wait?_exists_of_enabled invariant enabled with ⟨next, equation⟩
  exact ⟨next, equation, wait?_schedulerInvariant invariant equation⟩

/-- Read-only applicability data for the stable `forward` rule.

The witness states only the exact submitted par choice, its pre-state mate
mark, and the paper's non-strict raw-age guard.  Token synchronization,
component ownership, first-occurrence picks, and ready-list freshness are all
derived from the complete scheduler invariant. -/
structure ForwardInput (certificate : Certificate)
    (before : ReservationState) : Type where
  head : ReadyHeadInput before
  par : SubmittedParInput certificate head.vertex
  mateRawAge : RawTokenAge
  mate_marked :
    before.core.marks[par.mate]? = some (some mateRawAge)
  not_older : head.rawAge ≤ mateRawAge

/-- Input-only applicability predicate for `forward`. -/
def ForwardEnabled (certificate : Certificate)
    (before : ReservationState) : Prop :=
  Nonempty (ForwardInput certificate before)

namespace ForwardInput

private theorem prepared_mate_marked
    {certificate : Certificate} {before : ReservationState}
    (input : ForwardInput certificate before)
    (invariant : SchedulerInvariant certificate before) :
    input.head.markedCore.marks[input.par.mate]? =
      some (some input.mateRawAge) := by
  change
    (before.core.marks.setIfInBounds
      input.head.vertex (some input.head.rawAge))[input.par.mate]? =
        some (some input.mateRawAge)
  rw [Array.getElem?_setIfInBounds_ne
    (input.par.mate_ne invariant.structural).symm]
  exact input.mate_marked

private theorem mate_age_bound
    {certificate : Certificate} {before : ReservationState}
    (input : ForwardInput certificate before)
    (invariant : SchedulerInvariant certificate before) :
    input.mateRawAge < input.head.middle.stack.nextAge := by
  have middleInvariant := input.head.middleInvariant invariant
  have stackMarked :
      input.head.middle.stack.marks[input.par.mate]? =
        some (some input.mateRawAge) := by
    rw [← middleInvariant.realizesSigma.marks_eq]
    exact input.prepared_mate_marked invariant
  exact middleInvariant.stack_wellShaped.assigned_age_bound
    input.par.mate input.mateRawAge stackMarked

private theorem mate_token
    {certificate : Certificate} {before : ReservationState}
    (input : ForwardInput certificate before)
    (invariant : SchedulerInvariant certificate before) :
    input.head.markedCore.tokenAt? input.par.mate =
      some input.head.rawAge := by
  have middleInvariant := input.head.middleInvariant invariant
  have boundaryLookup :
      sigmaBoundary? input.head.middle.stack.sigma input.mateRawAge =
        some input.head.rawAge := by
    apply middleInvariant.stack_wellShaped.sigma_partition
      |>.sigmaBoundary?_eq_top_of_le
    · simpa [ReadyHeadInput.middle, ReadyHeadInput.markedStack] using
        input.head.sigma_top
    · exact input.not_older
    · exact input.mate_age_bound invariant
  have realized :
      sigmaBoundary? input.head.middle.stack.sigma input.mateRawAge =
        some (input.head.markedCore.representative input.mateRawAge) :=
    middleInvariant.realizesSigma.representative_eq_boundary
      (input.mate_age_bound invariant)
  have root :
      input.head.markedCore.representative input.mateRawAge =
        input.head.rawAge :=
    Option.some.inj (realized.symm.trans boundaryLookup)
  unfold UnificationState.tokenAt?
  rw [input.prepared_mate_marked invariant]
  simp [root]

private theorem stored_premise_tokens
    {certificate : Certificate} {before : ReservationState}
    (input : ForwardInput certificate before)
    (invariant : SchedulerInvariant certificate before) :
    input.head.markedCore.tokenAt? input.par.storedLeft =
        some input.head.rawAge ∧
      input.head.markedCore.tokenAt? input.par.storedRight =
        some input.head.rawAge := by
  rcases input.par.premise_orientation with orientation | orientation
  · constructor
    · rw [← orientation.1]
      exact input.mate_token invariant
    · rw [← orientation.2]
      exact input.head.selected_token invariant
  · constructor
    · rw [← orientation.2]
      exact input.head.selected_token invariant
    · rw [← orientation.1]
      exact input.mate_token invariant

private theorem conclusion_ne_selected
    {certificate : Certificate} {before : ReservationState}
    (input : ForwardInput certificate before)
    (invariant : SchedulerInvariant certificate before) :
    input.par.conclusion ≠ input.head.vertex := by
  have wellFormed := input.par.wellFormed invariant.structural
  rcases input.par.premise_orientation with orientation | orientation
  · exact fun same =>
      wellFormed.2.2.1 (orientation.2.symm.trans same.symm)
  · exact fun same =>
      wellFormed.2.1 (orientation.2.symm.trans same.symm)

private theorem conclusion_not_produced_before
    {certificate : Certificate} {before : ReservationState}
    (input : ForwardInput certificate before)
    (invariant : SchedulerInvariant certificate before) :
    ¬ Produced before input.par.conclusion := by
  intro produced
  have linkMembership :
      (.par input.par.storedLeft input.par.storedRight
        input.par.conclusion : Link) ∈ certificate.links :=
    List.mem_of_getElem? input.par.link_eq
  rcases invariant.produced_premises_marked linkMembership produced with
    ⟨⟨leftAge, leftMarked⟩, rightAge, rightMarked⟩
  rcases input.par.premise_orientation with orientation | orientation
  · have rightUnmarked :
        before.core.marks[input.par.storedRight]? = some none := by
      rw [← orientation.2]
      exact input.head.core_vertex_unmarked invariant
    rw [rightUnmarked] at rightMarked
    simp at rightMarked
  · have leftUnmarked :
        before.core.marks[input.par.storedLeft]? = some none := by
      rw [← orientation.2]
      exact input.head.core_vertex_unmarked invariant
    rw [leftUnmarked] at leftMarked
    simp at leftMarked

private theorem conclusion_unmarked_before
    {certificate : Certificate} {before : ReservationState}
    (input : ForwardInput certificate before)
    (invariant : SchedulerInvariant certificate before) :
    before.core.marks[input.par.conclusion]? = some none := by
  have conclusionBound :=
    (input.par.wellFormed invariant.structural).2.2.2.2.2.1
  have marksSize : before.core.marks.size = certificate.formulas.size :=
    invariant.core_abstractable.markArraySize
  have coreBound : input.par.conclusion < before.core.marks.size := by
    simpa [marksSize] using conclusionBound
  cases conclusionLookup : before.core.marks[input.par.conclusion]? with
  | none =>
      rw [Array.getElem?_eq_getElem coreBound] at conclusionLookup
      simp at conclusionLookup
  | some mark =>
      cases mark with
      | none => rfl
      | some age =>
          exact (input.conclusion_not_produced_before invariant
            (Or.inl ⟨age, conclusionLookup⟩)).elim

private theorem conclusion_unmarked_middle
    {certificate : Certificate} {before : ReservationState}
    (input : ForwardInput certificate before)
    (invariant : SchedulerInvariant certificate before) :
    input.head.markedCore.marks[input.par.conclusion]? = some none := by
  change
    (before.core.marks.setIfInBounds
      input.head.vertex (some input.head.rawAge))[input.par.conclusion]? =
        some none
  rw [Array.getElem?_setIfInBounds_ne
    (input.conclusion_ne_selected invariant).symm]
  exact input.conclusion_unmarked_before invariant

private theorem ready_mem_liveFrontier
    {certificate : Certificate} {state : ReservationState}
    (invariant : SchedulerInvariant certificate state)
    {vertex : Vertex} (membership : vertex ∈ state.stack.ready.flatten) :
    vertex ∈ state.core.liveFrontierVertices := by
  rcases List.mem_flatten.mp membership with
    ⟨bucket, bucketMembership, vertexMembership⟩
  rcases List.mem_iff_getElem.mp bucketMembership with
    ⟨position, positionBound, positionEquation⟩
  have readyLookup : state.stack.ready[position]? = some bucket := by
    rw [List.getElem?_eq_getElem positionBound, positionEquation]
  have sigmaPositionBound : position < state.stack.sigma.length := by
    rw [← invariant.stack_wellShaped.ready_aligned]
    exact positionBound
  let boundary := state.stack.sigma[position]
  have sigmaLookup : state.stack.sigma[position]? = some boundary :=
    List.getElem?_eq_getElem sigmaPositionBound
  rcases invariant.ready_bucket_frontier_exact sigmaLookup readyLookup with
    ⟨component, componentLookup, exactMembership⟩
  have frontierMembership : vertex ∈ component.frontier :=
    (exactMembership vertex).mp vertexMembership |>.1
  unfold UnificationState.liveFrontierVertices
  apply List.mem_flatMap.mpr
  refine ⟨some component, ?_, ?_⟩
  · exact List.mem_of_getElem? (by simpa using componentLookup)
  · simpa using frontierMembership

private theorem conclusion_not_produced_middle
    {certificate : Certificate} {before : ReservationState}
    (input : ForwardInput certificate before)
    (invariant : SchedulerInvariant certificate before) :
    ¬ Produced input.head.middle input.par.conclusion := by
  intro produced
  apply input.conclusion_not_produced_before invariant
  rcases produced with ⟨age, marked⟩ | frontier
  · left
    refine ⟨age, ?_⟩
    change input.head.markedCore.marks[input.par.conclusion]? =
      some (some age) at marked
    change
      (before.core.marks.setIfInBounds
        input.head.vertex (some input.head.rawAge))[input.par.conclusion]? =
          some (some age) at marked
    rw [Array.getElem?_setIfInBounds_ne
      (input.conclusion_ne_selected invariant).symm] at marked
    exact marked
  · right
    change input.par.conclusion ∈ input.head.markedCore.liveFrontierVertices
      at frontier
    simpa [ReadyHeadInput.markedCore,
      UnificationState.liveFrontierVertices] using frontier

private theorem conclusion_not_ready_middle
    {certificate : Certificate} {before : ReservationState}
    (input : ForwardInput certificate before)
    (invariant : SchedulerInvariant certificate before) :
    input.par.conclusion ∉ input.head.middle.stack.ready.flatten := by
  intro ready
  exact input.conclusion_not_produced_middle invariant
    (Or.inr (ready_mem_liveFrontier
      (input.head.middleInvariant invariant) ready))

private theorem premise_covered
    {certificate : Certificate} {before : ReservationState}
    (input : ForwardInput certificate before)
    (invariant : SchedulerInvariant certificate before)
    {premise : Vertex}
    (premiseMembership :
      premise ∈ [input.par.storedLeft, input.par.storedRight])
    (tokenAt :
      input.head.markedCore.tokenAt? premise = some input.head.rawAge) :
    ∃ component,
      input.head.markedCore.componentAt? input.head.rawAge = some component ∧
        premise ∈ component.frontier := by
  have linkMembership :
      (.par input.par.storedLeft input.par.storedRight
        input.par.conclusion : Link) ∈ certificate.links :=
    List.mem_of_getElem? input.par.link_eq
  exact (input.head.middleInvariant invariant)
    |>.pending_premises_covered_except_ready
      linkMembership (input.conclusion_unmarked_middle invariant)
      (input.conclusion_not_ready_middle invariant)
      premiseMembership tokenAt

private theorem queue_data_exists
    {certificate : Certificate} {before : ReservationState}
    (input : ForwardInput certificate before)
    (invariant : SchedulerInvariant certificate before) :
    ∃ (component : UnificationComponent)
        (leftFocus : Nat) (leftRemainder : List Vertex)
        (rightFocus : Nat) (context : List Vertex),
      input.head.markedCore.forwardToken?
          input.par.storedLeft input.par.storedRight input.par.conclusion =
        some input.head.rawAge ∧
      input.head.markedCore.componentAt? input.head.rawAge = some component ∧
      Certificate.FirstOccurrencePick component.frontier
        input.par.storedLeft leftFocus leftRemainder ∧
      Certificate.FirstOccurrencePick leftRemainder
        input.par.storedRight rightFocus context := by
  have tokens := input.stored_premise_tokens invariant
  rcases input.premise_covered invariant (by simp) tokens.1 with
    ⟨leftComponent, leftLookup, leftMembership⟩
  rcases input.premise_covered invariant (by simp) tokens.2 with
    ⟨rightComponent, rightLookup, rightMembership⟩
  have componentEquation : rightComponent = leftComponent :=
    Option.some.inj (rightLookup.symm.trans leftLookup)
  subst rightComponent
  rcases Certificate.FirstOccurrencePick.two_of_mem
      (input.par.wellFormed invariant.structural).1
      leftMembership rightMembership with
    ⟨leftFocus, leftRemainder, rightFocus, context,
      leftPick, rightPick⟩
  have tokenGuard :
      input.head.markedCore.forwardToken?
          input.par.storedLeft input.par.storedRight input.par.conclusion =
        some input.head.rawAge := by
    simp [UnificationState.forwardToken?,
      input.conclusion_unmarked_middle invariant, tokens.1, tokens.2]
  exact ⟨leftComponent, leftFocus, leftRemainder, rightFocus, context,
    tokenGuard, leftLookup, leftPick, rightPick⟩

private def next
    {certificate : Certificate} {before : ReservationState}
    (input : ForwardInput certificate before)
    (component : UnificationComponent)
    (leftFocus rightFocus : Nat) (context : List Vertex) :
    ReservationState where
  stack := {
    input.head.middle.stack with
    ready := before.stack.ready.dropLast ++
      [input.par.conclusion :: input.head.readyTail] }
  core := {
    input.head.markedCore with
    components := input.head.markedCore.components.setIfInBounds
      input.head.rawAge
      (some {
        tree := .par leftFocus rightFocus component.tree
        frontier := context ++ [input.par.conclusion] })
    firedConnectives := input.head.markedCore.firedConnectives + 1 }
  tags := before.tags

private theorem directRule
    {certificate : Certificate} {before : ReservationState}
    (input : ForwardInput certificate before)
    (invariant : SchedulerInvariant certificate before)
    (component : UnificationComponent)
    (leftFocus : Nat) (leftRemainder : List Vertex)
    (rightFocus : Nat) (context : List Vertex)
    (tokenGuard :
      input.head.markedCore.forwardToken?
          input.par.storedLeft input.par.storedRight input.par.conclusion =
        some input.head.rawAge)
    (componentLookup :
      input.head.markedCore.componentAt? input.head.rawAge = some component)
    (leftPick :
      Certificate.FirstOccurrencePick component.frontier
        input.par.storedLeft leftFocus leftRemainder)
    (rightPick :
      Certificate.FirstOccurrencePick leftRemainder
        input.par.storedRight rightFocus context) :
    ForwardRule certificate before
      (input.next component leftFocus rightFocus context) := by
  refine ⟨input.head.vertex, input.head.rawAge, input.par.linkIndex,
    input.par.storedLeft, input.par.storedRight, input.par.conclusion,
    input.par.side, input.head.middle, input.mateRawAge, input.head.rawAge,
    component, leftFocus, leftRemainder, rightFocus, context,
    before.stack.ready.dropLast, input.head.readyTail,
    input.head.rulePrefix invariant, input.par.link_eq,
    input.par.premise_eq, input.mate_marked, input.not_older,
    tokenGuard, componentLookup, rfl, leftPick, rightPick,
    rfl, rfl, rfl, rfl⟩

private theorem executor_exists
    {certificate : Certificate} {before : ReservationState}
    (input : ForwardInput certificate before)
    (invariant : SchedulerInvariant certificate before) :
    ∃ next,
      forward? certificate before invariant.toReservationInvariant = some next := by
  rcases input.queue_data_exists invariant with
    ⟨component, leftFocus, leftRemainder, rightFocus, context,
      tokenGuard, componentLookup, leftPick, rightPick⟩
  exact ⟨input.next component leftFocus rightFocus context,
    forward?_complete_of_schedulerInvariant invariant
      (input.directRule invariant component leftFocus leftRemainder
        rightFocus context tokenGuard componentLookup leftPick rightPick)⟩

end ForwardInput

/-- Complete scheduler validity turns `ForwardEnabled` into executable
success. -/
theorem forward?_exists_of_enabled
    {certificate : Certificate} {before : ReservationState}
    (invariant : SchedulerInvariant certificate before)
    (enabled : ForwardEnabled certificate before) :
    ∃ next,
      forward? certificate before invariant.toReservationInvariant = some next := by
  rcases enabled with ⟨input⟩
  exact input.executor_exists invariant

/-- `forward` enabledness yields an executor output carrying the complete
scheduler invariant. -/
theorem forward?_exists_schedulerInvariant_of_enabled
    {certificate : Certificate} {before : ReservationState}
    (invariant : SchedulerInvariant certificate before)
    (enabled : ForwardEnabled certificate before) :
    ∃ next,
      forward? certificate before invariant.toReservationInvariant = some next ∧
        SchedulerInvariant certificate next := by
  rcases forward?_exists_of_enabled invariant enabled with ⟨next, equation⟩
  exact ⟨next, equation, forward?_schedulerInvariant invariant equation⟩

/-- A selected exact submitted par in a complete invariant state falls into
one of the three raw-mark cases used by `nop`, `wait`, and `forward`.

This is deliberately scoped to an already supplied ready head and submitted
par.  It says nothing about conclusions, tensors, `new`, unification,
dispatcher priority, or whether an arbitrary invariant state has ready work. -/
theorem submittedParInput_enabled_cases
    {certificate : Certificate} {before : ReservationState}
    (invariant : SchedulerInvariant certificate before)
    (head : ReadyHeadInput before)
    (par : SubmittedParInput certificate head.vertex) :
    NopEnabled certificate before ∨
      WaitEnabled certificate before ∨
        ForwardEnabled certificate before := by
  have mateBound : par.mate < before.core.marks.size := by
    rw [invariant.core_abstractable.markArraySize]
    exact par.mate_bound invariant.structural
  cases mateLookup : before.core.marks[par.mate]? with
  | none =>
      rw [Array.getElem?_eq_getElem mateBound] at mateLookup
      simp at mateLookup
  | some mark =>
      cases mark with
      | none =>
          exact Or.inl ⟨{
            head
            par
            mate_unmarked := mateLookup }⟩
      | some mateRawAge =>
          by_cases younger : mateRawAge < head.rawAge
          · exact Or.inr (Or.inl ⟨{
              head
              par
              mateRawAge
              mate_marked := mateLookup
              younger }⟩)
          · exact Or.inr (Or.inr ⟨{
              head
              par
              mateRawAge
              mate_marked := mateLookup
              not_older := Nat.le_of_not_gt younger }⟩)

end SequentialFigure7

end ProofNetIR
