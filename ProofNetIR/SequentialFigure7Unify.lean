import ProofNetIR.SequentialFigure7UnifyOne

namespace ProofNetIR

/-!
# Arbitrary waiting-payload activation fold

This module starts the general Figure-7 `unify` layer by making the delayed
waiting-payload activation order explicit.  Guerrini's `W(j)` is a set and
therefore does not prescribe an iteration order.  ProofNet-IR stores that set
as a duplicate-free list and deterministically activates the stored payload
from head to tail.  This order is a representation choice: it fixes the exact
derivation-tree nesting and executable output, but is not claimed to be a
paper-level temporal, token-age, or complexity order.

The fold below threads the production core.  Reusing one stale input core for
all payload elements would overwrite earlier par constructions and is
therefore deliberately not represented.  This module proves the local fold
correspondence and the preservation facts that are independent of the final
scheduler drain.  A later atomic `unify` witness will combine one tensor
construction, this fold, and the ready/waiting merge under a transient gap
invariant; no intermediate fold state is claimed to satisfy the complete
`SchedulerInvariant`.
-/

namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerBridge
open SequentialUnification

/-- Independent Boolean-free relation for activating a stored waiting payload
from head to tail.  Each step uses the direct one-par relation and threads the
resulting production core into the rest of the payload. -/
inductive WaitingParActivationFoldRule (certificate : Certificate) :
    UnificationState → List Vertex → UnificationState → Prop where
  | nil (state : UnificationState) :
      WaitingParActivationFoldRule certificate state [] state
  | cons {before middle after : UnificationState}
      {conclusion : Vertex} {payload : List Vertex}
      (head :
        WaitingParActivationRule certificate before middle conclusion)
      (tail :
        WaitingParActivationFoldRule certificate middle payload after) :
      WaitingParActivationFoldRule certificate before
        (conclusion :: payload) after

/-- Proof-relevant executable trace for one head-to-tail waiting-payload
activation fold. -/
inductive WaitingParActivationFoldStep (certificate : Certificate) :
    UnificationState → List Vertex → UnificationState → Type where
  | nil (state : UnificationState) :
      WaitingParActivationFoldStep certificate state [] state
  | cons {before middle after : UnificationState}
      {conclusion : Vertex} {payload : List Vertex}
      (head :
        WaitingParActivationStep certificate before middle conclusion)
      (tail :
        WaitingParActivationFoldStep certificate middle payload after) :
      WaitingParActivationFoldStep certificate before
        (conclusion :: payload) after

/-- Execute the deterministic stored-order waiting-payload activation fold. -/
def activateWaitingPayload? (certificate : Certificate) :
    UnificationState → List Vertex → Option UnificationState
  | state, [] => some state
  | state, conclusion :: payload =>
      match activateWaitingPar? certificate state conclusion with
      | none => none
      | some middle => activateWaitingPayload? certificate middle payload

/-- Executable payload activation succeeds exactly when its proof-relevant
threaded trace exists. -/
theorem activateWaitingPayload?_some_iff
    {certificate : Certificate} {before after : UnificationState}
    {payload : List Vertex} :
    activateWaitingPayload? certificate before payload = some after ↔
      Nonempty
        (WaitingParActivationFoldStep certificate before payload after) := by
  induction payload generalizing before after with
  | nil =>
      constructor
      · intro equation
        have stateEquation : before = after := by
          exact Option.some.inj equation
        subst after
        exact ⟨.nil before⟩
      · rintro ⟨step⟩
        cases step
        rfl
  | cons conclusion payload induction =>
      constructor
      · intro equation
        rw [activateWaitingPayload?] at equation
        cases headEquation :
            activateWaitingPar? certificate before conclusion with
        | none =>
            simp [headEquation] at equation
        | some middle =>
            rw [headEquation] at equation
            rcases activateWaitingPar?_some_iff.mp headEquation with
              ⟨headStep⟩
            rcases induction.mp equation with ⟨tailStep⟩
            exact ⟨.cons headStep tailStep⟩
      · rintro ⟨step⟩
        cases step with
        | cons headStep tailStep =>
            rw [activateWaitingPayload?]
            rw [activateWaitingPar?_some_iff.mpr ⟨headStep⟩]
            exact induction.mpr ⟨tailStep⟩

namespace WaitingParActivationFoldStep

/-- A typed fold refines the independent direct fold relation. -/
theorem toRule
    {certificate : Certificate} {before after : UnificationState}
    {payload : List Vertex}
    (step :
      WaitingParActivationFoldStep certificate before payload after) :
    WaitingParActivationFoldRule certificate before payload after := by
  induction step with
  | nil state => exact .nil state
  | cons head tail induction =>
      exact .cons head.toRule induction

/-- Waiting-payload activation preserves the raw-mark array exactly. -/
theorem marks_eq
    {certificate : Certificate} {before after : UnificationState}
    {payload : List Vertex}
    (step :
      WaitingParActivationFoldStep certificate before payload after) :
    after.marks = before.marks := by
  induction step with
  | nil state => rfl
  | cons head tail induction =>
      exact induction.trans head.exact.2.1

/-- Waiting-payload activation preserves the parent forest exactly. -/
theorem parents_eq
    {certificate : Certificate} {before after : UnificationState}
    {payload : List Vertex}
    (step :
      WaitingParActivationFoldStep certificate before payload after) :
    after.parents = before.parents := by
  induction step with
  | nil state => rfl
  | cons head tail induction =>
      exact induction.trans head.exact.2.2.1

/-- Waiting-payload activation does not start any new axiom component. -/
theorem startedAxioms_eq
    {certificate : Certificate} {before after : UnificationState}
    {payload : List Vertex}
    (step :
      WaitingParActivationFoldStep certificate before payload after) :
    after.startedAxioms = before.startedAxioms := by
  induction step with
  | nil state => rfl
  | cons head tail induction =>
      exact induction.trans head.exact.2.2.2.1

/-- Each delayed par replaces one in-bounds component cell without resizing
the production carrier. -/
theorem components_size_eq
    {certificate : Certificate} {before after : UnificationState}
    {payload : List Vertex}
    (step :
      WaitingParActivationFoldStep certificate before payload after) :
    after.components.size = before.components.size := by
  induction step with
  | nil state => rfl
  | @cons before middle after conclusion payload head tail induction =>
      have headSize :
          middle.components.size = before.components.size := by
        rw [head.exact.1]
        simp
      exact induction.trans headSize

/-- The project representation constructs exactly one delayed par per payload
element, hence the local connective counter increases by the payload length.
This is not a claim about the number of paper-level Figure-7 transitions. -/
theorem firedConnectives_eq_add_length
    {certificate : Certificate} {before after : UnificationState}
    {payload : List Vertex}
    (step :
      WaitingParActivationFoldStep certificate before payload after) :
    after.firedConnectives = before.firedConnectives + payload.length := by
  induction step with
  | nil state => simp
  | cons head tail induction =>
      have headCounter := head.exact.2.2.2.2
      simp only [List.length_cons]
      omega

/-- The threaded activation fold preserves the abstraction contract. -/
theorem abstractable
    {certificate : Certificate} {before after : UnificationState}
    {payload : List Vertex}
    (step :
      WaitingParActivationFoldStep certificate before payload after)
    (abstractable : before.Abstractable certificate) :
    after.Abstractable certificate := by
  induction step with
  | nil state => exact abstractable
  | cons head tail induction =>
      exact induction
        (Certificate.queuePar?_abstractable abstractable head.queue_eq)

/-- The threaded activation fold leaves an ordered parent forest ordered. -/
theorem orderedParents
    {certificate : Certificate} {before after : UnificationState}
    {payload : List Vertex}
    (step :
      WaitingParActivationFoldStep certificate before payload after)
    (ordered : before.OrderedParents) :
    after.OrderedParents := by
  induction step with
  | nil state => exact ordered
  | cons head tail induction =>
      exact induction
        (Certificate.queuePar?_orderedParents ordered head.queue_eq)

/-- Exact submitted producers make every fold element formula-consistent. -/
theorem componentsFormulaConsistent
    {certificate : Certificate} {before after : UnificationState}
    {payload : List Vertex}
    (step :
      WaitingParActivationFoldStep certificate before payload after)
    (consistent : before.ComponentsFormulaConsistent certificate) :
    after.ComponentsFormulaConsistent certificate := by
  induction step with
  | nil state => exact consistent
  | cons head tail induction =>
      exact induction
        (Certificate.queuePar?_componentsFormulaConsistent consistent
          head.producer.wellFormed head.queue_eq)

/-- The fold preserves component/parent and started-axiom/parent carrier
alignment without changing either carrier's size. -/
theorem reservationAlignment
    {certificate : Certificate} {before after : UnificationState}
    {payload : List Vertex}
    (step :
      WaitingParActivationFoldStep certificate before payload after)
    (carrier : before.components.size = before.parents.size)
    (counter : before.startedAxioms = before.parents.size) :
    after.components.size = after.parents.size ∧
      after.startedAxioms = after.parents.size := by
  induction step with
  | nil state => exact ⟨carrier, counter⟩
  | cons head tail induction =>
      rcases Certificate.queuePar?_reservationAlignment carrier counter
          head.queue_eq with
        ⟨middleCarrier, middleCounter⟩
      exact induction middleCarrier middleCounter

/-- A proof-relevant fold has one exact output for fixed input and payload. -/
theorem output_unique
    {certificate : Certificate} {before first second : UnificationState}
    {payload : List Vertex}
    (left :
      WaitingParActivationFoldStep certificate before payload first)
    (right :
      WaitingParActivationFoldStep certificate before payload second) :
    first = second := by
  have leftExecutable :
      activateWaitingPayload? certificate before payload = some first :=
    activateWaitingPayload?_some_iff.mpr ⟨left⟩
  have rightExecutable :
      activateWaitingPayload? certificate before payload = some second :=
    activateWaitingPayload?_some_iff.mpr ⟨right⟩
  exact Option.some.inj (leftExecutable.symm.trans rightExecutable)

end WaitingParActivationFoldStep

/-- Executable payload activation is sound for the independent direct fold. -/
theorem activateWaitingPayload?_sound
    {certificate : Certificate} {before after : UnificationState}
    {payload : List Vertex}
    (equation :
      activateWaitingPayload? certificate before payload = some after) :
    WaitingParActivationFoldRule certificate before payload after := by
  rcases activateWaitingPayload?_some_iff.mp equation with ⟨step⟩
  exact step.toRule

/-- Every direct stored-order activation fold reconstructs the executable
fold. -/
theorem activateWaitingPayload?_complete
    {certificate : Certificate} {before after : UnificationState}
    {payload : List Vertex}
    (rule :
      WaitingParActivationFoldRule certificate before payload after) :
    activateWaitingPayload? certificate before payload = some after := by
  induction rule with
  | nil state => rfl
  | cons head tail induction =>
      rw [activateWaitingPayload?]
      rw [activateWaitingPar?_complete head]
      exact induction

/-- Exact executable/direct correspondence for the stored-order payload
activation fold. -/
theorem activateWaitingPayload?_some_iff_rule
    {certificate : Certificate} {before after : UnificationState}
    {payload : List Vertex} :
    activateWaitingPayload? certificate before payload = some after ↔
      WaitingParActivationFoldRule certificate before payload after :=
  ⟨activateWaitingPayload?_sound, activateWaitingPayload?_complete⟩

/-- The independent direct payload-fold relation has one exact output. -/
theorem WaitingParActivationFoldRule.output_unique
    {certificate : Certificate} {before first second : UnificationState}
    {payload : List Vertex}
    (left :
      WaitingParActivationFoldRule certificate before payload first)
    (right :
      WaitingParActivationFoldRule certificate before payload second) :
    first = second := by
  have leftExecutable := activateWaitingPayload?_complete left
  have rightExecutable := activateWaitingPayload?_complete right
  exact Option.some.inj (leftExecutable.symm.trans rightExecutable)

end SequentialFigure7

end ProofNetIR
