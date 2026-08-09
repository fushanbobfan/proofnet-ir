/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7TagHistory

namespace ProofNetIR

/-!
# Figure-7 canonical raw-mark history

Every successful non-initial Figure-7 dispatcher branch executes the same
prepared prefix: it pops one ready occurrence and raw-marks that occurrence at
the selected immutable raw age.  `CanonicalTagHistory` already retains exact
typed evidence for all six branches, not only for the `new` branch that changes
search tags.  This module reuses that carrier to record raw-mark events without
introducing a parallel history type.

The one-step theorem says that an output raw mark is either an unchanged input
mark or exactly the occurrence/raw-age pair selected by the current prepared
prefix.  Induction over the canonical history then characterizes every final
raw mark by an authentic dispatcher event.

`RawMarked` is deliberately distinct from `DispatchTagEvidence.Touched` and
`CanonicalTagHistory.Touched`: stable branches can raw-mark connective
conclusions without running `NEXTAXIOM`.  This layer records provenance only.
It does not prove cross-component source-region separation, discharge any
created-candidate seam, establish dispatcher progress, or remove the recursive
fallback.
-/

namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge
open SequentialUnification

private theorem initial_no_core_rawMarked
    {certificate : Certificate} {after : ReservationState} {start : Vertex}
    (step : InitialReservationStep certificate after start)
    (rawAge : RawTokenAge) (vertex : Vertex) :
    after.core.marks[vertex]? ≠ some (some rawAge) := by
  intro marked
  have output := congrArg
    (fun state : ReservationState ↦ state.core.marks) step.output_eq
  rcases certificate.reserveAxiomAt?_exact step.core_eq with
    ⟨_left, _right, _component, _exactLink, _ready, _componentLookup,
      _frontier, marksEq, _parents, _components, _started, _fired⟩
  have finalMarks :
      after.core.marks = certificate.initialUnificationState.marks :=
    output.trans marksEq
  rw [finalMarks] at marked
  change (Array.replicate certificate.formulas.size none)[vertex]? =
    some (some rawAge) at marked
  rw [Array.getElem?_replicate] at marked
  split at marked <;> simp at marked

private def new_prepared
    {certificate : Certificate} {before after : ReservationState}
    (step : NewStep certificate before after) : PreparedStep before where
  stackResult := step.stackResult
  coreMarked := step.coreMarked
  stack_eq := step.stack_eq
  core_mark_eq := step.core_mark_eq

private theorem new_after_marks_eq_markedMiddle
    {certificate : Certificate} {before after : ReservationState}
    (step : NewStep certificate before after) :
    after.core.marks = step.markedMiddle.core.marks := by
  have afterCore : after.core = step.coreAfter :=
    congrArg (fun state : ReservationState ↦ state.core) step.output_eq
  rcases certificate.reserveAxiomAt?_exact step.core_reserve_eq with
    ⟨_left, _right, _component, _link, _ready, _lookup, _frontier,
      marksEquation, _parents, _components, _counter, _fired⟩
  rw [afterCore]
  exact marksEquation

private theorem unify_after_marks_eq_prepared
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after) :
    after.core.marks = step.prepared.after.core.marks := by
  have afterCore : after.core = step.coreAfter :=
    congrArg (fun state : ReservationState ↦ state.core) step.output_eq
  rw [afterCore]
  change step.coreAfter.marks = step.prepared.coreMarked.marks
  rw [step.activationFold.marks_eq]
  rw [step.tensorStep.after_eq]

namespace PreparedStep

private theorem after_rawMarked_iff
    {before : ReservationState} (step : PreparedStep before)
    {rawAge : RawTokenAge} {vertex : Vertex} :
    step.after.core.marks[vertex]? = some (some rawAge) ↔
      before.core.marks[vertex]? = some (some rawAge) ∨
        (rawAge = step.stackResult.rawAge ∧
          vertex = step.stackResult.vertex) := by
  rcases UnificationState.markReadyRaw?_exact step.core_mark_eq with
    ⟨selectedUnmarked, marksEq, _parents, _components, _started, _fired,
      selectedMarked⟩
  constructor
  · intro marked
    by_cases same : vertex = step.stackResult.vertex
    · right
      subst vertex
      change step.coreMarked.marks[step.stackResult.vertex]? =
        some (some rawAge) at marked
      rw [selectedMarked] at marked
      exact ⟨by simpa using marked.symm, rfl⟩
    · left
      change step.coreMarked.marks[vertex]? = some (some rawAge) at marked
      rw [marksEq] at marked
      simpa [Array.getElem?_setIfInBounds, Ne.symm same] using marked
  · rintro (old | ⟨rfl, rfl⟩)
    · by_cases same : vertex = step.stackResult.vertex
      · subst vertex
        rw [selectedUnmarked] at old
        simp at old
      · change step.coreMarked.marks[vertex]? = some (some rawAge)
        rw [marksEq]
        simpa [Array.getElem?_setIfInBounds, Ne.symm same] using old
    · change step.coreMarked.marks[step.stackResult.vertex]? =
        some (some step.stackResult.rawAge)
      exact selectedMarked

end PreparedStep

namespace DispatchTagEvidence

/-- The exact prepared prefix retained by one branch-aligned dispatcher
evidence witness.

Although the carrier is named for tag effects, every constructor stores the
typed rule witness and therefore the common pop/raw-mark prefix as well.
-/
def prepared
    {certificate : Certificate} {before : ReservationState}
    {result : Figure7DispatchResult}
    (evidence : DispatchTagEvidence certificate before result) :
    PreparedStep before :=
  match evidence with
  | .concl step => step.prepared
  | .nop step => step.prepared
  | .new step => new_prepared step
  | .wait step => step.prepared
  | .forward step => step.prepared
  | .unifyPayload step => step.prepared

/-- The exact occurrence/raw-age pair newly marked by one dispatcher event.

This relation is not a `NEXTAXIOM` touch relation.  All six successful rule
families contribute exactly one prepared raw-mark event.
-/
def RawMarked
    {certificate : Certificate} {before : ReservationState}
    {result : Figure7DispatchResult}
    (evidence : DispatchTagEvidence certificate before result)
    (rawAge : RawTokenAge) (vertex : Vertex) : Prop :=
  rawAge = evidence.prepared.stackResult.rawAge ∧
    vertex = evidence.prepared.stackResult.vertex

private theorem after_core_marks_eq_prepared
    {certificate : Certificate} {before : ReservationState}
    {result : Figure7DispatchResult}
    (evidence : DispatchTagEvidence certificate before result) :
    result.after.core.marks = evidence.prepared.after.core.marks := by
  cases evidence with
  | concl step =>
      have output := congrArg
        (fun state : ReservationState ↦ state.core.marks) step.output_eq
      simpa only [prepared] using output
  | nop step =>
      have output := congrArg
        (fun state : ReservationState ↦ state.core.marks) step.output_eq
      simpa only [prepared] using output
  | new step =>
      simpa only [prepared, NewStep.markedMiddle, new_prepared,
        PreparedStep.after] using new_after_marks_eq_markedMiddle step
  | wait step =>
      have output := congrArg
        (fun state : ReservationState ↦ state.core.marks)
        step.destination.output_eq
      simpa only [prepared] using output
  | forward step =>
      have output := congrArg
        (fun state : ReservationState ↦ state.core.marks) step.output_eq
      have queued := congrArg
        (fun core : UnificationState ↦ core.marks) step.queueStep.after_eq
      simpa only [prepared, PreparedStep.after] using output.trans queued
  | unifyPayload step =>
      simpa only [prepared] using unify_after_marks_eq_prepared step

/-- One successful dispatcher step has exactly the expected raw-mark effect:
an output mark either already existed on input or is the current prepared
selection. -/
theorem final_rawMarked_iff_old_or_event
    {certificate : Certificate} {before : ReservationState}
    {result : Figure7DispatchResult}
    (evidence : DispatchTagEvidence certificate before result)
    {rawAge : RawTokenAge} {vertex : Vertex} :
    result.after.core.marks[vertex]? = some (some rawAge) ↔
      before.core.marks[vertex]? = some (some rawAge) ∨
        evidence.RawMarked rawAge vertex := by
  rw [evidence.after_core_marks_eq_prepared]
  simpa only [RawMarked] using
    (evidence.prepared.after_rawMarked_iff
      (rawAge := rawAge) (vertex := vertex))

end DispatchTagEvidence

namespace CanonicalTagHistory

/-- An occurrence/raw-age pair selected by some authentic dispatcher event in
the supplied canonical history.

The relation is accumulated independently of the history's search-touch
relation.  Initialization contributes no raw mark; every later dispatcher
event contributes its one prepared selection.
-/
def RawMarked
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state} :
    CanonicalTagHistory certificate history →
      RawTokenAge → Vertex → Prop
  | .empty => fun _ _ ↦ False
  | .init _step => fun _ _ ↦ False
  | .later prior evidence =>
      fun rawAge vertex ↦
        prior.RawMarked rawAge vertex ∨ evidence.RawMarked rawAge vertex

/-- Final concrete raw marks are characterized exactly by authentic prepared
selection events in the canonical history. -/
theorem final_rawMarked_iff
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    {rawAge : RawTokenAge} {vertex : Vertex} :
    state.core.marks[vertex]? = some (some rawAge) ↔
      tagHistory.RawMarked rawAge vertex := by
  induction tagHistory with
  | empty =>
      constructor
      · intro marked
        change (Array.replicate certificate.formulas.size none)[vertex]? =
          some (some rawAge) at marked
        rw [Array.getElem?_replicate] at marked
        split at marked <;> simp at marked
      · intro impossible
        exact False.elim impossible
  | init step =>
      constructor
      · intro marked
        exact False.elim (initial_no_core_rawMarked step rawAge vertex marked)
      · intro impossible
        exact False.elim impossible
  | later prior evidence induction =>
      rw [evidence.final_rawMarked_iff_old_or_event, induction]
      rfl

end CanonicalTagHistory

namespace ExecutedHistory

/-- Every final raw mark in an exact executed history has an authentic
prepared-selection event in a canonical augmentation of that same history. -/
theorem final_rawMarked_has_event
    {certificate : Certificate} {state : ReservationState}
    (history : ExecutedHistory certificate state)
    {rawAge : RawTokenAge} {vertex : Vertex}
    (marked : state.core.marks[vertex]? = some (some rawAge)) :
    ∃ tagHistory : CanonicalTagHistory certificate history,
      tagHistory.RawMarked rawAge vertex := by
  rcases history.hasCanonicalTagHistory with ⟨tagHistory⟩
  exact ⟨tagHistory, tagHistory.final_rawMarked_iff.mp marked⟩

end ExecutedHistory

namespace ReachableByImplementedDispatcher

/-- Every concrete raw mark in a certified dispatcher-reachable state is
witnessed by an authentic prepared-selection event in an exact history ending
at that state. -/
theorem final_rawMarked_has_event
    {certificate : Certificate} {state : ReservationState}
    (reachable : ReachableByImplementedDispatcher certificate state)
    {rawAge : RawTokenAge} {vertex : Vertex}
    (marked : state.core.marks[vertex]? = some (some rawAge)) :
    ∃ history : ExecutedHistory certificate state,
      ∃ tagHistory : CanonicalTagHistory certificate history,
        tagHistory.RawMarked rawAge vertex := by
  rcases reachable with ⟨history⟩
  exact ⟨history, history.final_rawMarked_has_event marked⟩

end ReachableByImplementedDispatcher

end SequentialFigure7

end ProofNetIR
