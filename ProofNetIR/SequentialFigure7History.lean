import ProofNetIR.SequentialFigure7New

namespace ProofNetIR

/-!
# Executed history for the implemented Figure-7 fragment

This module records genuine executions of the currently implemented
deterministic scheduler fragment: exact initialization followed by zero or
more successful operational `new` steps.  It deliberately does not identify
an arbitrary invariant-satisfying state with a reachable state, and it does
not include the reservation-only helper, the literal printed `new`, or any
still-unimplemented Figure-7 rule.

The dependent history retains every exact search result and transition
equation.  This supports history-level tag provenance, global non-reuse of a
submitted axiom-link slot, and exact event-count alignment without making a
progress or completeness claim.
-/

namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge

/-- Pointwise monotonicity of boolean tag carriers. -/
def TagsExtend (older newer : Array Bool) : Prop :=
  ∀ ⦃vertex : Vertex⦄,
    older[vertex]? = some true → newer[vertex]? = some true

namespace TagsExtend

/-- Every tag carrier pointwise extends itself. -/
theorem refl (tags : Array Bool) : TagsExtend tags tags :=
  by
    intro vertex inputTrue
    exact inputTrue

/-- Pointwise tag extension composes transitively. -/
theorem trans {first second third : Array Bool}
    (firstSecond : TagsExtend first second)
    (secondThird : TagsExtend second third) :
    TagsExtend first third :=
  by
    intro vertex inputTrue
    exact secondThird (firstSecond inputTrue)

end TagsExtend

/-- Exact output tag projection of an initialization witness. -/
theorem initial_output_tags_eq
    {certificate : Certificate} {after : ReservationState}
    {start : Vertex}
    (step : InitialReservationStep certificate after start) :
    after.tags = step.result.tags := by
  simpa using congrArg ReservationState.tags step.output_eq

/-- Initialization preserves every pre-existing true tag.  Its concrete input
is all false, but the theorem is useful as the uniform first history step. -/
theorem initial_tagsExtend
    {certificate : Certificate} {after : ReservationState}
    {start : Vertex}
    (step : InitialReservationStep certificate after start) :
    TagsExtend (ReservationState.empty certificate).tags after.tags := by
  intro vertex inputTrue
  rw [initial_output_tags_eq step]
  exact step.result.preservesTrue inputTrue

namespace NewStep

/-- Exact output tag projection of a complete operational `new` witness. -/
theorem output_tags_eq
    {certificate : Certificate}
    {before after : ReservationState}
    (step : NewStep certificate before after) :
    after.tags = step.search.tags := by
  simpa using congrArg ReservationState.tags step.output_eq

/-- A complete operational `new` only adds true tags. -/
theorem tagsExtend
    {certificate : Certificate}
    {before after : ReservationState}
    (step : NewStep certificate before after) :
    TagsExtend before.tags after.tags := by
  intro vertex inputTrue
  rw [step.output_tags_eq]
  exact step.search.preservesTrue inputTrue

end NewStep

/-- Proof-relevant history of exactly the implemented init/new reservation
fragment.

`empty` is the zero-event run.  `init` is intrinsically tied to the exact
empty production state by `InitialReservationStep`.  Every `later` constructor
stores a complete operational `new`, not the reservation-only helper.  This
type is intentionally not a generic Figure-7 rule history. The implemented
non-reserving rules need separate rule-step accounting. The canonical
dispatcher history in `SequentialFigure7Dispatcher` now accounts for exact
successful `concl`, `nop`, `new`, `wait`, `forward`, and arbitrary-payload
`unifyPayload` executions. Those steps are deliberately not retrofitted into this
reservation-event history, whose route-touch, submitted-slot, and event-count
laws remain specific to `init`/`new`. -/
inductive InitNewHistory (certificate : Certificate) :
    ReservationState → Type
  | empty :
      InitNewHistory certificate (ReservationState.empty certificate)
  | init {after : ReservationState} {start : Vertex} :
      InitialReservationStep certificate after start →
      InitNewHistory certificate after
  | later {before after : ReservationState} :
      InitNewHistory certificate before →
      NewStep certificate before after →
      InitNewHistory certificate after

/-- Honest reachability for exactly the implemented init/new fragment. -/
def ReachableByImplementedInitNew
    (certificate : Certificate) (state : ReservationState) : Prop :=
  Nonempty (InitNewHistory certificate state)

namespace InitNewHistory

/-- Vertices touched by any exact `NEXTAXIOM` search in the history. -/
def Touched
    {certificate : Certificate} {state : ReservationState} :
    InitNewHistory certificate state → Vertex → Prop
  | .empty => fun _ => False
  | .init step => step.result.Touched
  | .later history step =>
      fun vertex => history.Touched vertex ∨ step.search.Touched vertex

/-- Submitted axiom-link slots, newest first. -/
def linkIndices
    {certificate : Certificate} {state : ReservationState} :
    InitNewHistory certificate state → List Nat
  | .empty => []
  | .init step => [step.result.linkIndex]
  | .later history step => step.search.linkIndex :: history.linkIndices

/-- Number of exact axiom-search/reservation events. -/
def length
    {certificate : Certificate} {state : ReservationState} :
    InitNewHistory certificate state → Nat
  | .empty => 0
  | .init _ => 1
  | .later history _ => history.length + 1

/-- Every state named by an executed history satisfies the current
reservation-layer invariant.  This is a consequence of execution, not the
definition of reachability. -/
theorem reservationInvariant
    {certificate : Certificate} {state : ReservationState}
    (history : InitNewHistory certificate state) :
    ReservationInvariant certificate state := by
  cases history with
  | empty => exact empty_reservationInvariant certificate
  | init step => exact step.reservationInvariant
  | later _history step => exact step.reservationInvariant

/-- Exact tag provenance for the implemented history: a current true tag
exists exactly when some recorded search touched that vertex. -/
theorem tagged_iff_touched
    {certificate : Certificate} {state : ReservationState}
    (history : InitNewHistory certificate state)
    {vertex : Vertex} :
    state.tags[vertex]? = some true ↔ history.Touched vertex := by
  induction history with
  | empty =>
      constructor
      · intro outputTrue
        rcases Array.getElem?_eq_some_iff.mp outputTrue with
          ⟨vertexBound, value⟩
        simp [ReservationState.empty] at value
      · intro impossible
        exact False.elim impossible
  | init step =>
      rw [initial_output_tags_eq step,
        SequentialUnification.nextAxiom?_tagged_iff_input_or_touched
          step.search_eq]
      constructor
      · rintro (inputTrue | touched)
        · rcases Array.getElem?_eq_some_iff.mp inputTrue with
            ⟨vertexBound, value⟩
          simp [ReservationState.empty] at value
        · exact touched
      · intro touched
        exact Or.inr touched
  | later history step induction =>
      rw [step.output_tags_eq,
        SequentialUnification.nextAxiom?_tagged_iff_input_or_touched
          step.search_eq,
        induction]
      rfl

/-- Every earlier touched vertex is unavailable to the next exact search. -/
theorem touched_disjoint_next
    {certificate : Certificate}
    {before after : ReservationState}
    (history : InitNewHistory certificate before)
    (step : NewStep certificate before after)
    {vertex : Vertex}
    (oldTouched : history.Touched vertex)
    (newTouched : step.search.Touched vertex) :
    False := by
  have oldTrue : before.tags[vertex]? = some true :=
    (history.tagged_iff_touched).2 oldTouched
  have newFalse :=
    (SequentialUnification.nextAxiomWithFuel?_touched_tagged
      step.search_eq newTouched).1
  rw [oldTrue] at newFalse
  contradiction

/-- Membership in the history's submitted-slot list carries an exact axiom
lookup and a touched endpoint witness. -/
theorem mem_linkIndices_witness
    {certificate : Certificate} {state : ReservationState}
    (history : InitNewHistory certificate state)
    {index : Nat}
    (membership : index ∈ history.linkIndices) :
    ∃ left right,
      certificate.links[index]? = some (.axiom left right) ∧
        history.Touched left := by
  induction history with
  | empty =>
      simp [linkIndices] at membership
  | init step =>
      simp [linkIndices] at membership
      subst index
      exact ⟨step.result.left, step.result.right,
        step.result.exactLink, by
          simp [Touched, SequentialUnification.NextAxiomResult.Touched]⟩
  | later history step induction =>
      simp only [linkIndices, List.mem_cons] at membership
      rcases membership with current | old
      · subst index
        exact ⟨step.search.left, step.search.right,
          step.search.exactLink, by
            exact Or.inr (by
              simp [SequentialUnification.NextAxiomResult.Touched])⟩
      · rcases induction old with
          ⟨left, right, exactLink, oldTouched⟩
        exact ⟨left, right, exactLink, Or.inl oldTouched⟩

/-- No submitted axiom-link slot occurs twice anywhere in a genuine
implemented history.  This strengthens the adjacent replay theorem to the
whole recorded execution and still deliberately distinguishes duplicate link
slots with equal values. -/
theorem linkIndices_nodup
    {certificate : Certificate} {state : ReservationState}
    (history : InitNewHistory certificate state) :
    history.linkIndices.Nodup := by
  induction history with
  | empty => simp [linkIndices]
  | init step => simp [linkIndices]
  | later history step induction =>
      rw [linkIndices, List.nodup_cons]
      refine ⟨?_, induction⟩
      intro oldMembership
      rcases history.mem_linkIndices_witness oldMembership with
        ⟨oldLeft, oldRight, oldLink, oldTouched⟩
      have sameAxiom :
          Link.axiom oldLeft oldRight =
            Link.axiom step.search.left step.search.right := by
        exact Option.some.inj
          (oldLink.symm.trans step.search.exactLink)
      have sameLeft : oldLeft = step.search.left := by
        injection sameAxiom
      subst oldLeft
      exact history.touched_disjoint_next step
        oldTouched (by
          simp [SequentialUnification.NextAxiomResult.Touched])

/-- Event count agrees with the raw-age allocation horizon. -/
theorem length_eq_nextAge
    {certificate : Certificate} {state : ReservationState}
    (history : InitNewHistory certificate state) :
    history.length = state.stack.nextAge := by
  induction history with
  | empty =>
      simp [length, ReservationState.empty,
        SequentialStackState.empty]
  | init step =>
      rcases SequentialStackState.initEnqueue?_exact step.stack_eq with
        ⟨_, nextAge, _, _, _, _⟩
      have outputNextAge :=
        congrArg
          (fun output : ReservationState => output.stack.nextAge)
          step.output_eq
      calc
        (InitNewHistory.init step).length = 1 := rfl
        _ = step.stackAfter.nextAge := nextAge.symm
        _ = _ := outputNextAge.symm
  | later history step induction =>
      rcases
          SequentialStackState.popReadyMark?_exact step.stack_eq with
        ⟨topEquation, sigmaTopEquation, unmarked, marksEquation,
          popNextAgeEquation, popSigmaEquation, popReadyEquation,
          popWaitingEquation, marked⟩
      rcases
          SequentialStackState.operationalNewEnqueue?_exact
            step.stack_enqueue_eq with
        ⟨active, activeEquation, activeLt, marksEquation,
          nextAgeEquation, sigmaEquation, readyEquation,
          waitingEquation, activeInitialized, freshUndefined⟩
      have outputNextAge :=
        congrArg
          (fun output : ReservationState => output.stack.nextAge)
          step.output_eq
      calc
        (InitNewHistory.later history step).length =
            history.length + 1 := rfl
        _ = step.stackResult.after.nextAge + 1 := by
          rw [induction, popNextAgeEquation]
        _ = step.stackAfter.nextAge := nextAgeEquation.symm
        _ = _ := outputNextAge.symm

/-- The same event count agrees with the production axiom counter. -/
theorem length_eq_startedAxioms
    {certificate : Certificate} {state : ReservationState}
    (history : InitNewHistory certificate state) :
    history.length = state.core.startedAxioms := by
  calc
    history.length = state.stack.nextAge :=
      history.length_eq_nextAge
    _ = state.core.parents.size :=
      history.reservationInvariant.realizesSigma.horizon_eq.symm
    _ = state.core.startedAxioms :=
      history.reservationInvariant.core_counter_aligned.symm

end InitNewHistory

/-- The exact empty state is reachable by the zero-event history. -/
theorem reachable_empty (certificate : Certificate) :
    ReachableByImplementedInitNew certificate
      (ReservationState.empty certificate) :=
  ⟨InitNewHistory.empty⟩

/-- Every successful executable initialization creates an exact history. -/
theorem reachable_of_initializeReservation?_eq_some
    {certificate : Certificate} {after : ReservationState}
    {start : Vertex}
    (equation :
      initializeReservation? certificate start = some after) :
    ReachableByImplementedInitNew certificate after := by
  rcases (initializeReservation?_some_iff.mp equation) with ⟨step⟩
  exact ⟨InitNewHistory.init step⟩

/-- Extending an executed history by a successful complete operational `new`
creates another executed history. -/
theorem ReachableByImplementedInitNew.new
    {certificate : Certificate}
    {before after : ReservationState}
    (reachable : ReachableByImplementedInitNew certificate before)
    (invariant : ReservationInvariant certificate before)
    (equation :
      new? certificate before invariant = some after) :
    ReachableByImplementedInitNew certificate after := by
  rcases reachable with ⟨history⟩
  rcases (new?_some_iff invariant).mp equation with ⟨step⟩
  exact ⟨InitNewHistory.later history step⟩

end SequentialFigure7

end ProofNetIR
