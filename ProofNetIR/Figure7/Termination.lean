import ProofNetIR.SequentialFigure7RawMarkHistory

namespace ProofNetIR

/-!
# Bounded canonical dispatcher histories

Every successful dispatcher branch marks exactly the occurrence popped by its
prepared prefix and nothing else, so the number of marked occurrences rises by
one per successful `dispatch?` call and is bounded by the formula carrier.
Executed histories therefore contain at most `certificate.formulas.size`
dispatcher calls, and any run that keeps feeding successful outputs back into
`dispatch?` meets `none` by that index.

This bounds history length only. It does not prove progress, later-state
totality, completeness of the terminal state, or a complexity bound on
individual steps.
-/

namespace SequentialFigure7

open SequentialSchedulerBridge

/-- Number of marked formula occurrences in the production core. -/
def dispatchMeasure (state : ReservationState) : Nat :=
  state.core.marks.countP Option.isSome

/-- The scheduler invariant bounds the measure by the formula carrier. -/
theorem dispatchMeasure_le {certificate : Certificate} {state : ReservationState}
    (invariant : SchedulerInvariant certificate state) :
    dispatchMeasure state ≤ certificate.formulas.size := by
  unfold dispatchMeasure
  exact Nat.le_trans (Array.countP_le_size (p := @Option.isSome Nat) (xs := state.core.marks))
    (Nat.le_of_eq invariant.core_abstractable.markArraySize)

private theorem rawMark_count {before after : UnificationState} {vertex age : Nat}
    (equation : before.markReadyRaw? vertex age = .ok after) :
    after.marks.countP Option.isSome = before.marks.countP Option.isSome + 1 := by
  rcases UnificationState.markReadyRaw?_exact equation with
    ⟨unmarked, marks, _⟩
  obtain ⟨bound, value⟩ := Array.getElem?_eq_some_iff.mp unmarked
  rw [marks]
  simp [Array.setIfInBounds, bound, Array.countP_set, value]

/-- Every exact canonical dispatcher success marks exactly one more occurrence. -/
theorem DispatchStep.measure_eq {certificate : Certificate} {before : ReservationState}
    {invariant : SchedulerInvariant certificate before} {result : Figure7DispatchResult}
    (step : DispatchStep certificate before invariant result) :
    dispatchMeasure result.after = dispatchMeasure before + 1 := by
  rcases step.tagEvidence with ⟨evidence⟩
  unfold dispatchMeasure
  rw [evidence.after_core_marks_eq_prepared]
  exact rawMark_count evidence.prepared.core_mark_eq

/-- Every exact canonical dispatcher success strictly increases the measure. -/
theorem DispatchStep.measure_lt {certificate : Certificate} {before : ReservationState}
    {invariant : SchedulerInvariant certificate before} {result : Figure7DispatchResult}
    (step : DispatchStep certificate before invariant result) :
    dispatchMeasure before < dispatchMeasure result.after := by
  rw [step.measure_eq]
  omega

/-- Number of successful canonical dispatcher calls in a history. Initialization is
outside `dispatch?`, so empty and initialized histories both count zero. -/
def ExecutedHistory.dispatchCount {certificate : Certificate} {state : ReservationState} :
    ExecutedHistory certificate state → Nat
  | .empty => 0
  | .init _ => 0
  | .later history _ _ => history.dispatchCount + 1

private theorem dispatchCount_le_measure {certificate : Certificate}
    {state : ReservationState} (history : ExecutedHistory certificate state) :
    history.dispatchCount ≤ dispatchMeasure state := by
  induction history with
  | empty => exact Nat.zero_le _
  | init _ => exact Nat.zero_le _
  | later history invariant step ih =>
      have increase := step.measure_lt
      change history.dispatchCount + 1 ≤ _
      omega

/-- Every executed history has at most one dispatcher call per formula occurrence.
No certificate-validity hypothesis is needed: nonempty dispatcher traces carry
the scheduler invariant, and initialization alone counts zero. -/
theorem ExecutedHistory.dispatchCount_le {certificate : Certificate}
    {state : ReservationState} (history : ExecutedHistory certificate state) :
    history.dispatchCount ≤ certificate.formulas.size := by
  cases history with
  | empty => exact Nat.zero_le _
  | init _ => exact Nat.zero_le _
  | later history invariant step =>
      exact Nat.le_trans (dispatchCount_le_measure (.later history invariant step))
        (dispatchMeasure_le step.schedulerInvariant)

/-- A run that starts with the scheduler invariant and feeds every successful
output below index `formulas.size` into the next state meets `dispatch? = none`
at some index at most `formulas.size`. The hypothesis constrains exactly the
indices below `formulas.size` at which `dispatch?` succeeds, whether or not an
earlier index failed; nothing is assumed about the run at or beyond
`formulas.size`, and a success there is already impossible by the measure bound.
This does not assert progress or terminal-state completeness. -/
theorem dispatch_stops {certificate : Certificate} (run : Nat → ReservationState)
    (initial : SchedulerInvariant certificate (run 0))
    (follows : ∀ n, n < certificate.formulas.size →
      ∀ (invariant : SchedulerInvariant certificate (run n)) result,
        dispatch? certificate (run n) invariant = some result → result.after = run (n + 1)) :
    ∃ n < certificate.formulas.size + 1,
      ∃ invariant : SchedulerInvariant certificate (run n),
        dispatch? certificate (run n) invariant = none := by
  classical
  apply Classical.byContradiction
  intro noStop
  have growth : ∀ n, n ≤ certificate.formulas.size + 1 →
      ∃ invariant : SchedulerInvariant certificate (run n), n ≤ dispatchMeasure (run n) := by
    intro n
    induction n with
    | zero => intro _; exact ⟨initial, Nat.zero_le _⟩
    | succ n ih =>
        intro bound
        obtain ⟨invariant, previous⟩ := ih (by omega)
        cases equation : dispatch? certificate (run n) invariant with
        | none => exact False.elim (noStop ⟨n, by omega, invariant, equation⟩)
        | some result =>
            rcases (dispatch?_some_iff invariant).mp equation with ⟨step⟩
            have increase := step.measure_eq
            have nextInvariant := step.schedulerInvariant
            have upper := dispatchMeasure_le nextInvariant
            by_cases below : n < certificate.formulas.size
            · rw [follows n below invariant result equation] at increase nextInvariant
              exact ⟨nextInvariant, by omega⟩
            · exfalso
              omega
  obtain ⟨invariant, lower⟩ := growth (certificate.formulas.size + 1) (Nat.le_refl _)
  have upper := dispatchMeasure_le invariant
  omega

end SequentialFigure7
end ProofNetIR
