import ProofNetIR.Figure7.Termination

namespace ProofNetIR
namespace Figure7TerminationTests

open SequentialSchedulerBridge SequentialFigure7

/-! The single-axiom certificate: two formula occurrences, so the history bound is
two, and the canonical dispatcher stops after exactly two calls. -/

private def axiomCertificate : Certificate where
  formulas := #[.atom "p" true, .atom "p" false]
  links := [.axiom 0 1]
  conclusions := [0, 1]

private theorem structural : axiomCertificate.StructurallyWellFormed :=
  (Certificate.wellFormed_iff_structurallyWellFormed axiomCertificate).mp (by decide)

private def initial : ReservationState :=
  (initializeReservation? axiomCertificate 0).getD (ReservationState.empty axiomCertificate)

private theorem initial_eq : initializeReservation? axiomCertificate 0 = some initial := by
  native_decide

private theorem initialInvariant : SchedulerInvariant axiomCertificate initial :=
  initializeReservation?_schedulerInvariant structural initial_eq

private def first : Figure7DispatchResult :=
  (dispatch? axiomCertificate initial initialInvariant).getD ⟨.concl, initial⟩

private theorem first_eq : dispatch? axiomCertificate initial initialInvariant = some first := by
  native_decide

private theorem firstInvariant : SchedulerInvariant axiomCertificate first.after :=
  dispatch?_schedulerInvariant initialInvariant first_eq

private def second : Figure7DispatchResult :=
  (dispatch? axiomCertificate first.after firstInvariant).getD ⟨.concl, first.after⟩

private theorem second_eq :
    dispatch? axiomCertificate first.after firstInvariant = some second := by
  native_decide

private theorem secondInvariant : SchedulerInvariant axiomCertificate second.after :=
  dispatch?_schedulerInvariant firstInvariant second_eq

private theorem stopped : dispatch? axiomCertificate second.after secondInvariant = none := by
  native_decide

-- Two actual dispatcher successes attain the formula-count bound.
example : ∃ history : ExecutedHistory axiomCertificate second.after,
    history.dispatchCount = 2 ∧ history.dispatchCount ≤ axiomCertificate.formulas.size := by
  rcases initializeReservation?_some_iff.mp initial_eq with ⟨initStep⟩
  rcases (dispatch?_some_iff initialInvariant).mp first_eq with ⟨firstStep⟩
  rcases (dispatch?_some_iff firstInvariant).mp second_eq with ⟨secondStep⟩
  exact ⟨.later (.later (.init initStep) initialInvariant firstStep) firstInvariant secondStep,
    rfl, ExecutedHistory.dispatchCount_le _⟩

example : dispatchMeasure initial = 0 ∧ dispatchMeasure first.after = 1 ∧
    dispatchMeasure second.after = 2 := by native_decide

example : dispatchMeasure second.after ≤ axiomCertificate.formulas.size :=
  dispatchMeasure_le secondInvariant

example : dispatchMeasure first.after = dispatchMeasure initial + 1 ∧
    dispatchMeasure initial < dispatchMeasure first.after := by
  rcases (dispatch?_some_iff initialInvariant).mp first_eq with ⟨step⟩
  exact ⟨step.measure_eq, step.measure_lt⟩

private def run : Nat → ReservationState
  | 0 => initial
  | 1 => first.after
  | _ + 2 => second.after

-- Only the two indices below the bound carry an obligation; the stop at index
-- two is a conclusion of `dispatch_stops`, not one of its premises.
private theorem follows (n : Nat) (bound : n < axiomCertificate.formulas.size)
    (invariant : SchedulerInvariant axiomCertificate (run n))
    (result : Figure7DispatchResult)
    (equation : dispatch? axiomCertificate (run n) invariant = some result) :
    result.after = run (n + 1) := by
  cases n with
  | zero =>
      have eq : first = result := Option.some.inj (first_eq.symm.trans equation)
      rw [← eq]
      rfl
  | succ n =>
      cases n with
      | zero =>
          have eq : second = result := Option.some.inj (second_eq.symm.trans equation)
          rw [← eq]
          rfl
      | succ n =>
          have size : axiomCertificate.formulas.size = 2 := rfl
          omega

example : ∃ n < 3, ∃ invariant : SchedulerInvariant axiomCertificate (run n),
    dispatch? axiomCertificate (run n) invariant = none :=
  dispatch_stops run initialInvariant follows

end Figure7TerminationTests
end ProofNetIR

#print axioms ProofNetIR.SequentialFigure7.DispatchTagEvidence.after_core_marks_eq_prepared
#print axioms ProofNetIR.SequentialFigure7.dispatchMeasure_le
#print axioms ProofNetIR.SequentialFigure7.DispatchStep.measure_eq
#print axioms ProofNetIR.SequentialFigure7.DispatchStep.measure_lt
#print axioms ProofNetIR.SequentialFigure7.ExecutedHistory.dispatchCount_le
#print axioms ProofNetIR.SequentialFigure7.dispatch_stops

def main : IO Unit :=
  IO.println "Figure-7 termination consumer passed: two dispatches, bound 2, stop at index 2"
