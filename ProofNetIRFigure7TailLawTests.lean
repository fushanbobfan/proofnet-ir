import ProofNetIR.Figure7.TailLaw

namespace ProofNetIR.Figure7TailLawTests

open SequentialFigure7 SequentialSchedulerBridge

private def certificate : Certificate where
  formulas := #[.atom "p" true, .atom "p" false,
    .par (.atom "p" true) (.atom "p" false)]
  links := [.axiom 0 1, .par 0 1 2]
  conclusions := [2]

private theorem correct : certificate.DeclarativelyCorrect :=
  certificate.check_iff_declarativelyCorrect.mp (by decide)

private def initial :=
  (initializeReservation? certificate 0).getD (ReservationState.empty certificate)

private theorem initialEq : initializeReservation? certificate 0 = some initial := by decide +kernel

private theorem initialC12 : ParHeadGuardTailNonconclusion certificate initial := by
  obtain ⟨step⟩ := initializeReservation?_some_iff.mp initialEq
  exact SequentialFigure7.InitialReservationStep.parHeadGuardTail step correct

-- An actual canonical nop consumes the first endpoint and retains its partner.
example : ∃ after, Nonempty (NopStep certificate initial after) ∧
    ∃ step : NopStep certificate initial after,
      ∃ pending, pending ∈ step.prepared.stackResult.remainingTop ∧
        pending ∉ certificate.conclusions := by
  let invariant := initializeReservation?_schedulerInvariant correct.1 initialEq
  have success : (nop? certificate initial invariant.toReservationInvariant).isSome := by
    decide +kernel
  obtain ⟨after, equation⟩ := Option.isSome_iff_exists.mp success
  obtain ⟨step⟩ := (nop?_some_iff invariant.toReservationInvariant).mp equation
  obtain ⟨pending, member, notGlobal⟩ := step.tailNonconclusion_of_parHeadGuard initialC12
  exact ⟨after, ⟨step⟩, step, pending, member, notGlobal⟩

example {cert : Certificate} {before after : ReservationState}
    (step : WaitStep cert before after)
    (law : ParHeadGuardTailNonconclusion cert before) :
    ∃ pending, pending ∈ step.prepared.stackResult.remainingTop ∧ pending ∉ cert.conclusions := by
  obtain ⟨pending, member, notGlobal⟩ := step.tailNonconclusion_of_parHeadGuard law
  exact ⟨pending, member, notGlobal⟩

-- The obstruction concerns induction on C12 alone, not reachable-state validity.
example : ¬ (∀ {cert : Certificate} {before after : ReservationState}
    (invariant : SchedulerInvariant cert before), cert.DeclarativelyCorrect →
    ParHeadGuardTailNonconclusion cert before →
    Nonempty (DispatchStep cert before invariant ⟨.nop, after⟩) →
    ParHeadGuardTailNonconclusion cert after) := by
  intro preservation
  obtain ⟨cert, before, after, invariant, valid, prior, step, failed, _unreachable⟩ :=
    parHeadGuardTail_not_inductive
  exact failed (preservation invariant valid prior step)

end ProofNetIR.Figure7TailLawTests

#print axioms ProofNetIR.SequentialFigure7.InitialReservationStep.parHeadGuardTail
#print axioms ProofNetIR.SequentialFigure7.NopStep.tailNonconclusion_of_parHeadGuard
#print axioms ProofNetIR.SequentialFigure7.WaitStep.tailNonconclusion_of_parHeadGuard
#print axioms ProofNetIR.SequentialFigure7.parHeadGuardTail_not_inductive

def main : IO Unit :=
  IO.println "C12 consumer passed: initialization, nop/wait implications, preservation obstruction"
