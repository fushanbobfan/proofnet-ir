import ProofNetIR.Figure7.Sequential

namespace ProofNetIR.Figure7SequentialTests

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

private theorem initialEq : initializeReservation? certificate 0 = some initial := by
  decide +kernel

private theorem initialReachable : ReachableByImplementedDispatcher certificate initial := by
  obtain ⟨step⟩ := initializeReservation?_some_iff.mp initialEq
  exact ⟨.init step⟩

-- The bounded run from the initial state ends reachable, fully marked, and stopped.
example :
    let final := runDispatcher certificate (certificate.formulas.size + 1) initial
      (initializeReservation?_schedulerInvariant correct.1 initialEq)
    ReachableByImplementedDispatcher certificate final ∧
      ∃ finalInvariant : SchedulerInvariant certificate final,
        dispatch? certificate final finalInvariant = none ∧ final.core.allMarked = true :=
  runDispatcher_spec (initializeReservation?_schedulerInvariant correct.1 initialEq)
    initialReachable correct (by decide +kernel)

-- The executable accepts this certificate and its acceptance is sound.
example : certificate.sequentialFastCheck = true := by native_decide

example : certificate.sequentialReconstruct?.isSome = true := by native_decide

example (accepted : certificate.sequentialFastCheck = true) : certificate.check = true :=
  certificate.sequentialFastCheck_sound accepted

-- A wrong certificate is rejected: the par of two non-dual atoms fails well-formedness.
private def rejected : Certificate where
  formulas := #[.atom "p" true, .atom "q" false,
    .par (.atom "p" true) (.atom "q" false)]
  links := [.axiom 0 1, .par 0 1 2]
  conclusions := [2]

example : rejected.sequentialFastCheck = false := by native_decide

-- Initialization succeeds at every in-bounds start, through the carrier complexity bound.
example : ∃ state, initializeReservation? certificate 2 = some state :=
  correct.1.initializeReservation?_isSome (by decide)

example : certificate.formulaComplexityAt 2 < certificate.formulas.size :=
  correct.1.formulaComplexityAt_lt_size (by decide)

example {cert : Certificate} (structural : cert.StructurallyWellFormed) {start : Vertex}
    (bound : start < cert.formulas.size) : ∃ state, initializeReservation? cert start = some state :=
  structural.initializeReservation?_isSome bound

end ProofNetIR.Figure7SequentialTests

#print axioms ProofNetIR.SequentialFigure7.runDispatcher_spec
#print axioms ProofNetIR.Certificate.sequentialFastCheck_sound
#print axioms ProofNetIR.Certificate.StructurallyWellFormed.formulaComplexityAt_lt_size
#print axioms ProofNetIR.Certificate.StructurallyWellFormed.initializeReservation?_isSome

def main : IO Unit := do
  let accepted := ProofNetIR.Figure7SequentialTests.certificate.sequentialFastCheck
  let rejected := ProofNetIR.Figure7SequentialTests.rejected.sequentialFastCheck
  unless accepted && !rejected do
    throw (IO.userError "sequential fast path regression failed")
  IO.println "Sequential consumer passed: bounded run spec, accepted axiom-par net, rejected non-dual net, soundness, initialization totality"
