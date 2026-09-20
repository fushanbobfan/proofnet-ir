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

example {cert : Certificate} {state : ReservationState}
    (invariant : SchedulerInvariant cert state) (drained : ActiveTopDrained state) :
    ∃ age seed, state.stack.sigma.getLast? = some age ∧
      state.stack.ready.getLast? = some [] ∧
      markClass? state.stack seed = some age ∧ seed < cert.formulas.size :=
  seed_of_drained invariant drained

example {cert : Certificate} {state : ReservationState}
    (reachable : ReachableByImplementedDispatcher cert state)
    (correct : cert.DeclarativelyCorrect) (marked : state.core.allMarked = true) :
    ∃ component, state.core.liveComponents = [component] ∧
      component.frontier.Perm cert.conclusions := by
  obtain ⟨_, component, _, _, _, _, live, witness, covers⟩ :=
    finalComponents_eq_singleton reachable correct marked
  exact ⟨component, live, Certificate.finalFrontier_perm correct.1 witness covers⟩

example {cert : Certificate} {state : ReservationState}
    (reachable : ReachableByImplementedDispatcher cert state)
    (correct : cert.DeclarativelyCorrect) (marked : state.core.allMarked = true) :
    (cert.sequentialFinalTree? state).isSome = true ∧
      ∃ (component : UnificationComponent) (order : List Nat),
        Certificate.occurrenceOrder? component.frontier cert.conclusions = some order ∧
        order.Nodup := by
  obtain ⟨component, order, _, _, _, _, _, orderEq, nodup, _, finalEq⟩ :=
    Certificate.sequentialFinalTree?_eq_some reachable correct marked
  exact ⟨by simp [finalEq], component, order, orderEq, nodup⟩

example {cert : Certificate} {state : ReservationState}
    (reachable : ReachableByImplementedDispatcher cert state)
    (correct : cert.DeclarativelyCorrect) (marked : state.core.allMarked = true) :
    ∃ tree output, cert.sequentialFinalTree? state = some tree ∧
      tree.desequentialize? = some output ∧ output.check = true := by
  obtain ⟨tree, _, finalEq, _, _, output, built, checked⟩ :=
    Certificate.sequentialFinalTree?_infer_eq reachable correct marked
  exact ⟨tree, output, finalEq, built, checked⟩

example : ∃ fragment,
    (CutFreeDerivation.exchange [1, 0] (.axiom "p" true)).build? = some fragment ∧
      Certificate.OccurrenceBuildMatch certificate fragment [1, 0] [0] [0, 1] [0, 1] := by
  obtain ⟨fragment, built, matched⟩ := Certificate.occurrenceBuild_axiom_eq correct.1
    (index := 0) (left := 0) (right := 1) (name := "p") (positive := true) rfl rfl
  exact Certificate.occurrenceBuild_exchange_eq built matched (by decide +kernel)

private def repeated : Certificate where
  formulas := #[.atom "p" true, .atom "p" false, .atom "p" true, .atom "p" false,
    .tensor (.atom "p" true) (.atom "p" true)]
  links := [.axiom 0 1, .axiom 2 3, .tensor 0 2 4]
  conclusions := [3, 4, 1]

example : repeated.check = true := by decide +kernel
example : repeated.sequentialFastCheck = true := by native_decide

end ProofNetIR.Figure7SequentialTests

#print axioms ProofNetIR.SequentialFigure7.runDispatcher_spec
#print axioms ProofNetIR.Certificate.sequentialFastCheck_sound
#print axioms ProofNetIR.Certificate.StructurallyWellFormed.formulaComplexityAt_lt_size
#print axioms ProofNetIR.Certificate.StructurallyWellFormed.initializeReservation?_isSome
#print axioms ProofNetIR.SequentialFigure7.seed_of_drained
#print axioms ProofNetIR.SequentialFigure7.finalComponents_eq_singleton
#print axioms ProofNetIR.Certificate.finalFrontier_perm
#print axioms ProofNetIR.Certificate.sequentialFinalTree?_eq_some
#print axioms ProofNetIR.Certificate.sequentialFinalTree?_infer_eq
#print axioms ProofNetIR.Certificate.occurrenceBuild_axiom_eq
#print axioms ProofNetIR.Certificate.occurrenceBuild_exchange_eq

def main : IO Unit := do
  let accepted := ProofNetIR.Figure7SequentialTests.certificate.sequentialFastCheck
  let rejected := ProofNetIR.Figure7SequentialTests.rejected.sequentialFastCheck
  let repeated := ProofNetIR.Figure7SequentialTests.repeated.sequentialFastCheck
  unless accepted && !rejected && repeated do
    throw (IO.userError "sequential fast path regression failed")
  IO.println ("Sequential consumer passed: final structure, inference, " ++
    "axiom/exchange numbering, repeated-label tensor")
