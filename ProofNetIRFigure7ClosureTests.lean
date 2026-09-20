import ProofNetIR.Figure7.Closure

namespace ProofNetIR.Figure7ClosureTests

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

-- Region closure holds after initialization and yields C12 through connectedness.
private theorem initialClosure : RegionClosure certificate initial.stack := by
  obtain ⟨step⟩ := initializeReservation?_some_iff.mp initialEq
  exact RegionClosure.ofInitialReservation step correct.1

example : ParHeadGuardTailNonconclusion certificate initial :=
  initialClosure.guardedParHeadTail (initializeReservation?_schedulerInvariant correct.1 initialEq) correct

-- The cutting switching of any set separating two vertices has a boundary edge.
example : ∃ u v, (fun vertex ↦ decide (vertex = 0)) u = true ∧
    (fun vertex ↦ decide (vertex = 0)) v = false ∧
    (certificate.graphForSelection
      (certificate.parChoices.map (cutChoice fun vertex ↦ decide (vertex = 0)))).Adjacent u v :=
  boundary_edge_of_correct correct (fun vertex ↦ decide (vertex = 0)) (start := 0) (finish := 1)
    (by decide) (by decide) (by decide) (by decide)

-- The closure is order-free: it is stated on the stack and never inspects bucket order.
example (closure : RegionClosure certificate initial.stack)
    (invariant : SchedulerInvariant certificate initial) :
    ParHeadGuardTailNonconclusion certificate initial :=
  closure.guardedParHeadTail invariant correct

end ProofNetIR.Figure7ClosureTests

#print axioms ProofNetIR.SequentialFigure7.boundary_edge_of_correct
#print axioms ProofNetIR.SequentialFigure7.RegionClosure.guardedParHeadTail
#print axioms ProofNetIR.SequentialFigure7.RegionClosure.ofInitialReservation

def main : IO Unit :=
  IO.println "Region-closure consumer passed: initialization, C12 from closure, switching boundary"
