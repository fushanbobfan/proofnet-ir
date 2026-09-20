import ProofNetIR.Figure7.Enabledness

namespace ProofNetIR.Figure7EnablednessTests

open SequentialFigure7 SequentialSchedulerBridge

private def certificate : Certificate where
  formulas := #[.atom "p" true, .atom "p" false, .atom "q" true, .atom "q" false,
    .tensor (.atom "p" true) (.atom "q" true)]
  links := [.axiom 0 1, .axiom 2 3, .tensor 0 2 4]
  conclusions := [1, 3, 4]

private theorem correct : certificate.DeclarativelyCorrect :=
  certificate.check_iff_declarativelyCorrect.mp (by decide +kernel)

private def initial :=
  (initializeReservation? certificate 0).getD (ReservationState.empty certificate)

private theorem initialEq : initializeReservation? certificate 0 = some initial := by decide +kernel

private theorem reachable : ReachableByImplementedDispatcher certificate initial :=
  dispatcher_reachable_of_initializeReservation?_eq_some initialEq

private def guard : NewGuard certificate initial where
  head := {
    vertex := 0
    readyTail := [1]
    rawAge := 0
    top_ready := by decide +kernel
    sigma_top := by decide +kernel }
  tensor := ⟨2, 0, 2, 4, .storedLeft⟩
  tensor_valid := Certificate.tensorBelow?_eq_some_iff.mp (by decide +kernel)
  mate_unmarked := by decide +kernel

example : NewEnabled certificate initial :=
  figure7Enabledness_started_and_sequentialize.1 reachable correct guard

example : ∃ kind,
    PriorityEnabled certificate initial (reachable.schedulerInvariant correct.1) kind :=
  (figure7Enabledness_started_and_sequentialize.2.1 reachable correct
    (by decide +kernel)).mpr (by decide +kernel)

example (enabled : ∃ kind,
    PriorityEnabled certificate initial (reachable.schedulerInvariant correct.1) kind) :
    0 < initial.stack.nextAge :=
  (figure7Enabledness_started_and_sequentialize.2.1 reachable correct
    (by decide +kernel)).mp enabled

example : ∃ result : ExecutableSequentializationResult certificate,
    certificate.sequentialize = .ok result :=
  figure7Enabledness_started_and_sequentialize.2.2 certificate (by decide +kernel)

-- The original three-conjunct D5 target is refuted without changing its statement.
example : ¬ ((∀ {certificate state},
    ReachableByImplementedDispatcher certificate state →
    certificate.DeclarativelyCorrect →
    NewGuard certificate state → NewEnabled certificate state) ∧
  (∀ {certificate state}
    (reachable : ReachableByImplementedDispatcher certificate state)
    (correct : certificate.DeclarativelyCorrect),
    let invariant := reachable.schedulerInvariant correct.1
    state.core.allMarked ≠ true →
      ∃ kind, PriorityEnabled certificate state invariant kind) ∧
  (∀ certificate : Certificate, certificate.check = true →
    ∃ result : ExecutableSequentializationResult certificate,
      certificate.sequentialize = .ok result)) :=
  fun claimed ↦ priorityEnabled_not_allReachable claimed.2.1

def smoke : IO Unit := do
  let empty := ReservationState.empty certificate
  let emptyInvariant := (dispatcher_reachable_empty certificate).schedulerInvariant correct.1
  unless !empty.core.allMarked && empty.stack.nextAge == 0 do
    throw (IO.userError "unexpected empty scheduler marks or age")
  unless (dispatch? certificate empty emptyInvariant).isNone do
    throw (IO.userError "empty scheduler unexpectedly dispatched")
  let invariant := reachable.schedulerInvariant correct.1
  unless (dispatch? certificate initial invariant).map Figure7DispatchResult.kind == some .new do
    throw (IO.userError "guarded tensor did not dispatch new")
  match certificate.sequentialize with
  | .ok _ => pure ()
  | .error _ => throw (IO.userError "accepted certificate failed recursive sequentialization")
  IO.println ("Enabledness consumer passed: new guard, started iff, " ++
    "unstarted counterexample, recursive completion")

end ProofNetIR.Figure7EnablednessTests

#print axioms ProofNetIR.SequentialFigure7.figure7Enabledness_started_and_sequentialize
#print axioms ProofNetIR.SequentialFigure7.priorityEnabled_not_allReachable

def main : IO Unit := ProofNetIR.Figure7EnablednessTests.smoke
