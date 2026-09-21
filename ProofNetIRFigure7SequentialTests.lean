import ProofNetIR.Figure7.Sequential
import ProofNetIR.Figure7.Cost

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

-- The par build numbers its fresh conclusion by the submitted conclusion.
example : ∃ output,
    (CutFreeDerivation.par 0 0 (.axiom "p" true)).build? = some output ∧
      Certificate.OccurrenceBuildMatch certificate output [2] [1, 0] [2, 0, 1] [0, 1, 2] := by
  obtain ⟨fragment, built, matched⟩ := Certificate.occurrenceBuild_axiom_eq correct.1
    (index := 0) (left := 0) (right := 1) (name := "p") (positive := true) rfl rfl
  exact Certificate.occurrenceBuild_par_eq correct.1 built matched (index := 1)
    (afterLeft := [1]) (context := []) rfl rfl rfl

private theorem repeatedCorrect : repeated.DeclarativelyCorrect :=
  repeated.check_iff_declarativelyCorrect.mp (by decide)

-- The tensor build concatenates both numberings and shifts the right fragment.
example : ∃ output,
    (CutFreeDerivation.tensor 0 0 (.axiom "p" true) (.axiom "p" true)).build? = some output ∧
      Certificate.OccurrenceBuildMatch repeated output [4, 1, 3] [2, 0, 1] [4, 0, 1, 2, 3]
        [0, 1, 2, 3, 4] := by
  obtain ⟨leftFragment, leftBuilt, leftMatched⟩ := Certificate.occurrenceBuild_axiom_eq
    repeatedCorrect.1 (index := 0) (left := 0) (right := 1) (name := "p") (positive := true) rfl rfl
  obtain ⟨rightFragment, rightBuilt, rightMatched⟩ := Certificate.occurrenceBuild_axiom_eq
    repeatedCorrect.1 (index := 1) (left := 2) (right := 3) (name := "p") (positive := true) rfl rfl
  exact Certificate.occurrenceBuild_tensor_eq repeatedCorrect.1 leftBuilt leftMatched rightBuilt
    rightMatched (index := 2) (leftContext := [1]) (rightContext := [3]) rfl rfl rfl

-- Every occurrence derivation builds with an exact numbering, and a covering one
-- desequentializes to a proof-net equivalent certificate.
example {cert : Certificate} (structural : cert.StructurallyWellFormed)
    {tree : CutFreeDerivation} {frontier used owned : List Nat}
    (witness : cert.OccurrenceDerivation tree frontier used owned) :
    ∃ fragment numbering, tree.build? = some fragment ∧
      Certificate.OccurrenceBuildMatch cert fragment frontier used owned numbering :=
  Certificate.occurrenceBuild_exists structural witness

example {cert : Certificate} (structural : cert.StructurallyWellFormed)
    {tree : CutFreeDerivation} {used owned : List Nat}
    (witness : cert.OccurrenceDerivation tree cert.conclusions used owned)
    (usedNodup : used.Nodup) (ownedNodup : owned.Nodup)
    (covers : ∀ vertex, vertex ∈ owned ↔ vertex < cert.formulas.size) :
    ∃ output, tree.desequentialize? = some output ∧ output.ProofNetEquivalent cert :=
  Certificate.occurrenceBuild_equivalent structural witness usedNodup ownedNodup covers

-- Completeness: the fast path decides exactly the reference checker.
example (accepted : certificate.check = true) : certificate.sequentialFastCheck = true :=
  certificate.sequentialFastCheck_complete accepted

example (cert : Certificate) : cert.sequentialFastCheck = cert.check :=
  cert.sequentialFastCheck_eq_check

example : rejected.check = false := by
  rw [← rejected.sequentialFastCheck_eq_check]
  native_decide

-- The public decision is the sequential fast path with no fallback (D2).
example (cert : Certificate) : cert.unificationCheck = cert.sequentialFastCheck :=
  cert.unificationCheck_eq_sequentialFastCheck

example (cert : Certificate) : cert.unificationCheck = cert.check :=
  cert.unificationCheck_eq_check

example : certificate.unificationCheck = true := by native_decide

example : rejected.unificationCheck = false := by native_decide

-- The instrumented decision agrees with the public decision and its counters are explicit.
example (cert : Certificate) :
    cert.sequentialDecisionWithStats.accepted = cert.unificationCheck :=
  cert.sequentialDecisionWithStats_accepted

example {cert : Certificate} (fuel : Nat) (state : ReservationState)
    (invariant : SchedulerInvariant cert state) :
    (SequentialCost.runDispatcherWithStats cert fuel state invariant).state =
        runDispatcher cert fuel state invariant ∧
      (SequentialCost.runDispatcherWithStats cert fuel state invariant).calls ≤ fuel :=
  ⟨SequentialCost.runDispatcherWithStats_state cert fuel state invariant,
    SequentialCost.runDispatcherWithStats_calls_le cert fuel state invariant⟩

example : certificate.sequentialDecisionWithStats.accepted = true := by native_decide

example : certificate.sequentialDecisionWithStats.stats.dispatchCalls = 4 := by native_decide

example : rejected.sequentialDecisionWithStats.stats.dispatchCalls = 0 := by native_decide

-- The linear duplicate guard of `forward` and `unifyPayload` decides exactly duplicate freedom.
example (size : Nat) (vertices : List Vertex) :
    SequentialSchedulerState.nodupGuard size vertices = true ↔ vertices.Nodup :=
  SequentialSchedulerState.nodupGuard_eq_true_iff size vertices

example : SequentialSchedulerState.nodupGuard 4 [3, 1, 0] = true := by decide
example : SequentialSchedulerState.nodupGuard 4 [3, 1, 3] = false := by decide
example : SequentialSchedulerState.nodupGuard 2 [7, 1, 7] = false := by decide

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
#print axioms ProofNetIR.Certificate.occurrenceBuild_par_eq
#print axioms ProofNetIR.Certificate.occurrenceBuild_tensor_eq
#print axioms ProofNetIR.Certificate.occurrenceBuild_exists
#print axioms ProofNetIR.Certificate.occurrenceBuild_equivalent
#print axioms ProofNetIR.Certificate.sequentialFastCheck_complete
#print axioms ProofNetIR.Certificate.sequentialFastCheck_eq_check
#print axioms ProofNetIR.Certificate.unificationCheck_eq_sequentialFastCheck
#print axioms ProofNetIR.Certificate.unificationCheck_eq_check
#print axioms ProofNetIR.SequentialSchedulerState.nodupGuard_eq_true_iff
#print axioms ProofNetIR.SequentialCost.runDispatcherWithStats_state
#print axioms ProofNetIR.SequentialCost.runDispatcherWithStats_calls_le
#print axioms ProofNetIR.Certificate.sequentialDecisionWithStats_accepted

def main : IO Unit := do
  let accepted := ProofNetIR.Figure7SequentialTests.certificate.sequentialFastCheck
  let rejected := ProofNetIR.Figure7SequentialTests.rejected.sequentialFastCheck
  let repeated := ProofNetIR.Figure7SequentialTests.repeated.sequentialFastCheck
  let decision := ProofNetIR.Figure7SequentialTests.certificate.unificationCheck
  let run := ProofNetIR.Figure7SequentialTests.repeated.sequentialDecisionWithStats
  unless accepted && !rejected && repeated && decision && run.accepted do
    throw (IO.userError "sequential fast path regression failed")
  IO.println ("Sequential consumer passed: final structure, inference, " ++
    "par/tensor numbering, equivalence, completeness, public decision; " ++
    s!"repeated-label tensor counters: calls {run.stats.dispatchCalls}, " ++
    s!"total {run.stats.total}")
