import ProofNetIR.Figure7.Closure
import ProofNetIR.ExecutableSequentialization

/-!
# Reachable enabledness and initialization

The shallow `new` guard is sufficient on reachable states of a correct
certificate. Among reachable states that are not fully marked, a priority
branch exists exactly when initialization has occurred. The empty scheduler
of a single axiom refutes enabledness without that initialization condition.
The completion conjunct concerns the existing recursive sequentialization API.
-/

namespace ProofNetIR.SequentialFigure7

open SequentialSchedulerBridge

private theorem priority_started
    {certificate : Certificate} {state : ReservationState}
    {invariant : SchedulerInvariant certificate state} {kind : Figure7RuleKind}
    (enabled : PriorityEnabled certificate state invariant kind) :
    0 < state.stack.nextAge := by
  obtain ⟨after, equation⟩ :=
    (dispatch?_kind_success_iff_priorityEnabled invariant kind).mpr enabled
  obtain ⟨step⟩ := (dispatch?_some_iff invariant).mp equation
  obtain ⟨evidence⟩ := step.tagEvidence
  have head := evidence.prepared.readyHeadInput
  have bound := invariant.stack_wellShaped.sigma_partition.boundary_lt
    head.rawAge (List.mem_of_getLast? head.sigma_top)
  exact Nat.lt_of_le_of_lt (Nat.zero_le _) bound

/-- Reachable `new` guards suffice; a reachable, not fully marked state has a
priority branch exactly when started; the recursive sequentializer succeeds
on every accepted certificate. -/
theorem figure7Enabledness_started_and_sequentialize :
    (∀ {certificate state},
      ReachableByImplementedDispatcher certificate state →
      certificate.DeclarativelyCorrect →
      NewGuard certificate state → NewEnabled certificate state) ∧
    (∀ {certificate state}
      (reachable : ReachableByImplementedDispatcher certificate state)
      (correct : certificate.DeclarativelyCorrect),
      let invariant := reachable.schedulerInvariant correct.1
      state.core.allMarked ≠ true →
        ((∃ kind, PriorityEnabled certificate state invariant kind) ↔
          0 < state.stack.nextAge)) ∧
    (∀ certificate : Certificate, certificate.check = true →
      ∃ result : ExecutableSequentializationResult certificate,
        certificate.sequentialize = .ok result) := by
  refine ⟨?_, ?_, Certificate.sequentialize_complete⟩
  · rintro certificate state ⟨history⟩ correct guard
    obtain ⟨tagHistory⟩ := history.hasCanonicalTagHistory
    exact tagHistory.active_newEnabled correct (history.schedulerInvariant correct.1) guard
  · intro certificate state reachable correct invariant notMarked
    constructor
    · rintro ⟨kind, enabled⟩
      exact priority_started enabled
    · intro started
      rcases reachable.dispatch_or_allMarked correct started with dispatch | marked
      · obtain ⟨result, equation⟩ := dispatch
        exact ⟨result.kind,
          (dispatch?_kind_success_iff_priorityEnabled invariant result.kind).mp
            ⟨result.after, equation⟩⟩
      · exact (notMarked marked).elim

private def unstartedAxiom : Certificate where
  formulas := #[.atom "p" true, .atom "p" false]
  links := [.axiom 0 1]
  conclusions := [0, 1]

private theorem unstartedAxiom_correct : unstartedAxiom.DeclarativelyCorrect :=
  unstartedAxiom.check_iff_declarativelyCorrect.mp (by decide +kernel)

/-- The unrestricted enabledness conjunct is false: the reachable empty
scheduler of one correct axiom is not fully marked and cannot dispatch. -/
theorem priorityEnabled_not_allReachable :
    ¬ (∀ {certificate state}
      (reachable : ReachableByImplementedDispatcher certificate state)
      (correct : certificate.DeclarativelyCorrect),
      let invariant := reachable.schedulerInvariant correct.1
      state.core.allMarked ≠ true →
        ∃ kind, PriorityEnabled certificate state invariant kind) := by
  intro enabled
  let reachable := dispatcher_reachable_empty unstartedAxiom
  obtain ⟨kind, branch⟩ := enabled reachable unstartedAxiom_correct (by decide +kernel)
  have stopped : dispatch? unstartedAxiom (ReservationState.empty unstartedAxiom)
      (reachable.schedulerInvariant unstartedAxiom_correct.1) = none := by decide +kernel
  exact (dispatch?_eq_none_iff_forall_not_priorityEnabled _).mp stopped kind branch

end ProofNetIR.SequentialFigure7
