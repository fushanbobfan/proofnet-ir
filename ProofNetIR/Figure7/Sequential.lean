import ProofNetIR.Figure7.Closure
import ProofNetIR.Figure7.Termination

/-!
# The sequential fast path

`runDispatcher` executes the canonical Figure-7 dispatcher for a bounded
number of calls, threading the scheduler invariant as a proof argument.
`sequentialReconstruct?` initializes at the first conclusion, runs the
dispatcher with the formula-carrier budget, exchanges the final component's
frontier into the public conclusion order, and accepts only a derivation that
passes the independent verifier, so `sequentialFastCheck` is sound by
construction. `runDispatcher_spec` shows that from any started reachable state
of a correct certificate the run ends reachable, fully marked, and unable to
dispatch (ledger items D3 and D4). Completeness of `sequentialFastCheck`
(ledger item D1) is not proved here: initialization totality at the first
conclusion and the verification of the final component's derivation remain
open.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerBridge

/-- Execute at most `fuel` canonical dispatches, stopping at the first failed call.
The invariant argument is proof-only and is threaded through successful steps. -/
def runDispatcher (certificate : Certificate) : (fuel : Nat) →
    (state : ReservationState) → SchedulerInvariant certificate state → ReservationState
  | 0, state, _ => state
  | fuel + 1, state, invariant =>
      match equation : dispatch? certificate state invariant with
      | none => state
      | some result => runDispatcher certificate fuel result.after
          (dispatch?_schedulerInvariant invariant equation)

private theorem run_invariant {certificate : Certificate} (fuel : Nat)
    (state : ReservationState) (invariant : SchedulerInvariant certificate state) :
    SchedulerInvariant certificate (runDispatcher certificate fuel state invariant) := by
  induction fuel generalizing state with
  | zero => exact invariant
  | succ fuel ih =>
      unfold runDispatcher
      split
      · exact invariant
      · exact ih _ _

private theorem run_reachable {certificate : Certificate} (fuel : Nat)
    (state : ReservationState) (invariant : SchedulerInvariant certificate state)
    (reachable : ReachableByImplementedDispatcher certificate state) :
    ReachableByImplementedDispatcher certificate
      (runDispatcher certificate fuel state invariant) := by
  induction fuel generalizing state with
  | zero => exact reachable
  | succ fuel ih =>
      unfold runDispatcher
      split
      · exact reachable
      · rename_i result equation
        exact ih _ _ (reachable.dispatch invariant equation)

private def DispatcherStopped (certificate : Certificate) (state : ReservationState) : Prop :=
  ∃ invariant : SchedulerInvariant certificate state, dispatch? certificate state invariant = none

private theorem run_stopped {certificate : Certificate} (fuel : Nat)
    (state : ReservationState) (invariant : SchedulerInvariant certificate state)
    (budget : certificate.formulas.size < dispatchMeasure state + fuel) :
    DispatcherStopped certificate (runDispatcher certificate fuel state invariant) := by
  induction fuel generalizing state with
  | zero =>
      have := dispatchMeasure_le invariant
      omega
  | succ fuel ih =>
      simp only [runDispatcher]
      split
      · exact ⟨invariant, by assumption⟩
      · rename_i result equation
        have nextInvariant := dispatch?_schedulerInvariant invariant equation
        obtain ⟨step⟩ := (dispatch?_some_iff invariant).mp equation
        have increase := step.measure_eq
        exact ih result.after nextInvariant (by omega)

private theorem run_started {certificate : Certificate} (fuel : Nat)
    (state : ReservationState) (invariant : SchedulerInvariant certificate state)
    (started : 0 < state.stack.nextAge) :
    0 < (runDispatcher certificate fuel state invariant).stack.nextAge := by
  induction fuel generalizing state with
  | zero => exact started
  | succ fuel ih =>
      unfold runDispatcher
      split
      · exact started
      · rename_i result equation
        obtain ⟨step⟩ := (dispatch?_some_iff invariant).mp equation
        obtain ⟨evidence⟩ := step.tagEvidence
        have count := evidence.linkIndices_length_add_nextAge
        exact ih result.after _ (Nat.lt_of_lt_of_le started (by omega))

/-- From any started reachable state of a correct certificate, the carrier-sized
run ends at a reachable, invariant, fully marked state where dispatch fails. -/
theorem runDispatcher_spec {certificate : Certificate} {state : ReservationState}
    (invariant : SchedulerInvariant certificate state)
    (reachable : ReachableByImplementedDispatcher certificate state)
    (correct : certificate.DeclarativelyCorrect) (started : 0 < state.stack.nextAge) :
    let final := runDispatcher certificate (certificate.formulas.size + 1) state invariant
    ReachableByImplementedDispatcher certificate final ∧
      ∃ finalInvariant : SchedulerInvariant certificate final,
        dispatch? certificate final finalInvariant = none ∧ final.core.allMarked = true := by
  dsimp only
  have finalReachable := run_reachable (certificate.formulas.size + 1) state invariant reachable
  obtain ⟨finalInvariant, stopped⟩ :=
    run_stopped (certificate.formulas.size + 1) state invariant (by omega)
  have finalStarted := run_started (certificate.formulas.size + 1) state invariant started
  refine ⟨finalReachable, finalInvariant, stopped, ?_⟩
  rcases finalReachable.dispatch_or_allMarked correct finalStarted with succeeds | marked
  · obtain ⟨result, equation⟩ := succeeds
    rw [stopped] at equation
    cases equation
  · exact marked

end SequentialFigure7

namespace Certificate

open SequentialSchedulerBridge SequentialFigure7

private def occurrenceOrder? (source : List Vertex) : List Vertex → Option (List Nat)
  | [] => some []
  | vertex :: rest => do
      let index ← source.findIdx? (· == vertex)
      let tail ← occurrenceOrder? source rest
      pure (index :: tail)

private def sequentialFinalTree? (certificate : Certificate)
    (state : ReservationState) : Option CutFreeDerivation := do
  let [component] := state.core.liveComponents | none
  guard (component.frontier.length = certificate.conclusions.length)
  let order ← occurrenceOrder? component.frontier certificate.conclusions
  guard (order.eraseDups.length = order.length)
  pure (.exchange order component.tree)

/-- Initialize at the first conclusion, run the canonical dispatcher with the
formula-carrier budget, and independently verify the exchanged final component.
No switching enumeration or recursive reconstruction fallback is executed. -/
def sequentialReconstruct? (certificate : Certificate) :
    Option (DerivationVerificationResult certificate) :=
  if wellFormed : certificate.wellFormed = true then do
    let start ← certificate.conclusions.head?
    match equation : initializeReservation? certificate start with
    | none => none
    | some state =>
        let invariant := initializeReservation?_schedulerInvariant
          (certificate.wellFormed_iff_structurallyWellFormed.mp wellFormed) equation
        let final := runDispatcher certificate (certificate.formulas.size + 1) state invariant
        let tree ← sequentialFinalTree? certificate final
        certificate.verifyDerivation? tree
  else none

/-- Boolean acceptance of the sequential proof-bearing reconstruction. -/
def sequentialFastCheck (certificate : Certificate) : Bool :=
  certificate.sequentialReconstruct?.isSome

/-- Every accepted sequential candidate is accepted by the reference checker. -/
theorem sequentialFastCheck_sound (certificate : Certificate)
    (accepted : certificate.sequentialFastCheck = true) : certificate.check = true := by
  unfold sequentialFastCheck at accepted
  cases equation : certificate.sequentialReconstruct? with
  | none => simp [equation] at accepted
  | some result =>
      rw [← result.equivalent.check_eq]
      exact result.outputAccepted

end Certificate
end ProofNetIR
