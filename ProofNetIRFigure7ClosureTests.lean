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


-- Preservation through the six typed rules, entered through the exact dispatcher witness.
example {cert : Certificate} {before after : ReservationState} (step : ConclStep cert before after)
    (structural : cert.StructurallyWellFormed) (closure : RegionClosure cert before.stack) :
    RegionClosure cert after.stack :=
  step.regionClosure structural closure

example {cert : Certificate} {before after : ReservationState} (step : NopStep cert before after)
    (structural : cert.StructurallyWellFormed) (closure : RegionClosure cert before.stack) :
    RegionClosure cert after.stack :=
  step.regionClosure structural closure

example {cert : Certificate} {before after : ReservationState} (step : WaitStep cert before after)
    (structural : cert.StructurallyWellFormed) (closure : RegionClosure cert before.stack) :
    RegionClosure cert after.stack :=
  step.regionClosure structural closure

example {cert : Certificate} {before after : ReservationState} (step : ForwardStep cert before after)
    (structural : cert.StructurallyWellFormed) (closure : RegionClosure cert before.stack) :
    RegionClosure cert after.stack :=
  step.regionClosure structural closure

example {cert : Certificate} {before after : ReservationState} (step : NewStep cert before after)
    (structural : cert.StructurallyWellFormed) (closure : RegionClosure cert before.stack) :
    RegionClosure cert after.stack :=
  step.regionClosure structural closure

example {cert : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep cert before after)
    (structural : cert.StructurallyWellFormed) (closure : RegionClosure cert before.stack) :
    RegionClosure cert after.stack :=
  step.regionClosure structural closure

example {cert : Certificate} {before : ReservationState} {invariant : SchedulerInvariant cert before}
    {result : Figure7DispatchResult} (step : DispatchStep cert before invariant result)
    (closure : RegionClosure cert before.stack) : RegionClosure cert result.after.stack :=
  step.regionClosure closure

-- The actual canonical run: initialization, then the nop on the first endpoint.
private theorem initialReachable : ReachableByImplementedDispatcher certificate initial := by
  obtain ⟨step⟩ := initializeReservation?_some_iff.mp initialEq
  exact ⟨.init step⟩

example : RegionClosure certificate initial.stack := by
  obtain ⟨step⟩ := initializeReservation?_some_iff.mp initialEq
  exact (ExecutedHistory.init step).regionClosure correct.1

example : RegionClosure certificate initial.stack :=
  initialReachable.regionClosure correct.1

example : ParHeadGuardTailNonconclusion certificate initial :=
  initialReachable.guardedHeadTail correct

-- A nop extension of the initial canonical prefix carries no new tail-law obligation.
example : ∃ (step : InitialReservationStep certificate initial 0) (result : Figure7DispatchResult),
    result.kind = .nop ∧
    ∃ (invariant : SchedulerInvariant certificate initial)
      (dispatch : DispatchStep certificate initial invariant result)
      (evidence : DispatchTagEvidence certificate initial result),
      ((CanonicalTagHistory.later (dispatch := dispatch) (CanonicalTagHistory.init step)
          evidence).ActiveTopDebtTailLaw ↔
        (CanonicalTagHistory.init step).ActiveTopDebtTailLaw) := by
  obtain ⟨step⟩ := initializeReservation?_some_iff.mp initialEq
  let invariant := initializeReservation?_schedulerInvariant correct.1 initialEq
  have kindEq : (dispatch? certificate initial invariant).map Figure7DispatchResult.kind =
      some .nop := by decide +kernel
  cases equation : dispatch? certificate initial invariant with
  | none => rw [equation] at kindEq; cases kindEq
  | some result =>
      rw [equation] at kindEq
      have kind : result.kind = .nop := Option.some.inj kindEq
      obtain ⟨dispatch⟩ := (dispatch?_some_iff invariant).mp equation
      obtain ⟨evidence⟩ := dispatch.tagEvidence
      exact ⟨step, result, kind, invariant, dispatch, evidence,
        CanonicalTagHistory.nopWaitTailLaw_iff _ evidence correct (Or.inl kind)⟩


-- Figure-7 progress (ledger item D3): a started reachable state dispatches or is fully marked.
example : (∃ result : Figure7DispatchResult,
      dispatch? certificate initial (initialReachable.schedulerInvariant correct.1) = some result) ∨
    initial.core.allMarked = true :=
  initialReachable.dispatch_or_allMarked correct (by decide +kernel)

example (drained : ActiveTopDrained initial) : initial.core.allMarked = true :=
  initialReachable.allMarked_of_drained correct drained

example : ∃ step : InitialReservationStep certificate initial 0,
    (∃ result : Figure7DispatchResult,
      dispatch? certificate initial ((ExecutedHistory.init step).schedulerInvariant correct.1) =
        some result) ∨ initial.core.allMarked = true := by
  obtain ⟨step⟩ := initializeReservation?_some_iff.mp initialEq
  exact ⟨step, (CanonicalTagHistory.init step).dispatch_or_allMarked correct (by decide +kernel)⟩

example {cert : Certificate} {state : ReservationState} (closure : RegionClosure cert state.stack)
    (invariant : SchedulerInvariant cert state) (correct : cert.DeclarativelyCorrect)
    {age : SequentialSchedulerState.RawTokenAge}
    (sigmaLast : state.stack.sigma.getLast? = some age) (readyLast : state.stack.ready.getLast? = some [])
    {seed : Vertex} (seedClass : markClass? state.stack seed = some age)
    (seedBound : seed < cert.formulas.size) {vertex : Vertex} (bound : vertex < cert.formulas.size) :
    markClass? state.stack vertex = some age :=
  closure.class_of_empty_active invariant correct sigmaLast readyLast seedClass seedBound bound

end ProofNetIR.Figure7ClosureTests

#print axioms ProofNetIR.SequentialFigure7.boundary_edge_of_correct
#print axioms ProofNetIR.SequentialFigure7.RegionClosure.guardedParHeadTail
#print axioms ProofNetIR.SequentialFigure7.RegionClosure.ofInitialReservation
#print axioms ProofNetIR.SequentialFigure7.ConclStep.regionClosure
#print axioms ProofNetIR.SequentialFigure7.NopStep.regionClosure
#print axioms ProofNetIR.SequentialFigure7.WaitStep.regionClosure
#print axioms ProofNetIR.SequentialFigure7.ForwardStep.regionClosure
#print axioms ProofNetIR.SequentialFigure7.NewStep.regionClosure
#print axioms ProofNetIR.SequentialFigure7.UnifyPayloadStep.regionClosure
#print axioms ProofNetIR.SequentialFigure7.DispatchStep.regionClosure
#print axioms ProofNetIR.SequentialFigure7.ExecutedHistory.regionClosure
#print axioms ProofNetIR.SequentialFigure7.ReachableByImplementedDispatcher.regionClosure
#print axioms ProofNetIR.SequentialFigure7.ReachableByImplementedDispatcher.guardedHeadTail
#print axioms ProofNetIR.SequentialFigure7.CanonicalTagHistory.nopWaitTailLaw_iff
#print axioms ProofNetIR.SequentialFigure7.RegionClosure.class_of_empty_active
#print axioms ProofNetIR.SequentialFigure7.ReachableByImplementedDispatcher.allMarked_of_drained
#print axioms ProofNetIR.SequentialFigure7.ReachableByImplementedDispatcher.dispatch_or_allMarked
#print axioms ProofNetIR.SequentialFigure7.CanonicalTagHistory.dispatch_or_allMarked

def main : IO Unit :=
  IO.println "Region-closure consumer passed: initialization, C12 from closure, switching boundary, six-rule preservation, reachable C12, nop/wait tail law, D3 progress"
