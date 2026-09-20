import ProofNetIR.SequentialFigure7ActiveTopDebtHistoryTail
import ProofNetIR.SequentialFigure7ActiveTopDebtParentEscape

/-!
# Guarded par-head tails

C12 asks for a non-conclusion behind an active par premise whose mate is
unmarked or has a smaller raw age. Initialization establishes this condition.
The `nop` and `wait` tail obligations follow from C12 on their pre-state.
A certified counterexample refutes state-only preservation; its pre-state is
canonically unreachable. Preservation along canonical histories remains open.
-/

namespace ProofNetIR.SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge

/-- A guarded active par head leaves a non-conclusion in its ready tail. -/
def ParHeadGuardTailNonconclusion (certificate : Certificate) (state : ReservationState) : Prop :=
  ∀ {age : RawTokenAge} {head : Vertex} {rest : List Vertex}
    (consumer : ConnectiveBelow certificate head),
    state.stack.sigma.getLast? = some age →
    state.stack.ready.getLast? = some (head :: rest) →
    consumer.kind = .par →
    (state.core.marks[consumer.mate]? = some none ∨
      ∃ mateAge, state.core.marks[consumer.mate]? = some (some mateAge) ∧ mateAge < age) →
    ∃ pending, pending ∈ rest ∧ pending ∉ certificate.conclusions

private theorem empty_parHeadGuardTail (certificate : Certificate) :
    ParHeadGuardTailNonconclusion certificate (ReservationState.empty certificate) := by
  intro age head rest consumer sigmaTop
  simp [ReservationState.empty, SequentialStackState.empty] at sigmaTop

private theorem parHeadGuardTail_of_no_marked_frontier
    {certificate : Certificate} {state : ReservationState}
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate state)
    (absent : ¬ ActiveTopMarkedNonconclusionPresent certificate state) :
    ParHeadGuardTailNonconclusion certificate state := by
  intro age head rest consumer sigmaTop readyTop parEq _guard
  let input : ReadyHeadInput state := ⟨head, rest, age, readyTop, sigmaTop⟩
  rcases input.readyTail_nonconclusion_or_parentEscape correct invariant consumer parEq with
    ⟨component, _used, _owned, lookup, _occurrence, _accounted, tail | escape⟩
  · exact tail
  · rcases escape with
      ⟨premise, markedAge, _index, _kind, _left, _right, _conclusion,
        _different, frontier, marked, notGlobal, _submitted, _premise, _outside⟩
    exact (absent ⟨age, markedAge, component, premise, sigmaTop, lookup,
      frontier, marked, notGlobal⟩).elim

/-- On a correct certificate, an initial axiom bucket satisfies C12. -/
theorem InitialReservationStep.parHeadGuardTail
    {certificate : Certificate} {after : ReservationState} {start : Vertex}
    (step : InitialReservationStep certificate after start)
    (correct : certificate.DeclarativelyCorrect) :
    ParHeadGuardTailNonconclusion certificate after := by
  apply parHeadGuardTail_of_no_marked_frontier correct (step.schedulerInvariant correct.1)
  rintro ⟨_age, markedAge, _component, vertex, _sigma, _lookup, _frontier, marked, _notGlobal⟩
  rcases certificate.reserveAxiomAt?_exact step.core_eq with
    ⟨_left, _right, _fresh, _link, _ready, _lookup, _frontier,
      marksEq, _parents, _components, _started, _fired⟩
  rw [step.output_eq] at marked
  change step.coreAfter.marks[vertex]? = some (some markedAge) at marked
  rw [marksEq] at marked
  change (Array.replicate certificate.formulas.size none)[vertex]? =
    some (some markedAge) at marked
  rw [Array.getElem?_replicate] at marked
  split at marked <;> simp at marked

/-- C12 on the pre-state discharges the exact `nop` remaining-top obligation. -/
theorem NopStep.tailNonconclusion_of_parHeadGuard
    {certificate : Certificate} {before after : ReservationState}
    (step : NopStep certificate before after)
    (guardTail : ParHeadGuardTailNonconclusion certificate before) :
    ∃ pending, pending ∈ step.prepared.stackResult.remainingTop ∧
      pending ∉ certificate.conclusions := by
  have popped := popReadyMark?_exact step.prepared.stack_eq
  exact guardTail step.consumer popped.2.1 popped.1 step.par_eq
    (Or.inl step.mate_unmarked_before)

/-- C12 uses precisely the active raw age compared by the `wait` guard. -/
theorem WaitStep.tailNonconclusion_of_parHeadGuard
    {certificate : Certificate} {before after : ReservationState}
    (step : WaitStep certificate before after)
    (guardTail : ParHeadGuardTailNonconclusion certificate before) :
    ∃ pending, pending ∈ step.prepared.stackResult.remainingTop ∧
      pending ∉ certificate.conclusions := by
  have popped := popReadyMark?_exact step.prepared.stack_eq
  exact guardTail step.consumer popped.2.1 popped.1 step.par_eq
    (Or.inr ⟨step.mateRawAge, step.mate_marked_before, step.younger⟩)


namespace TailCounterexample

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

private def cert : Certificate where
  formulas := #[.atom "a" true, .atom "a" false,
    .atom "b" true, .atom "b" false, .atom "c" true, .atom "c" false,
    .tensor (.atom "b" true) (.atom "c" true),
    .tensor (.atom "b" false) (.atom "a" true),
    .par (.tensor (.atom "b" true) (.atom "c" true)) (.atom "a" false),
    .par (.atom "c" false) (.tensor (.atom "b" false) (.atom "a" true))]
  links := [.axiom 0 1, .axiom 2 3, .axiom 4 5, .tensor 2 4 6,
    .tensor 3 0 7, .par 6 1 8, .par 5 7 9]
  conclusions := [8, 9]

private theorem correct : cert.DeclarativelyCorrect :=
  cert.check_iff_declarativelyCorrect.mp (by decide +kernel)

private def initial := (initializeReservation? cert 4).getD (ReservationState.empty cert)
private theorem initialEq : initializeReservation? cert 4 = some initial := by decide +kernel
private theorem initialInv : SchedulerInvariant cert initial :=
  initializeReservation?_schedulerInvariant correct.1 initialEq
private def first := (dispatch? cert initial initialInv).getD ⟨.concl, initial⟩
private theorem firstEq : dispatch? cert initial initialInv = some first := by decide +kernel
private theorem firstInv : SchedulerInvariant cert first.after :=
  dispatch?_schedulerInvariant initialInv firstEq
private def second := (dispatch? cert first.after firstInv).getD ⟨.concl, first.after⟩
private theorem secondEq : dispatch? cert first.after firstInv = some second := by decide +kernel
private theorem secondInv : SchedulerInvariant cert second.after :=
  dispatch?_schedulerInvariant firstInv secondEq


private def reordered : ReservationState :=
  { second.after with stack := { second.after.stack with ready := [[3, 6, 5]] } }

private theorem reorderedInv : SchedulerInvariant cert reordered := by
  have inv := secondInv
  refine { inv with
    stack_wellShaped := ?_
    stack_operationalWaitingDomain := ?_
    realizesSigma := ?_
    ready_bucket_frontier_exact := ?_
    queued_vertices_nodup := ?_
    queued_vertices_unmarked := ?_
    pending_premises_covered_except_ready := ?_ }
  · exact { inv.stack_wellShaped with
      ready_aligned := by decide +kernel
      ready_nodup := by decide +kernel
      ready_in_bounds := by decide +kernel }
  · exact { inv.stack_operationalWaitingDomain with }
  · exact { inv.realizesSigma with }
  · intro position boundary bucket sigmaLookup readyLookup
    have sigma : reordered.stack.sigma = [0] := by decide +kernel
    rw [sigma] at sigmaLookup
    cases position with
    | zero =>
      have boundaryEq : boundary = 0 := by simpa using sigmaLookup.symm
      subst boundary
      have bucketEq : bucket = [3, 6, 5] := by simpa [reordered] using readyLookup.symm
      subst bucket
      obtain ⟨component, lookup, membership⟩ := inv.ready_bucket_frontier_exact
        (position := 0) (boundary := 0) (bucket := [6, 5, 3])
        (by decide +kernel) (by decide +kernel)
      refine ⟨component, lookup, ?_⟩
      intro vertex
      change vertex ∈ [3, 6, 5] ↔ vertex ∈ component.frontier ∧
        second.after.core.marks[vertex]? = some none
      rw [← membership vertex]
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      grind
    | succ position => simp at sigmaLookup
  · unfold QueuedVerticesNodup; decide +kernel
  · unfold QueuedVerticesUnmarked; decide +kernel
  · intro link member
    have old := inv.pending_premises_covered_except_ready member
    cases link with
    | «axiom» left right => trivial
    | par left right conclusion =>
      intro raw absent
      apply old raw
      simpa [reordered, show second.after.stack.ready = [[6, 5, 3]] from by decide +kernel,
        or_comm, or_left_comm, and_assoc] using absent
    | tensor left right conclusion =>
      intro raw absent
      apply old raw
      simpa [reordered, show second.after.stack.ready = [[6, 5, 3]] from by decide +kernel,
        or_comm, or_left_comm, and_assoc] using absent

private def prepared : PreparedStep reordered := (prepare? reordered).get (by decide +kernel)
private def before := prepared.after
private theorem beforeInv : SchedulerInvariant cert before :=
  prepared.schedulerInvariant reorderedInv
private def result := (dispatch? cert before beforeInv).getD ⟨.concl, before⟩
private theorem resultEq : dispatch? cert before beforeInv = some result := by decide +kernel

private theorem beforeC12 : ParHeadGuardTailNonconclusion cert before := by
  intro age head rest consumer _sigma ready _par _guard
  have readyEq : before.stack.ready = [[6, 5]] := by decide +kernel
  rw [readyEq] at ready
  have shape : head = 6 ∧ rest = [5] := by simpa using ready.symm
  rcases shape with ⟨rfl, rfl⟩
  exact ⟨5, by decide, by decide⟩

private theorem afterNotC12 : ¬ ParHeadGuardTailNonconclusion cert result.after := by
  intro law
  let consumer := (cert.connectiveBelow? 5).get (by decide +kernel)
  have tail := law (age := 0) (head := 5) (rest := []) consumer
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (Or.inl (by decide +kernel))
  simp at tail

private structure Snapshot where
  state : ReservationState
  invariant : SchedulerInvariant cert state

private def fromStart (start : Nat) : Option Snapshot :=
  match eq : initializeReservation? cert start with
  | none => none
  | some state => some ⟨state, initializeReservation?_schedulerInvariant correct.1 eq⟩

private def trace : Nat → Snapshot → List Snapshot
  | 0, snapshot => [snapshot]
  | fuel + 1, snapshot => snapshot ::
    match eq : dispatch? cert snapshot.state snapshot.invariant with
    | none => []
    | some next => trace fuel ⟨next.after, dispatch?_schedulerInvariant snapshot.invariant eq⟩

private def snapshots : List Snapshot :=
  ⟨ReservationState.empty cert, empty_schedulerInvariant correct.1⟩ ::
    ((List.range 10).filterMap fromStart).flatMap (trace 10)

private def states := snapshots.map Snapshot.state

private theorem closed : ∀ snapshot ∈ snapshots,
    match dispatch? cert snapshot.state snapshot.invariant with
    | none => True
    | some next => next.after ∈ states := by
  have verified : snapshots.all (fun snapshot ↦
      match dispatch? cert snapshot.state snapshot.invariant with
      | none => true
      | some next => states.contains next.after) = true := by decide +kernel
  intro snapshot member
  have checked := List.all_eq_true.mp verified snapshot member
  cases eq : dispatch? cert snapshot.state snapshot.invariant with
  | none => trivial
  | some next => simpa [eq] using checked

private theorem initCovered : ∀ start ∈ List.range 10,
    match initializeReservation? cert start with
    | none => True
    | some state => state ∈ states := by
  have verified : (List.range 10).all (fun start ↦
      match initializeReservation? cert start with
      | none => true
      | some state => states.contains state) = true := by decide +kernel
  intro start member
  have checked := List.all_eq_true.mp verified start member
  cases eq : initializeReservation? cert start with
  | none => trivial
  | some state => simpa [eq] using checked

private theorem reachableCovered {state : ReservationState}
    (history : ExecutedHistory cert state) : state ∈ states := by
  induction history with
  | empty => exact List.mem_cons_self
  | @init after start step =>
    have raw := SequentialUnification.nextAxiom?_startReady step.search_eq
    have bound : start < 10 := by
      have := (Array.getElem?_eq_some_iff.mp raw).1
      exact this
    have equation := initializeReservation?_some_iff.mpr ⟨step⟩
    have covered := initCovered start (List.mem_range.mpr bound)
    rw [equation] at covered
    exact covered
  | @later before next prior invariant step ih =>
    obtain ⟨snapshot, member, same⟩ := List.mem_map.mp ih
    have nextEq := (dispatch?_some_iff invariant).mpr ⟨step⟩
    have covered := closed snapshot member
    have snapshotEq : snapshot.state = before := same
    cases snapshot with
    | mk snapState snapInv =>
      dsimp at snapshotEq
      subst snapState
      rw [nextEq] at covered
      exact covered

private theorem beforeUnreachable : ¬ ReachableByImplementedDispatcher cert before := by
  rintro ⟨history⟩
  have excluded : before ∉ states := by decide +kernel
  exact excluded (reachableCovered history)

end TailCounterexample

open TailCounterexample in
/-- C12 and the scheduler invariant do not suffice for one-step preservation,
 even on a correct certificate and a canonical `nop` call. The exhibited
 pre-state is proved unreachable by the implemented dispatcher. -/
theorem parHeadGuardTail_not_inductive :
    ∃ (certificate : Certificate) (before after : ReservationState)
    (invariant : SchedulerInvariant certificate before),
    certificate.DeclarativelyCorrect ∧
    ParHeadGuardTailNonconclusion certificate before ∧
    Nonempty (DispatchStep certificate before invariant ⟨.nop, after⟩) ∧
    ¬ ParHeadGuardTailNonconclusion certificate after ∧
    ¬ ReachableByImplementedDispatcher certificate before := by
  refine ⟨cert, before, result.after, beforeInv, correct, beforeC12, ?_,
    afterNotC12, beforeUnreachable⟩
  apply (dispatch?_some_iff beforeInv).mp
  decide +kernel

end ProofNetIR.SequentialFigure7
