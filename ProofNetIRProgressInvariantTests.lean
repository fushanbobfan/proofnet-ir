import ProofNetIR.SequentialFigure7ProgressInvariant
import ProofNetIR.SequentialFigure7NewEnabled

namespace ProofNetIR

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge

namespace ProgressInvariantTests

private def axiomCertificate : Certificate where
  formulas := #[.atom "p" true, .atom "p" false]
  links := [.axiom 0 1]
  conclusions := [0, 1]

private theorem axiomCertificate_structural :
    axiomCertificate.StructurallyWellFormed := by
  exact
    (Certificate.wellFormed_iff_structurallyWellFormed
      axiomCertificate).mp (by native_decide)

/-- A state that differs from the exact empty state only by forging one
future waiting cell as initialized-empty. -/
private def forgedFutureWaitingState : ReservationState where
  stack := {
    marks := #[none, none]
    nextAge := 0
    sigma := []
    ready := []
    waiting := #[.initialized [], .undefined] }
  core := axiomCertificate.initialUnificationState
  tags := #[false, false]

private theorem forgedFutureWaitingState_reservationInvariant :
    ReservationInvariant axiomCertificate forgedFutureWaitingState := by
  refine {
    stack_wellShaped := ?_
    stack_operationalWaitingDomain := ?_
    realizesSigma := ?_
    core_orderedParents :=
      Certificate.initialUnificationState_orderedParents axiomCertificate
    core_abstractable :=
      Certificate.initialUnificationState_abstractable axiomCertificate
    core_componentsFormulaConsistent :=
      Certificate.initialUnificationState_componentsFormulaConsistent
        axiomCertificate
    core_carriers_aligned :=
      Certificate.initialUnificationState_componentsParentsAligned
        axiomCertificate
    core_counter_aligned := rfl
    tags_size := by native_decide }
  · exact {
      marks_size := by native_decide
      waiting_size := by native_decide
      assigned_age_bound := by
        intro vertex age lookup
        have vertexBound : vertex < 2 :=
          (Array.getElem?_eq_some_iff.mp lookup).1
        cases vertex with
        | zero => simp [forgedFutureWaitingState] at lookup
        | succ vertex =>
            cases vertex with
            | zero => simp [forgedFutureWaitingState] at lookup
            | succ vertex =>
                exact (Nat.not_lt_of_ge
                  (Nat.succ_le_succ
                    (Nat.succ_le_succ (Nat.zero_le vertex)))
                  vertexBound).elim
      sigma_partition := SigmaAgePartition.empty
      ready_aligned := by native_decide
      ready_nodup := by simp [forgedFutureWaitingState]
      ready_in_bounds := by simp [forgedFutureWaitingState]
      nextAge_le_waiting := by native_decide }
  · exact {
      initialized_iff_inactive := by
        intro age ageBound
        simp [forgedFutureWaitingState] at ageBound }
  · exact {
      marks_eq := rfl
      horizon_eq := rfl
      representative_eq_boundary := by
        intro age ageBound
        simp [forgedFutureWaitingState] at ageBound }

private theorem forgedFutureWaitingState_schedulerInvariant :
    SchedulerInvariant axiomCertificate forgedFutureWaitingState := by
  refine {
    toReservationInvariant :=
      forgedFutureWaitingState_reservationInvariant
    structural := axiomCertificate_structural
    component_domain_exact := ?_
    component_forest_provenance :=
      Certificate.initialUnificationState_componentForestProvenance
        axiomCertificate
    live_frontiers_nodup := ?_
    ready_bucket_frontier_exact := ?_
    queued_vertices_nodup := ?_
    queued_vertices_unmarked := ?_
    produced_premises_marked := ?_
    waiting_span_exact := ?_
    pending_premises_covered_except_ready := ?_
    fired_counter_exact := ?_ }
  · intro token
    simp [forgedFutureWaitingState,
      Certificate.initialUnificationState]
  · simp [LiveFrontiersNodup, forgedFutureWaitingState,
      UnificationState.liveFrontierVertices,
      Certificate.initialUnificationState]
  · intro position boundary bucket sigmaLookup
    simp [forgedFutureWaitingState] at sigmaLookup
  · simp [QueuedVerticesNodup, forgedFutureWaitingState,
      SequentialStackState.queuedVertices,
      SequentialStackState.waitingVertices, WaitingCell.vertices]
  · intro vertex membership
    simp [forgedFutureWaitingState,
      SequentialStackState.queuedVertices,
      SequentialStackState.waitingVertices,
      WaitingCell.vertices] at membership
  · intro link membership
    simp [axiomCertificate] at membership
    subst link
    trivial
  · intro boundary payload conclusion waitingLookup conclusionMembership
    have boundaryBound : boundary < 2 :=
      (Array.getElem?_eq_some_iff.mp waitingLookup).1
    cases boundary with
    | zero =>
        simp [forgedFutureWaitingState] at waitingLookup
        subst payload
        simp at conclusionMembership
    | succ boundary =>
        cases boundary with
        | zero => simp [forgedFutureWaitingState] at waitingLookup
        | succ boundary =>
            exact (Nat.not_lt_of_ge
              (Nat.succ_le_succ
                (Nat.succ_le_succ (Nat.zero_le boundary)))
              boundaryBound).elim
  · intro link membership
    simp [axiomCertificate] at membership
    subst link
    trivial
  · rfl

/-- The current `SchedulerInvariant` does not imply clean future waiting
storage.  This is a separation regression, not a reachable-state example. -/
example :
    SchedulerInvariant axiomCertificate forgedFutureWaitingState ∧
      ¬ SequentialFigure7.FutureWaitingUndefined
        forgedFutureWaitingState := by
  refine ⟨forgedFutureWaitingState_schedulerInvariant, ?_⟩
  intro future
  have forgedLookup := future 0 (Nat.zero_le 0) (by native_decide)
  simp [forgedFutureWaitingState] at forgedLookup

private def tensorCertificate : Certificate where
  formulas := #[
    .atom "p" true,
    .atom "p" false,
    .atom "p" true,
    .atom "p" false,
    .tensor (.atom "p" true) (.atom "p" true)]
  links := [
    .axiom 0 1,
    .axiom 2 3,
    .tensor 0 2 4]
  conclusions := [4, 1, 3]

private theorem tensorCertificate_structural :
    tensorCertificate.StructurallyWellFormed := by
  exact
    (Certificate.wellFormed_iff_structurallyWellFormed
      tensorCertificate).mp (by decide)

private def tensorInitial : Option ReservationState :=
  initializeReservation? tensorCertificate 0

private def tensorReadyState : ReservationState :=
  match tensorInitial with
  | some state => state
  | none => ReservationState.empty tensorCertificate

private theorem tensorReadyState_eq :
    tensorInitial = some tensorReadyState := by
  native_decide

private theorem tensorReadyState_schedulerInvariant :
    SchedulerInvariant tensorCertificate tensorReadyState := by
  rcases initializeReservation?_some_iff.mp (by
      simpa [tensorInitial] using tensorReadyState_eq) with
    ⟨step⟩
  exact step.schedulerInvariant tensorCertificate_structural

/-- Forge only the first unallocated waiting cell of a genuine initialized
tensor-ready state.  The payload is empty, so it adds no queued occurrence. -/
private def forgedNewFutureState : ReservationState :=
  { tensorReadyState with
    stack := {
      tensorReadyState.stack with
      waiting :=
        tensorReadyState.stack.waiting.setIfInBounds
          tensorReadyState.stack.nextAge (.initialized []) } }

private theorem forgedNewFutureState_reservationInvariant :
    ReservationInvariant tensorCertificate forgedNewFutureState := by
  let invariant :=
    tensorReadyState_schedulerInvariant.toReservationInvariant
  refine {
    stack_wellShaped := ?_
    stack_operationalWaitingDomain := ?_
    realizesSigma := ?_
    core_orderedParents := by
      intro token parent lookup
      exact invariant.core_orderedParents (by
        simpa [forgedNewFutureState] using lookup)
    core_abstractable := by
      simpa [forgedNewFutureState] using invariant.core_abstractable
    core_componentsFormulaConsistent := by
      intro index component lookup
      exact invariant.core_componentsFormulaConsistent (by
        simpa [forgedNewFutureState] using lookup)
    core_carriers_aligned := by
      simpa [forgedNewFutureState] using invariant.core_carriers_aligned
    core_counter_aligned := by
      simpa [forgedNewFutureState] using invariant.core_counter_aligned
    tags_size := by
      simpa [forgedNewFutureState] using invariant.tags_size }
  · exact {
      marks_size := by
        simpa [forgedNewFutureState] using
          invariant.stack_wellShaped.marks_size
      waiting_size := by
        simpa [forgedNewFutureState] using
          invariant.stack_wellShaped.waiting_size
      assigned_age_bound := by
        intro vertex age lookup
        apply invariant.stack_wellShaped.assigned_age_bound vertex age
        simpa [forgedNewFutureState] using lookup
      sigma_partition := by
        simpa [forgedNewFutureState] using
          invariant.stack_wellShaped.sigma_partition
      ready_aligned := by
        simpa [forgedNewFutureState] using
          invariant.stack_wellShaped.ready_aligned
      ready_nodup := by
        simpa [forgedNewFutureState] using
          invariant.stack_wellShaped.ready_nodup
      ready_in_bounds := by
        simpa [forgedNewFutureState] using
          invariant.stack_wellShaped.ready_in_bounds
      nextAge_le_waiting := by
        simpa [forgedNewFutureState] using
          invariant.stack_wellShaped.nextAge_le_waiting }
  · refine {
      initialized_iff_inactive := ?_ }
    intro age ageBound
    have oldAgeBound : age < tensorReadyState.stack.nextAge := by
      simpa [forgedNewFutureState] using ageBound
    have indexNeAge : tensorReadyState.stack.nextAge ≠ age :=
      (Nat.ne_of_lt oldAgeBound).symm
    have waitingLookup :
        forgedNewFutureState.stack.waiting[age]? =
          tensorReadyState.stack.waiting[age]? := by
      simpa [forgedNewFutureState] using
        Array.getElem?_setIfInBounds_ne indexNeAge
    unfold WaitingInitializedAt
    rw [waitingLookup]
    have oldDomain :=
      invariant.stack_operationalWaitingDomain.initialized_iff_inactive
        oldAgeBound
    unfold WaitingInitializedAt at oldDomain
    simpa [forgedNewFutureState] using oldDomain
  · exact {
      marks_eq := by
        simpa [forgedNewFutureState] using invariant.realizesSigma.marks_eq
      horizon_eq := by
        simpa [forgedNewFutureState] using invariant.realizesSigma.horizon_eq
      representative_eq_boundary := by
        intro age ageBound
        have oldAgeBound : age < tensorReadyState.stack.nextAge := by
          simpa [forgedNewFutureState] using ageBound
        simpa [forgedNewFutureState] using
          invariant.realizesSigma.representative_eq_boundary oldAgeBound }

private theorem forgedNewFutureState_queuedVertices :
    forgedNewFutureState.stack.queuedVertices =
      tensorReadyState.stack.queuedVertices := by
  native_decide

private theorem forgedNewFutureState_schedulerInvariant :
    SchedulerInvariant tensorCertificate forgedNewFutureState := by
  let invariant := tensorReadyState_schedulerInvariant
  refine {
    toReservationInvariant := forgedNewFutureState_reservationInvariant
    structural := tensorCertificate_structural
    component_domain_exact := by
      simpa [ComponentDomainExact, forgedNewFutureState] using
        invariant.component_domain_exact
    component_forest_provenance := by
      simpa [forgedNewFutureState] using
        invariant.component_forest_provenance
    live_frontiers_nodup := by
      simpa [LiveFrontiersNodup, forgedNewFutureState] using
        invariant.live_frontiers_nodup
    ready_bucket_frontier_exact := by
      intro position boundary bucket sigmaLookup readyLookup
      apply invariant.ready_bucket_frontier_exact
      · simpa [forgedNewFutureState] using sigmaLookup
      · simpa [forgedNewFutureState] using readyLookup
    queued_vertices_nodup := by
      rw [QueuedVerticesNodup, forgedNewFutureState_queuedVertices]
      exact invariant.queued_vertices_nodup
    queued_vertices_unmarked := by
      intro vertex membership
      apply invariant.queued_vertices_unmarked vertex
      rw [← forgedNewFutureState_queuedVertices]
      exact membership
    produced_premises_marked := by
      intro link membership
      simpa [Produced, forgedNewFutureState] using
        invariant.produced_premises_marked membership
    waiting_span_exact := ?_
    pending_premises_covered_except_ready := by
      intro link membership
      simpa [forgedNewFutureState] using
        invariant.pending_premises_covered_except_ready membership
    fired_counter_exact := by
      simpa [FiredCounterExact, forgedNewFutureState] using
        invariant.fired_counter_exact }
  intro boundary payload conclusion waitingLookup conclusionMembership
  by_cases same : boundary = tensorReadyState.stack.nextAge
  · subst boundary
    have exactLookup :
        forgedNewFutureState.stack.waiting[
            tensorReadyState.stack.nextAge]? =
          some (.initialized []) := by
      native_decide
    have cellEquation :
        WaitingCell.initialized ([] : List Vertex) =
          .initialized payload :=
      Option.some.inj (exactLookup.symm.trans waitingLookup)
    have payloadEquation : ([] : List Vertex) = payload :=
      WaitingCell.initialized.inj cellEquation
    subst payload
    simp at conclusionMembership
  · have waitingLookupEq :
        forgedNewFutureState.stack.waiting[boundary]? =
          tensorReadyState.stack.waiting[boundary]? := by
      simpa [forgedNewFutureState] using
        Array.getElem?_setIfInBounds_ne (Ne.symm same)
    rw [waitingLookupEq] at waitingLookup
    exact invariant.waiting_span_exact waitingLookup conclusionMembership

private def forgedNewHead :
    SequentialFigure7.ReadyHeadInput forgedNewFutureState where
  vertex := 0
  readyTail := [1]
  rawAge := 0
  top_ready := by native_decide
  sigma_top := by native_decide

private def forgedNewTensor : TensorBelow where
  linkIndex := 2
  storedLeft := 0
  storedRight := 2
  conclusion := 4
  side := .storedLeft

private theorem forgedNewTensor_eq :
    tensorCertificate.tensorBelow? forgedNewHead.vertex =
      some forgedNewTensor := by
  decide

private theorem forgedNewTensor_mate_unmarked :
    forgedNewFutureState.core.marks[forgedNewTensor.mate]? = some none := by
  native_decide

private def forgedNewGuard :
    SequentialFigure7.NewGuard tensorCertificate forgedNewFutureState where
  head := forgedNewHead
  tensor := forgedNewTensor
  tensor_valid :=
    Certificate.tensorBelow?_eq_some_iff.mp forgedNewTensor_eq
  mate_unmarked := forgedNewTensor_mate_unmarked

private theorem forgedNewRun :
    Nonempty
      (SequentialUnification.FreshSourceLeftRun tensorCertificate
        forgedNewGuard.head.markedCore tensorCertificate.formulas.size
        forgedNewFutureState.tags forgedNewGuard.tensor.mate [2] 2 3 1) := by
  let source : SequentialUnification.SourceIncidence := {
    linkIndex := 1
    link := .axiom 2 3 }
  have run :
      SequentialUnification.FreshSourceLeftRun tensorCertificate
        forgedNewGuard.head.markedCore tensorCertificate.formulas.size
        forgedNewFutureState.tags forgedNewGuard.tensor.mate [2] 2 3 1 := by
    exact .axiomLeft source (by native_decide) rfl rfl
      (by native_decide) (by decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  exact ⟨run⟩

private theorem forgedNewFutureState_not_operationalReady :
    ¬ OperationalNewReadyAt forgedNewGuard.head.markedStack
      forgedNewGuard.head.rawAge 2 3 := by
  intro ready
  rcases ready with
    ⟨_, _, _, _, _, _, _, _, _, _, _, futureLookup⟩
  change
    forgedNewFutureState.stack.waiting[
        forgedNewFutureState.stack.nextAge]? =
      some .undefined at futureLookup
  have initialized :
      forgedNewFutureState.stack.waiting[
          forgedNewFutureState.stack.nextAge]? =
        some (.initialized []) := by
    native_decide
  rw [initialized] at futureLookup
  simp at futureLookup

private theorem forgedNewFutureState_not_newEnabled :
    ¬ SequentialFigure7.NewEnabled tensorCertificate
      forgedNewFutureState := by
  rintro ⟨input⟩
  rcases input.enqueueReady with
    ⟨_, _, _, _, _, _, _, _, _, _, _, futureLookup⟩
  change
    forgedNewFutureState.stack.waiting[
        forgedNewFutureState.stack.nextAge]? =
      some .undefined at futureLookup
  have initialized :
      forgedNewFutureState.stack.waiting[
          forgedNewFutureState.stack.nextAge]? =
        some (.initialized []) := by
    native_decide
  rw [initialized] at futureLookup
  simp at futureLookup

private theorem forgedNewFutureState_not_futureWaitingUndefined :
    ¬ SequentialFigure7.FutureWaitingUndefined
      forgedNewFutureState := by
  intro future
  have futureLookup := future forgedNewFutureState.stack.nextAge
      (Nat.le_refl _) (by native_decide)
  have initialized :
      forgedNewFutureState.stack.waiting[
          forgedNewFutureState.stack.nextAge]? =
        some (.initialized []) := by
    native_decide
  rw [initialized] at futureLookup
  simp at futureLookup

/-- Fixed executable counterexample to the bare implication from a complete
state invariant, ready head, exact tensor consumer, and raw-unmarked mate to
input-only `new` enabledness.  The closed initialization fixture uses
`native_decide`; this private regression is therefore outside the public
three-axiom theorem boundary.  Only the future waiting cell is forged, and the
state is not claimed reachable. -/
private theorem exists_schedulerInvariant_readyTensorUnmarked_not_newEnabled :
    ∃ (certificate : Certificate) (state : ReservationState)
        (head : SequentialFigure7.ReadyHeadInput state)
        (tensor : TensorBelow),
      SchedulerInvariant certificate state ∧
        certificate.tensorBelow? head.vertex = some tensor ∧
        state.core.marks[tensor.mate]? = some none ∧
        state.stack.waiting[state.stack.nextAge]? =
          some (.initialized []) ∧
        ¬ SequentialFigure7.NewEnabled certificate state ∧
        ¬ SequentialFigure7.FutureWaitingUndefined state := by
  exact ⟨tensorCertificate, forgedNewFutureState, forgedNewHead,
    forgedNewTensor, forgedNewFutureState_schedulerInvariant,
    forgedNewTensor_eq, forgedNewTensor_mate_unmarked, by native_decide,
    forgedNewFutureState_not_newEnabled,
    forgedNewFutureState_not_futureWaitingUndefined⟩

/-- The exact source-left run also survives the future-cell forgery; it is
the operational enqueue guard, specifically its fresh-cell clause, that
fails. -/
private theorem exists_schedulerInvariant_newGuardRun_not_operationalReady :
    ∃ (certificate : Certificate) (state : ReservationState)
        (guard : SequentialFigure7.NewGuard certificate state)
        (trace : List Vertex) (reached partner : Vertex) (linkIndex : Nat),
      SchedulerInvariant certificate state ∧
        Nonempty
          (SequentialUnification.FreshSourceLeftRun certificate
            guard.head.markedCore certificate.formulas.size state.tags
            guard.tensor.mate trace reached partner linkIndex) ∧
        ¬ OperationalNewReadyAt guard.head.markedStack
          guard.head.rawAge reached partner ∧
        ¬ SequentialFigure7.NewEnabled certificate state := by
  exact ⟨tensorCertificate, forgedNewFutureState, forgedNewGuard,
    [2], 2, 3, 1, forgedNewFutureState_schedulerInvariant,
    forgedNewRun, forgedNewFutureState_not_operationalReady,
    forgedNewFutureState_not_newEnabled⟩

end ProgressInvariantTests

end ProofNetIR

def main : IO Unit :=
  IO.println "Figure-7 progress-invariant regressions passed"
