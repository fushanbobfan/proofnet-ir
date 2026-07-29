import ProofNetIR.SequentialSchedulerState

namespace ProofNetIR

/-!
# Delayed scheduler / production-core bridge

This module connects the independent raw-age `sigma` state to the existing
production unification carrier one reservation at a time.  Reserving an axiom
creates its submitted-orientation component and a fresh self-parent, but it
deliberately does not mark either endpoint.  Endpoint activation belongs to a
later Figure-7 transition.

The relation below is intentionally narrow.  It does not assert that arbitrary
production merges preserve contiguous raw-age intervals, that a link cannot be
reserved twice, or that the complete scheduler is live, complete, or linear.
-/

namespace Certificate

/-- Local precondition for reserving one submitted axiom without activating
its endpoints. -/
def AxiomReservationReady (certificate : Certificate)
    (state : UnificationState) (left right : Vertex) : Prop :=
  certificate.linkLocallyWellFormed (.axiom left right) = true ∧
    state.marks[left]? = some none ∧
    state.marks[right]? = some none ∧
    state.components.size = state.parents.size

instance (certificate : Certificate) (state : UnificationState)
    (left right : Vertex) :
    Decidable (certificate.AxiomReservationReady state left right) := by
  unfold AxiomReservationReady
  infer_instance

private def reservedAxiomState (state : UnificationState)
    (component : UnificationComponent) : UnificationState :=
  let fresh := state.parents.size
  { state with
    parents := state.parents.push fresh
    components := state.components.push (some component)
    startedAxioms := state.startedAxioms + 1 }

/-- Reserve the exact submitted axiom at `linkIndex`.

The submitted endpoint orientation is used for the live component.  Marks and
the connective counter are unchanged; the scheduler's search orientation is
kept separately in its ready bucket. -/
def reserveAxiomAt? (certificate : Certificate)
    (state : UnificationState) (linkIndex : Nat) :
    Option UnificationState := do
  let link ← certificate.links[linkIndex]?
  match link with
  | .axiom left right =>
      if certificate.AxiomReservationReady state left right then
        let component ←
          UnificationComponent.axiom? certificate left right
        some (reservedAxiomState state component)
      else
        none
  | _ => none

/-- Successful reservation exposes the exact submitted axiom, constructor,
local guard, and all changed and unchanged production fields. -/
theorem reserveAxiomAt?_exact
    {certificate : Certificate} {before after : UnificationState}
    {linkIndex : Nat}
    (equation :
      certificate.reserveAxiomAt? before linkIndex = some after) :
    ∃ left right component,
      certificate.links[linkIndex]? = some (.axiom left right) ∧
      certificate.AxiomReservationReady before left right ∧
      UnificationComponent.axiom? certificate left right =
        some component ∧
      component.frontier = [left, right] ∧
      after.marks = before.marks ∧
      after.parents = before.parents.push before.parents.size ∧
      after.components = before.components.push (some component) ∧
      after.startedAxioms = before.startedAxioms + 1 ∧
      after.firedConnectives = before.firedConnectives := by
  unfold reserveAxiomAt? at equation
  cases linkLookup : certificate.links[linkIndex]? with
  | none =>
      simp [linkLookup] at equation
  | some link =>
      cases link with
      | «axiom» left right =>
          simp [linkLookup] at equation
          by_cases ready :
              certificate.AxiomReservationReady before left right
          · simp [ready] at equation
            cases componentLookup :
                UnificationComponent.axiom? certificate left right with
            | none =>
                simp [componentLookup] at equation
            | some component =>
                simp [componentLookup] at equation
                subst after
                have frontier :
                    component.frontier = [left, right] := by
                  rcases
                      UnificationComponent.axiom?_success
                        componentLookup with
                    ⟨name, positive, leftFormula, rfl⟩
                  rfl
                exact
                  ⟨left, right, component, rfl, ready,
                    componentLookup, frontier, rfl, rfl, rfl, rfl, rfl⟩
          · simp [ready] at equation
      | tensor left right conclusion =>
          simp [linkLookup] at equation
      | «par» left right conclusion =>
          simp [linkLookup] at equation

/-- Reservation leaves both submitted axiom endpoints unmarked. -/
theorem reserveAxiomAt?_endpoint_unmarked
    {certificate : Certificate} {before after : UnificationState}
    {linkIndex : Nat}
    (equation :
      certificate.reserveAxiomAt? before linkIndex = some after) :
    ∃ left right,
      certificate.links[linkIndex]? = some (.axiom left right) ∧
      after.marks[left]? = some none ∧
      after.marks[right]? = some none := by
  rcases certificate.reserveAxiomAt?_exact equation with
    ⟨left, right, component, exactLink, ready, componentLookup,
      frontier, marksEq, parentsEq, componentsEq, counterEq, firedEq⟩
  exact ⟨left, right, exactLink, by
    rw [marksEq]
    exact ready.2.1, by
    rw [marksEq]
    exact ready.2.2.1⟩

/-- Reservation preserves parent/component carrier alignment. -/
theorem reserveAxiomAt?_componentsParentsAligned
    {certificate : Certificate} {before after : UnificationState}
    {linkIndex : Nat}
    (equation :
      certificate.reserveAxiomAt? before linkIndex = some after) :
    after.components.size = after.parents.size := by
  rcases certificate.reserveAxiomAt?_exact equation with
    ⟨left, right, component, exactLink, ready, componentLookup,
      frontier, marksEq, parentsEq, componentsEq, counterEq, firedEq⟩
  rw [componentsEq, parentsEq]
  simp [ready.2.2.2]

/-- Reservation preserves the ordered union-find forest. -/
theorem reserveAxiomAt?_orderedParents
    {certificate : Certificate} {before after : UnificationState}
    {linkIndex : Nat}
    (ordered : before.OrderedParents)
    (equation :
      certificate.reserveAxiomAt? before linkIndex = some after) :
    after.OrderedParents := by
  rcases certificate.reserveAxiomAt?_exact equation with
    ⟨left, right, component, exactLink, ready, componentLookup,
      frontier, marksEq, parentsEq, componentsEq, counterEq, firedEq⟩
  intro token parent lookup
  rw [parentsEq] at lookup
  by_cases fresh : token = before.parents.size
  · subst token
    rw [Array.getElem?_push_size] at lookup
    injection lookup with equality
    exact Nat.le_of_eq equality.symm
  · apply ordered
    simpa [Array.getElem?_push, fresh] using lookup

/-- Reservation preserves the production abstraction contract. -/
theorem reserveAxiomAt?_abstractable
    {certificate : Certificate} {before after : UnificationState}
    {linkIndex : Nat}
    (abstractable : before.Abstractable certificate)
    (ordered : before.OrderedParents)
    (equation :
      certificate.reserveAxiomAt? before linkIndex = some after) :
    after.Abstractable certificate := by
  rcases certificate.reserveAxiomAt?_exact equation with
    ⟨left, right, component, exactLink, ready, componentLookup,
      frontier, marksEq, parentsEq, componentsEq, counterEq, firedEq⟩
  have afterOrdered :
      after.OrderedParents :=
    certificate.reserveAxiomAt?_orderedParents ordered equation
  apply afterOrdered.abstractable
  · simpa [marksEq] using abstractable.markArraySize
  · intro vertex token marked
    apply abstractable.markedVertexBound
    unfold UnificationState.assignedToken? at marked ⊢
    rw [marksEq] at marked
    exact marked
  · intro vertex token marked
    have beforeMarked :
        before.assignedToken? vertex = some token := by
      unfold UnificationState.assignedToken? at marked ⊢
      rw [marksEq] at marked
      exact marked
    have oldBound := abstractable.markedTokenBound beforeMarked
    rw [parentsEq]
    simpa using Nat.lt_succ_of_lt oldBound

/-- A formula-consistent component carrier stays consistent after reservation. -/
theorem reserveAxiomAt?_componentsFormulaConsistent
    {certificate : Certificate} {before after : UnificationState}
    {linkIndex : Nat}
    (consistent :
      before.ComponentsFormulaConsistent certificate)
    (equation :
      certificate.reserveAxiomAt? before linkIndex = some after) :
    after.ComponentsFormulaConsistent certificate := by
  rcases certificate.reserveAxiomAt?_exact equation with
    ⟨left, right, component, exactLink, ready, componentLookup,
      frontier, marksEq, parentsEq, componentsEq, counterEq, firedEq⟩
  have componentConsistent :
      component.FormulaConsistent certificate :=
    UnificationComponent.axiom?_formulaConsistent
      ((certificate.linkLocallyWellFormed_iff _).mp ready.1)
      componentLookup
  have pushed :
      ({ before with
        components :=
          before.components.push (some component) } :
        UnificationState).ComponentsFormulaConsistent certificate :=
    consistent.push componentConsistent
  unfold UnificationState.ComponentsFormulaConsistent at pushed ⊢
  intro index candidate lookup
  apply pushed
  rw [componentsEq] at lookup
  exact lookup

/-- Axiom reservations and the production token horizon advance together. -/
theorem reserveAxiomAt?_counterAligned
    {certificate : Certificate} {before after : UnificationState}
    {linkIndex : Nat}
    (aligned :
      before.startedAxioms = before.parents.size)
    (equation :
      certificate.reserveAxiomAt? before linkIndex = some after) :
    after.startedAxioms = after.parents.size := by
  rcases certificate.reserveAxiomAt?_exact equation with
    ⟨left, right, component, exactLink, ready, componentLookup,
      frontier, marksEq, parentsEq, componentsEq, counterEq, firedEq⟩
  rw [counterEq, parentsEq, aligned]
  simp

/-- Pushing the reserved self-parent leaves every old representative
unchanged. -/
theorem reserveAxiomAt?_old_representative
    {certificate : Certificate} {before after : UnificationState}
    {linkIndex token : Nat}
    (ordered : before.OrderedParents)
    (equation :
      certificate.reserveAxiomAt? before linkIndex = some after) :
    after.representative token = before.representative token := by
  rcases certificate.reserveAxiomAt?_exact equation with
    ⟨left, right, component, exactLink, ready, componentLookup,
      frontier, marksEq, parentsEq, componentsEq, counterEq, firedEq⟩
  have shadow :=
    ordered.startMarking_representative_eq left right token
  simpa [UnificationState.representative,
    UnificationState.startMarking, parentsEq] using shadow

/-- The newly reserved token is represented by itself. -/
theorem reserveAxiomAt?_fresh_representative
    {certificate : Certificate} {before after : UnificationState}
    {linkIndex : Nat}
    (equation :
      certificate.reserveAxiomAt? before linkIndex = some after) :
    after.representative before.parents.size =
      before.parents.size := by
  rcases certificate.reserveAxiomAt?_exact equation with
    ⟨left, right, component, exactLink, ready, componentLookup,
      frontier, marksEq, parentsEq, componentsEq, counterEq, firedEq⟩
  apply UnificationState.representative_eq_of_lookup_self
  rw [parentsEq]
  exact Array.getElem?_push_size

end Certificate

namespace SequentialSchedulerState.SequentialStackState

/-- Raw discovery age stored at an occurrence, without representative
lookup. -/
def rawAgeAt?
    (state : SequentialStackState) (vertex : Vertex) :
    Option RawTokenAge :=
  state.marks[vertex]?.join

end SequentialSchedulerState.SequentialStackState

namespace SequentialSchedulerBridge

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState

/-- The narrow correspondence between delayed raw-age storage and the
production union-find carrier.

The representative equation identifies the production representative with the
executable `sigmaBoundary?` lookup value.  Interpreting that value as the left
boundary of a valid raw-age interval additionally requires the scheduler's
`SigmaAgePartition`/`WellShaped` invariant; that stronger bundle is deliberately
not part of this relation. -/
structure RealizesSigma (stack : SequentialStackState)
    (core : UnificationState) : Prop where
  marks_eq : core.marks = stack.marks
  horizon_eq : core.parents.size = stack.nextAge
  representative_eq_boundary :
    ∀ {age : RawTokenAge}, age < stack.nextAge →
      sigmaBoundary? stack.sigma age =
        some (core.representative age)

/-- A realization identifies scheduler raw-age lookup with the production
raw mark, without conflating either one with its representative. -/
theorem RealizesSigma.rawAgeAt?_eq_assignedToken?
    {stack : SequentialStackState} {core : UnificationState}
    (realizes : RealizesSigma stack core) (vertex : Vertex) :
    stack.rawAgeAt? vertex = core.assignedToken? vertex := by
  unfold SequentialStackState.rawAgeAt?
    UnificationState.assignedToken?
  rw [realizes.marks_eq]

/-- The exact empty production core realizes the exact empty delayed stack. -/
theorem initial_realizesSigma (certificate : Certificate) :
    RealizesSigma
      (SequentialStackState.empty certificate.formulas.size)
      certificate.initialUnificationState := by
  exact {
    marks_eq := rfl
    horizon_eq := rfl
    representative_eq_boundary := by
      intro age ageBound
      simp [SequentialStackState.empty] at ageBound }

/-- One successful delayed initial enqueue and any successful first production
reservation realize the same singleton carrier partition.

This carrier-only lemma intentionally does not relate the enqueue endpoints to
the reserved submitted link.  `init_reserve_route_exact` adds that binding. -/
theorem init_reserve_carrier_realizesSigma
    {certificate : Certificate}
    {reached partner : Vertex}
    {stackAfter : SequentialStackState}
    {coreAfter : UnificationState}
    {linkIndex : Nat}
    (stackEquation :
      SequentialStackState.initEnqueue?
          (SequentialStackState.empty certificate.formulas.size)
          reached partner =
        some stackAfter)
    (coreEquation :
      certificate.reserveAxiomAt?
          certificate.initialUnificationState linkIndex =
        some coreAfter) :
    RealizesSigma stackAfter coreAfter := by
  have stackExact :=
    SequentialStackState.initEnqueue?_exact stackEquation
  rcases certificate.reserveAxiomAt?_exact coreEquation with
    ⟨left, right, component, exactLink, ready, componentLookup,
      frontier, marksEq, parentsEq, componentsEq, counterEq, firedEq⟩
  refine {
    marks_eq := ?_
    horizon_eq := ?_
    representative_eq_boundary := ?_ }
  · calc
      coreAfter.marks =
          certificate.initialUnificationState.marks := marksEq
      _ =
          (SequentialStackState.empty
            certificate.formulas.size).marks := rfl
      _ = stackAfter.marks := stackExact.1.symm
  · calc
      coreAfter.parents.size =
          (certificate.initialUnificationState.parents.push
            certificate.initialUnificationState.parents.size).size :=
        congrArg Array.size parentsEq
      _ = 1 := by rfl
      _ = stackAfter.nextAge := stackExact.2.1.symm
  · intro age ageBound
    have ageZero : age = 0 := by
      have ageBound' : age < 1 := by
        simpa [stackExact.2.1] using ageBound
      exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ ageBound')
    subst age
    rw [stackExact.2.2.1]
    simp only [sigmaBoundary?]
    have fresh :=
      certificate.reserveAxiomAt?_fresh_representative coreEquation
    simpa [Certificate.initialUnificationState] using fresh.symm

/-- A single successful `NEXTAXIOM` result binds the search-oriented delayed
ready bucket and submitted-orientation production reservation to the same
exact result. -/
theorem init_reserve_route_exact
    {certificate : Certificate}
    {fuel : Nat} {tags : Array Bool}
    {start reached partner : Vertex}
    {result :
      SequentialUnification.NextAxiomResult certificate
        certificate.initialUnificationState fuel tags}
    {stackAfter : SequentialStackState}
    {coreAfter : UnificationState}
    (route :
      SequentialUnification.NextAxiomRoute
        start result reached partner)
    (stackEquation :
      SequentialStackState.initEnqueue?
          (SequentialStackState.empty certificate.formulas.size)
          reached partner =
        some stackAfter)
    (coreEquation :
      certificate.reserveAxiomAt?
          certificate.initialUnificationState result.linkIndex =
        some coreAfter) :
    result.orientedEndpoints? = some (reached, partner) ∧
      RealizesSigma stackAfter coreAfter := by
  exact ⟨route.orientedEndpoints?_eq,
    init_reserve_carrier_realizesSigma stackEquation coreEquation⟩

/-- The field-level companion to `init_reserve_route_exact`.

The delayed side exposes the actual search orientation in its ready bucket,
while the production component keeps the submitted axiom orientation from the
same `NextAxiomResult.linkIndex`.  This remains a one-reservation theorem: it
does not provide replay protection or a later-state transition invariant. -/
theorem init_reserve_route_fields
    {certificate : Certificate}
    {fuel : Nat} {tags : Array Bool}
    {start reached partner : Vertex}
    {result :
      SequentialUnification.NextAxiomResult certificate
        certificate.initialUnificationState fuel tags}
    {stackAfter : SequentialStackState}
    {coreAfter : UnificationState}
    (route :
      SequentialUnification.NextAxiomRoute
        start result reached partner)
    (stackEquation :
      SequentialStackState.initEnqueue?
          (SequentialStackState.empty certificate.formulas.size)
          reached partner =
        some stackAfter)
    (coreEquation :
      certificate.reserveAxiomAt?
          certificate.initialUnificationState result.linkIndex =
        some coreAfter) :
    result.orientedEndpoints? = some (reached, partner) ∧
      stackAfter.ready = [[reached, partner]] ∧
      ∃ component,
        coreAfter.components = #[some component] ∧
        component.frontier = [result.left, result.right] ∧
        RealizesSigma stackAfter coreAfter := by
  have stackExact :=
    SequentialStackState.initEnqueue?_exact stackEquation
  rcases certificate.reserveAxiomAt?_exact coreEquation with
    ⟨left, right, component, exactLink, ready, componentLookup,
      frontier, marksEq, parentsEq, componentsEq, counterEq, firedEq⟩
  have submittedLink :
      (Link.axiom left right) =
        .axiom result.left result.right := by
    exact Option.some.inj (exactLink.symm.trans result.exactLink)
  injection submittedLink with leftEq rightEq
  subst left
  subst right
  refine ⟨route.orientedEndpoints?_eq, stackExact.2.2.2.1,
    component, ?_, frontier, ?_⟩
  · simpa [Certificate.initialUnificationState] using componentsEq
  · exact init_reserve_carrier_realizesSigma
      stackEquation coreEquation

end SequentialSchedulerBridge

end ProofNetIR
