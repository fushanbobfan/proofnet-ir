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

/-- Executable state shared by the delayed scheduler reservation layer and
the production unification carrier.

The wrapper deliberately stores raw scheduler marks and production state side
by side instead of identifying raw ages with current representatives.  Search
tags are threaded independently and monotonically by `NEXTAXIOM`. -/
structure ReservationState where
  stack : SequentialStackState
  core : UnificationState
  tags : Array Bool
  deriving Repr, DecidableEq

namespace ReservationState

/-- Exact empty state before the first axiom reservation. -/
def empty (certificate : Certificate) : ReservationState where
  stack := SequentialStackState.empty certificate.formulas.size
  core := certificate.initialUnificationState
  tags := Array.replicate certificate.formulas.size false

end ReservationState

/-- Search and reserve the first axiom while preserving the distinction
between search-oriented and submitted endpoint order. -/
def initializeReservation? (certificate : Certificate)
    (start : Vertex) : Option ReservationState := do
  let before := ReservationState.empty certificate
  let result ←
    SequentialUnification.nextAxiom? certificate before.core
      (SequentialUnification.sourceIndex certificate)
      (SequentialUnification.sourceIndex_sound certificate)
      before.tags start
  let (reached, partner) ← result.orientedEndpoints?
  let stackAfter ←
    before.stack.initEnqueue? reached partner
  let coreAfter ←
    certificate.reserveAxiomAt? before.core result.linkIndex
  some {
    stack := stackAfter
    core := coreAfter
    tags := result.tags }

/-- Search and reserve one later axiom.

This is a reservation-only prefix of Guerrini's `new`: it appends the
search-oriented ready bucket, initializes the fresh waiting cell, appends the
submitted-orientation production component, and threads the complete tag
array.  It deliberately performs no endpoint marking, waiting-list draining,
unification, or connective firing. -/
def reserveNewAxiom? (certificate : Certificate)
    (before : ReservationState) (start : Vertex) :
    Option ReservationState := do
  let result ←
    SequentialUnification.nextAxiom? certificate before.core
      (SequentialUnification.sourceIndex certificate)
      (SequentialUnification.sourceIndex_sound certificate)
      before.tags start
  let (reached, partner) ← result.orientedEndpoints?
  let stackAfter ←
    before.stack.newEnqueue? reached partner
  let coreAfter ←
    certificate.reserveAxiomAt? before.core result.linkIndex
  some {
    stack := stackAfter
    core := coreAfter
    tags := result.tags }

/-- Proof-relevant exact specification of one successful initial wrapper
call. -/
structure InitialReservationStep (certificate : Certificate)
    (after : ReservationState) (start : Vertex) : Type where
  result :
    SequentialUnification.NextAxiomResult certificate
      (ReservationState.empty certificate).core
      certificate.formulas.size
      (ReservationState.empty certificate).tags
  reached : Vertex
  partner : Vertex
  stackAfter : SequentialStackState
  coreAfter : UnificationState
  search_eq :
    SequentialUnification.nextAxiom? certificate
        (ReservationState.empty certificate).core
        (SequentialUnification.sourceIndex certificate)
        (SequentialUnification.sourceIndex_sound certificate)
        (ReservationState.empty certificate).tags start =
      some result
  oriented_eq :
    result.orientedEndpoints? = some (reached, partner)
  stack_eq :
    (ReservationState.empty certificate).stack.initEnqueue?
        reached partner =
      some stackAfter
  core_eq :
    certificate.reserveAxiomAt?
        (ReservationState.empty certificate).core result.linkIndex =
      some coreAfter
  output_eq :
    after = {
      stack := stackAfter
      core := coreAfter
      tags := result.tags }

/-- Proof-relevant exact specification of one successful later wrapper call. -/
structure NewReservationStep (certificate : Certificate)
    (before after : ReservationState) (start : Vertex) : Type where
  result :
    SequentialUnification.NextAxiomResult certificate before.core
      certificate.formulas.size before.tags
  reached : Vertex
  partner : Vertex
  stackAfter : SequentialStackState
  coreAfter : UnificationState
  search_eq :
    SequentialUnification.nextAxiom? certificate before.core
        (SequentialUnification.sourceIndex certificate)
        (SequentialUnification.sourceIndex_sound certificate)
        before.tags start =
      some result
  oriented_eq :
    result.orientedEndpoints? = some (reached, partner)
  stack_eq :
    before.stack.newEnqueue? reached partner = some stackAfter
  core_eq :
    certificate.reserveAxiomAt?
        before.core result.linkIndex = some coreAfter
  output_eq :
    after = {
      stack := stackAfter
      core := coreAfter
      tags := result.tags }

/-- Executable initial success is equivalent to an exact proof-relevant
initial reservation witness. -/
theorem initializeReservation?_some_iff
    {certificate : Certificate} {after : ReservationState}
    {start : Vertex} :
    initializeReservation? certificate start = some after ↔
      Nonempty (InitialReservationStep certificate after start) := by
  constructor
  · intro equation
    unfold initializeReservation? at equation
    cases searchEquation :
        SequentialUnification.nextAxiom? certificate
          (ReservationState.empty certificate).core
          (SequentialUnification.sourceIndex certificate)
          (SequentialUnification.sourceIndex_sound certificate)
          (ReservationState.empty certificate).tags start with
    | none =>
        simp [searchEquation] at equation
    | some result =>
        cases orientedEquation :
            result.orientedEndpoints? with
        | none =>
            simp [searchEquation, orientedEquation] at equation
        | some endpoints =>
            rcases endpoints with ⟨reached, partner⟩
            cases stackEquation :
                (ReservationState.empty certificate).stack.initEnqueue?
                  reached partner with
            | none =>
                simp [searchEquation, orientedEquation, stackEquation]
                  at equation
            | some stackAfter =>
                cases coreEquation :
                    certificate.reserveAxiomAt?
                      (ReservationState.empty certificate).core
                      result.linkIndex with
                | none =>
                    simp [searchEquation, orientedEquation, coreEquation]
                      at equation
                | some coreAfter =>
                    simp [searchEquation, orientedEquation, stackEquation,
                      coreEquation] at equation
                    subst after
                    exact ⟨{
                      result := result
                      reached := reached
                      partner := partner
                      stackAfter := stackAfter
                      coreAfter := coreAfter
                      search_eq := searchEquation
                      oriented_eq := orientedEquation
                      stack_eq := stackEquation
                      core_eq := coreEquation
                      output_eq := rfl }⟩
  · rintro ⟨step⟩
    rcases step with
      ⟨result, reached, partner, stackAfter, coreAfter,
        searchEquation, orientedEquation, stackEquation, coreEquation,
        outputEquation⟩
    subst after
    simp [initializeReservation?, searchEquation, orientedEquation,
      stackEquation, coreEquation]

/-- Executable later success is equivalent to an exact proof-relevant
reservation witness. -/
theorem reserveNewAxiom?_some_iff
    {certificate : Certificate} {before after : ReservationState}
    {start : Vertex} :
    reserveNewAxiom? certificate before start = some after ↔
      Nonempty (NewReservationStep certificate before after start) := by
  constructor
  · intro equation
    unfold reserveNewAxiom? at equation
    cases searchEquation :
        SequentialUnification.nextAxiom? certificate before.core
          (SequentialUnification.sourceIndex certificate)
          (SequentialUnification.sourceIndex_sound certificate)
          before.tags start with
    | none =>
        simp [searchEquation] at equation
    | some result =>
        cases orientedEquation :
            result.orientedEndpoints? with
        | none =>
            simp [searchEquation, orientedEquation] at equation
        | some endpoints =>
            rcases endpoints with ⟨reached, partner⟩
            cases stackEquation :
                before.stack.newEnqueue? reached partner with
            | none =>
                simp [searchEquation, orientedEquation, stackEquation]
                  at equation
            | some stackAfter =>
                cases coreEquation :
                    certificate.reserveAxiomAt?
                      before.core result.linkIndex with
                | none =>
                    simp [searchEquation, orientedEquation, coreEquation]
                      at equation
                | some coreAfter =>
                    simp [searchEquation, orientedEquation, stackEquation,
                      coreEquation] at equation
                    subst after
                    exact ⟨{
                      result := result
                      reached := reached
                      partner := partner
                      stackAfter := stackAfter
                      coreAfter := coreAfter
                      search_eq := searchEquation
                      oriented_eq := orientedEquation
                      stack_eq := stackEquation
                      core_eq := coreEquation
                      output_eq := rfl }⟩
  · rintro ⟨step⟩
    rcases step with
      ⟨result, reached, partner, stackAfter, coreAfter,
        searchEquation, orientedEquation, stackEquation, coreEquation,
        outputEquation⟩
    subst after
    simp [reserveNewAxiom?, searchEquation, orientedEquation,
      stackEquation, coreEquation]

namespace InitialReservationStep

/-- The executable initial witness contains the exact source-left route, not
only an endpoint pair returned by an unchecked extractor. -/
theorem route
    {certificate : Certificate} {after : ReservationState}
    {start : Vertex}
    (step : InitialReservationStep certificate after start) :
    SequentialUnification.NextAxiomRoute
      start step.result step.reached step.partner := by
  rcases
      SequentialUnification.nextAxiom?_route step.search_eq with
    ⟨reached, partner, route⟩
  have endpoints :
      (reached, partner) = (step.reached, step.partner) :=
    Option.some.inj
      (route.orientedEndpoints?_eq.symm.trans step.oriented_eq)
  cases endpoints
  exact route

/-- Threading the initial wrapper's output tags into a later wrapper rules out
reserving the first submitted axiom-link index again.  Distinct duplicate link
slots require separate structural assumptions. -/
theorem linkIndex_ne_next
    {certificate : Certificate}
    {middle after : ReservationState}
    {firstStart secondStart : Vertex}
    (first :
      InitialReservationStep certificate middle firstStart)
    (second :
      NewReservationStep certificate middle after secondStart) :
    first.result.linkIndex ≠ second.result.linkIndex := by
  have middleTags : middle.tags = first.result.tags := by
    simpa using congrArg ReservationState.tags first.output_eq
  apply
    first.result.linkIndex_ne_of_input_left_tagged second.result
  rw [middleTags]
  exact first.result.leftTagged.2

end InitialReservationStep

namespace NewReservationStep

/-- Every successful later wrapper witness contains its exact source-left
route. -/
theorem route
    {certificate : Certificate} {before after : ReservationState}
    {start : Vertex}
    (step : NewReservationStep certificate before after start) :
    SequentialUnification.NextAxiomRoute
      start step.result step.reached step.partner := by
  rcases
      SequentialUnification.nextAxiom?_route step.search_eq with
    ⟨reached, partner, route⟩
  have endpoints :
      (reached, partner) = (step.reached, step.partner) :=
    Option.some.inj
      (route.orientedEndpoints?_eq.symm.trans step.oriented_eq)
  cases endpoints
  exact route

/-- Two composable later wrapper calls cannot reserve the same submitted
axiom-link index when the first call's complete tag output is threaded
unchanged.  Distinct duplicate link slots require separate structural
assumptions. -/
theorem linkIndex_ne
    {certificate : Certificate}
    {before middle after : ReservationState}
    {firstStart secondStart : Vertex}
    (first :
      NewReservationStep certificate before middle firstStart)
    (second :
      NewReservationStep certificate middle after secondStart) :
    first.result.linkIndex ≠ second.result.linkIndex := by
  have middleTags : middle.tags = first.result.tags := by
    simpa using congrArg ReservationState.tags first.output_eq
  apply
    first.result.linkIndex_ne_of_input_left_tagged second.result
  rw [middleTags]
  exact first.result.leftTagged.2

end NewReservationStep

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

/-- Reservation-layer invariant currently proved for initialization and every
successful reservation-only `new` wrapper.

It combines scheduler shape, the exact raw-age/representative bridge,
production carrier soundness, counter alignment, and tag-domain alignment.
It intentionally does not assert Figure-7 liveness, waiting-dependency
semantics, cross-ready-bucket uniqueness, or completeness. -/
structure ReservationInvariant (certificate : Certificate)
    (state : ReservationState) : Prop where
  stack_wellShaped :
    state.stack.WellShaped certificate.formulas.size
  realizesSigma :
    RealizesSigma state.stack state.core
  core_orderedParents :
    state.core.OrderedParents
  core_abstractable :
    state.core.Abstractable certificate
  core_componentsFormulaConsistent :
    state.core.ComponentsFormulaConsistent certificate
  core_carriers_aligned :
    state.core.components.size = state.core.parents.size
  core_counter_aligned :
    state.core.startedAxioms = state.core.parents.size
  tags_size :
    state.tags.size = certificate.formulas.size

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

/-- The exact empty wrapper state satisfies every reservation-layer
invariant, before any reservation is attempted. -/
theorem empty_reservationInvariant (certificate : Certificate) :
    ReservationInvariant certificate
      (ReservationState.empty certificate) := by
  exact {
    stack_wellShaped :=
      SequentialStackState.empty_wellShaped certificate.formulas.size
    realizesSigma := initial_realizesSigma certificate
    core_orderedParents :=
      Certificate.initialUnificationState_orderedParents certificate
    core_abstractable :=
      Certificate.initialUnificationState_abstractable certificate
    core_componentsFormulaConsistent :=
      Certificate.initialUnificationState_componentsFormulaConsistent
        certificate
    core_carriers_aligned :=
      Certificate.initialUnificationState_componentsParentsAligned
        certificate
    core_counter_aligned := rfl
    tags_size := by simp [ReservationState.empty] }

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

/-- A successful exact initial wrapper call establishes the complete
reservation-layer invariant. -/
theorem InitialReservationStep.reservationInvariant
    {certificate : Certificate} {after : ReservationState}
    {start : Vertex}
    (step : InitialReservationStep certificate after start) :
    ReservationInvariant certificate after := by
  rcases step with
    ⟨result, reached, partner, stackAfter, coreAfter,
      searchEquation, orientedEquation, stackEquation, coreEquation,
      outputEquation⟩
  subst after
  have initialInvariant :=
    empty_reservationInvariant certificate
  exact {
    stack_wellShaped :=
      SequentialStackState.initEnqueue?_wellShaped
        initialInvariant.stack_wellShaped stackEquation
    realizesSigma :=
      init_reserve_carrier_realizesSigma stackEquation coreEquation
    core_orderedParents :=
      certificate.reserveAxiomAt?_orderedParents
        initialInvariant.core_orderedParents coreEquation
    core_abstractable :=
      certificate.reserveAxiomAt?_abstractable
        initialInvariant.core_abstractable
        initialInvariant.core_orderedParents coreEquation
    core_componentsFormulaConsistent :=
      certificate.reserveAxiomAt?_componentsFormulaConsistent
        initialInvariant.core_componentsFormulaConsistent coreEquation
    core_carriers_aligned :=
      certificate.reserveAxiomAt?_componentsParentsAligned coreEquation
    core_counter_aligned :=
      certificate.reserveAxiomAt?_counterAligned
        initialInvariant.core_counter_aligned coreEquation
    tags_size := by
      calc
        result.tags.size =
            (ReservationState.empty certificate).tags.size :=
          result.tagsSize
        _ = certificate.formulas.size := by
          simp [ReservationState.empty] }

/-- Appending one delayed raw-age reservation and one production component
reservation preserves the exact `sigma`/union-find correspondence.

This theorem is intentionally carrier-local.  It requires the old
`WellShaped` partition and ordered parent forest, but it does not claim that
the selected endpoints are scheduler-live or that an arbitrary production
merge preserves `RealizesSigma`. -/
theorem new_reserve_carrier_realizesSigma
    {certificate : Certificate}
    {stackBefore stackAfter : SequentialStackState}
    {coreBefore coreAfter : UnificationState}
    {reached partner : Vertex}
    {linkIndex : Nat}
    (wellShaped :
      stackBefore.WellShaped certificate.formulas.size)
    (realizes : RealizesSigma stackBefore coreBefore)
    (ordered : coreBefore.OrderedParents)
    (stackEquation :
      stackBefore.newEnqueue? reached partner = some stackAfter)
    (coreEquation :
      certificate.reserveAxiomAt? coreBefore linkIndex = some coreAfter) :
    RealizesSigma stackAfter coreAfter := by
  have stackExact :=
    SequentialStackState.newEnqueue?_exact stackEquation
  rcases certificate.reserveAxiomAt?_exact coreEquation with
    ⟨left, right, component, exactLink, ready, componentLookup,
      frontier, marksEq, parentsEq, componentsEq, counterEq, firedEq⟩
  refine {
    marks_eq := ?_
    horizon_eq := ?_
    representative_eq_boundary := ?_ }
  · calc
      coreAfter.marks = coreBefore.marks := marksEq
      _ = stackBefore.marks := realizes.marks_eq
      _ = stackAfter.marks := stackExact.1.symm
  · calc
      coreAfter.parents.size =
          (coreBefore.parents.push coreBefore.parents.size).size := by
        rw [parentsEq]
      _ = coreBefore.parents.size + 1 := by simp
      _ = stackBefore.nextAge + 1 := by rw [realizes.horizon_eq]
      _ = stackAfter.nextAge := stackExact.2.1.symm
  · intro age ageBound
    have ageBound' : age < stackBefore.nextAge + 1 := by
      simpa [stackExact.2.1] using ageBound
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ ageBound') with
      oldAge | freshAge
    · calc
        sigmaBoundary? stackAfter.sigma age =
            sigmaBoundary?
              (stackBefore.sigma ++ [stackBefore.nextAge]) age := by
          rw [stackExact.2.2.1]
        _ = sigmaBoundary? stackBefore.sigma age :=
          sigmaBoundary?_append_fresh_old oldAge
        _ = some (coreBefore.representative age) :=
          realizes.representative_eq_boundary oldAge
        _ = some (coreAfter.representative age) := by
          rw [certificate.reserveAxiomAt?_old_representative
            ordered coreEquation]
    · subst age
      calc
        sigmaBoundary? stackAfter.sigma stackBefore.nextAge =
            sigmaBoundary?
              (stackBefore.sigma ++ [stackBefore.nextAge])
              stackBefore.nextAge := by
          rw [stackExact.2.2.1]
        _ = some stackBefore.nextAge :=
          wellShaped.sigma_partition.sigmaBoundary?_append_fresh_self
        _ =
            some (coreAfter.representative stackBefore.nextAge) := by
          rw [← realizes.horizon_eq]
          rw [certificate.reserveAxiomAt?_fresh_representative coreEquation]

/-- The later-state companion of `init_reserve_route_exact`: one exact
`NEXTAXIOM` result controls both the search-oriented appended ready bucket and
the submitted-orientation production reservation. -/
theorem new_reserve_route_exact
    {certificate : Certificate}
    {stackBefore stackAfter : SequentialStackState}
    {coreBefore coreAfter : UnificationState}
    {fuel : Nat} {tags : Array Bool}
    {start reached partner : Vertex}
    {result :
      SequentialUnification.NextAxiomResult certificate
        coreBefore fuel tags}
    (wellShaped :
      stackBefore.WellShaped certificate.formulas.size)
    (realizes : RealizesSigma stackBefore coreBefore)
    (ordered : coreBefore.OrderedParents)
    (route :
      SequentialUnification.NextAxiomRoute
        start result reached partner)
    (stackEquation :
      stackBefore.newEnqueue? reached partner = some stackAfter)
    (coreEquation :
      certificate.reserveAxiomAt?
          coreBefore result.linkIndex = some coreAfter) :
    result.orientedEndpoints? = some (reached, partner) ∧
      RealizesSigma stackAfter coreAfter := by
  exact ⟨route.orientedEndpoints?_eq,
    new_reserve_carrier_realizesSigma
      wellShaped realizes ordered stackEquation coreEquation⟩

/-- Field-level later reservation theorem.  The newly appended ready bucket
uses the search orientation while the newly appended production component
uses the same result's submitted orientation. -/
theorem new_reserve_route_fields
    {certificate : Certificate}
    {stackBefore stackAfter : SequentialStackState}
    {coreBefore coreAfter : UnificationState}
    {fuel : Nat} {tags : Array Bool}
    {start reached partner : Vertex}
    {result :
      SequentialUnification.NextAxiomResult certificate
        coreBefore fuel tags}
    (wellShaped :
      stackBefore.WellShaped certificate.formulas.size)
    (realizes : RealizesSigma stackBefore coreBefore)
    (ordered : coreBefore.OrderedParents)
    (route :
      SequentialUnification.NextAxiomRoute
        start result reached partner)
    (stackEquation :
      stackBefore.newEnqueue? reached partner = some stackAfter)
    (coreEquation :
      certificate.reserveAxiomAt?
          coreBefore result.linkIndex = some coreAfter) :
    result.orientedEndpoints? = some (reached, partner) ∧
      stackAfter.ready =
        stackBefore.ready ++ [[reached, partner]] ∧
      ∃ component,
        coreAfter.components =
          coreBefore.components.push (some component) ∧
        component.frontier = [result.left, result.right] ∧
        RealizesSigma stackAfter coreAfter := by
  have stackExact :=
    SequentialStackState.newEnqueue?_exact stackEquation
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
    component, componentsEq, frontier, ?_⟩
  exact new_reserve_carrier_realizesSigma
    wellShaped realizes ordered stackEquation coreEquation

/-- Every successful later wrapper call preserves the complete
reservation-layer invariant. -/
theorem NewReservationStep.reservationInvariant
    {certificate : Certificate}
    {before after : ReservationState}
    {start : Vertex}
    (beforeInvariant : ReservationInvariant certificate before)
    (step : NewReservationStep certificate before after start) :
    ReservationInvariant certificate after := by
  rcases step with
    ⟨result, reached, partner, stackAfter, coreAfter,
      searchEquation, orientedEquation, stackEquation, coreEquation,
      outputEquation⟩
  subst after
  exact {
    stack_wellShaped :=
      SequentialStackState.newEnqueue?_wellShaped
        beforeInvariant.stack_wellShaped stackEquation
    realizesSigma :=
      new_reserve_carrier_realizesSigma
        beforeInvariant.stack_wellShaped
        beforeInvariant.realizesSigma
        beforeInvariant.core_orderedParents
        stackEquation coreEquation
    core_orderedParents :=
      certificate.reserveAxiomAt?_orderedParents
        beforeInvariant.core_orderedParents coreEquation
    core_abstractable :=
      certificate.reserveAxiomAt?_abstractable
        beforeInvariant.core_abstractable
        beforeInvariant.core_orderedParents coreEquation
    core_componentsFormulaConsistent :=
      certificate.reserveAxiomAt?_componentsFormulaConsistent
        beforeInvariant.core_componentsFormulaConsistent coreEquation
    core_carriers_aligned :=
      certificate.reserveAxiomAt?_componentsParentsAligned coreEquation
    core_counter_aligned :=
      certificate.reserveAxiomAt?_counterAligned
        beforeInvariant.core_counter_aligned coreEquation
    tags_size := by
      calc
        result.tags.size = before.tags.size := result.tagsSize
        _ = certificate.formulas.size := beforeInvariant.tags_size }

end SequentialSchedulerBridge

end ProofNetIR
