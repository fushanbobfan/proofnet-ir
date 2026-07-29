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

namespace UnificationState

open SequentialSchedulerState

/-- Explicit failures of the production-side raw marking primitive.  As on the
independent stack, an out-of-bounds lookup is not conflated with an allocated
but already marked occurrence. -/
inductive MarkReadyRawError where
  | markOutOfBounds (vertex : Vertex)
  | alreadyMarked (vertex : Vertex) (rawAge : RawTokenAge)
  deriving Repr, DecidableEq

/-- Production-core update corresponding only to the common
`μ[u₁ ↦ i]` prefix of the non-`init` rules in Guerrini Figure 7.

The update writes one raw age into an explicitly unmarked occurrence.  It does
not append or union parents, mutate parsed components, advance either counter,
or invoke the eager `startMarking`/`markConclusion` operations. -/
def markReadyRaw? (state : UnificationState)
    (vertex : Vertex) (rawAge : RawTokenAge) :
    Except MarkReadyRawError UnificationState :=
  match state.marks[vertex]? with
  | none => .error (.markOutOfBounds vertex)
  | some none =>
      .ok {
        state with
        marks := state.marks.setIfInBounds vertex (some rawAge) }
  | some (some previousRawAge) =>
      .error (.alreadyMarked vertex previousRawAge)

/-- Proof-relevant exact specification of one successful production raw-mark
update. -/
structure MarkReadyRawStep (before after : UnificationState)
    (vertex : Vertex) (rawAge : RawTokenAge) : Type where
  unmarked : before.marks[vertex]? = some none
  after_eq :
    after = {
      before with
      marks := before.marks.setIfInBounds vertex (some rawAge) }

/-- Executable raw-mark success is equivalent to the exact dependent update
witness. -/
theorem markReadyRaw?_ok_iff
    {before after : UnificationState}
    {vertex : Vertex} {rawAge : RawTokenAge} :
    before.markReadyRaw? vertex rawAge = .ok after ↔
      Nonempty (MarkReadyRawStep before after vertex rawAge) := by
  constructor
  · intro equation
    unfold markReadyRaw? at equation
    cases lookup : before.marks[vertex]? with
    | none =>
        simp [lookup] at equation
    | some mark =>
        cases mark with
        | none =>
            simp [lookup] at equation
            subst after
            exact ⟨{
              unmarked := lookup
              after_eq := rfl }⟩
        | some previousRawAge =>
            simp [lookup] at equation
  · rintro ⟨step⟩
    rcases step with ⟨unmarked, rfl⟩
    simp [markReadyRaw?, unmarked]

/-- An out-of-bounds raw-mark failure is exactly an array lookup returning
`none`; it is not the successful in-bounds unmarked lookup `some none`. -/
theorem markReadyRaw?_markOutOfBounds_iff
    {state : UnificationState} {vertex : Vertex}
    {rawAge : RawTokenAge} :
    state.markReadyRaw? vertex rawAge =
        .error (.markOutOfBounds vertex) ↔
      state.marks[vertex]? = none := by
  unfold markReadyRaw?
  cases lookup : state.marks[vertex]? with
  | none =>
      simp
  | some mark =>
      cases mark <;> simp

/-- An already-marked failure carries the exact previous raw age. -/
theorem markReadyRaw?_alreadyMarked_iff
    {state : UnificationState} {vertex : Vertex}
    {rawAge previousRawAge : RawTokenAge} :
    state.markReadyRaw? vertex rawAge =
        .error (.alreadyMarked vertex previousRawAge) ↔
      state.marks[vertex]? = some (some previousRawAge) := by
  unfold markReadyRaw?
  cases lookup : state.marks[vertex]? with
  | none =>
      simp
  | some mark =>
      cases mark with
      | none =>
          simp
      | some storedRawAge =>
          simp

/-- Exact changed and unchanged production fields of a successful raw-mark
update. -/
theorem markReadyRaw?_exact
    {before after : UnificationState}
    {vertex : Vertex} {rawAge : RawTokenAge}
    (equation : before.markReadyRaw? vertex rawAge = .ok after) :
    before.marks[vertex]? = some none ∧
      after.marks =
        before.marks.setIfInBounds vertex (some rawAge) ∧
      after.parents = before.parents ∧
      after.components = before.components ∧
      after.startedAxioms = before.startedAxioms ∧
      after.firedConnectives = before.firedConnectives ∧
      after.marks[vertex]? = some (some rawAge) := by
  rcases markReadyRaw?_ok_iff.mp equation with ⟨step⟩
  have vertexBound : vertex < before.marks.size :=
    (Array.getElem?_eq_some_iff.mp step.unmarked).1
  refine ⟨step.unmarked, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [step.after_eq]
  · rw [step.after_eq]
  · rw [step.after_eq]
  · rw [step.after_eq]
  · rw [step.after_eq]
  · rw [step.after_eq]
    simp [vertexBound]

/-- Raw marking changes neither the parent carrier nor the parsed-component
carrier. -/
theorem markReadyRaw?_carriers
    {before after : UnificationState}
    {vertex : Vertex} {rawAge : RawTokenAge}
    (equation : before.markReadyRaw? vertex rawAge = .ok after) :
    after.parents = before.parents ∧
      after.components = before.components := by
  have exact := markReadyRaw?_exact equation
  exact ⟨exact.2.2.1, exact.2.2.2.1⟩

/-- Raw marking advances neither production counter. -/
theorem markReadyRaw?_counters
    {before after : UnificationState}
    {vertex : Vertex} {rawAge : RawTokenAge}
    (equation : before.markReadyRaw? vertex rawAge = .ok after) :
    after.startedAxioms = before.startedAxioms ∧
      after.firedConnectives = before.firedConnectives := by
  have exact := markReadyRaw?_exact equation
  exact ⟨exact.2.2.2.2.1, exact.2.2.2.2.2.1⟩

/-- Raw marking leaves the ordered parent forest unchanged. -/
theorem markReadyRaw?_orderedParents
    {before after : UnificationState}
    {vertex : Vertex} {rawAge : RawTokenAge}
    (ordered : before.OrderedParents)
    (equation : before.markReadyRaw? vertex rawAge = .ok after) :
    after.OrderedParents := by
  have parentsEquation := (markReadyRaw?_carriers equation).1
  intro token parent lookup
  apply ordered
  rw [parentsEquation] at lookup
  exact lookup

/-- Raw marking preserves the executable abstraction contract when the raw age
is already allocated in the unchanged parent carrier. -/
theorem markReadyRaw?_abstractable
    {certificate : Certificate}
    {before after : UnificationState}
    {vertex : Vertex} {rawAge : RawTokenAge}
    (abstractable : before.Abstractable certificate)
    (rawAgeBound : rawAge < before.parents.size)
    (equation : before.markReadyRaw? vertex rawAge = .ok after) :
    after.Abstractable certificate := by
  rcases markReadyRaw?_ok_iff.mp equation with ⟨step⟩
  have vertexBound : vertex < before.marks.size :=
    (Array.getElem?_eq_some_iff.mp step.unmarked).1
  rw [step.after_eq]
  refine {
    markArraySize := by
      simpa using abstractable.markArraySize
    markedVertexBound := ?_
    markedTokenBound := ?_
    representativeBound := abstractable.representativeBound
    representativeIdempotent :=
      abstractable.representativeIdempotent }
  · intro candidate token marked
    by_cases same : vertex = candidate
    · simpa [same, abstractable.markArraySize] using
        (show vertex < certificate.formulas.size by
          rw [← abstractable.markArraySize]
          exact vertexBound)
    · apply abstractable.markedVertexBound
      unfold assignedToken? at marked ⊢
      simpa [Array.getElem?_setIfInBounds, same] using marked
  · intro candidate token marked
    by_cases same : vertex = candidate
    · subst candidate
      unfold assignedToken? at marked
      simp [vertexBound] at marked
      subst token
      exact rawAgeBound
    · apply abstractable.markedTokenBound
      unfold assignedToken? at marked ⊢
      simpa [Array.getElem?_setIfInBounds, same] using marked

/-- Raw marking cannot change formula consistency because the component array
is unchanged. -/
theorem markReadyRaw?_componentsFormulaConsistent
    {certificate : Certificate}
    {before after : UnificationState}
    {vertex : Vertex} {rawAge : RawTokenAge}
    (consistent : before.ComponentsFormulaConsistent certificate)
    (equation : before.markReadyRaw? vertex rawAge = .ok after) :
    after.ComponentsFormulaConsistent certificate := by
  have componentsEquation := (markReadyRaw?_carriers equation).2
  intro index component lookup
  apply consistent
  rw [componentsEquation] at lookup
  exact lookup

end UnificationState

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

This is a reservation-only prefix of the operational `new`: it appends the
search-oriented ready bucket, initializes the old active waiting boundary
while leaving the fresh top undefined, appends the submitted-orientation
production component, and threads the complete tag array.  It deliberately
performs no endpoint marking, waiting-list draining, unification, or
connective firing. -/
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
    before.stack.operationalNewEnqueue? reached partner
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
    before.stack.operationalNewEnqueue? reached partner = some stackAfter
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
                before.stack.operationalNewEnqueue? reached partner with
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

It combines scheduler shape, the exact initialized waiting-cell domain, the
raw-age/representative bridge, production carrier soundness, counter alignment,
and tag-domain alignment.  The waiting-domain field says which cells are
initialized, not who owns each payload or how wait/unify transfers it.  The
invariant intentionally does not assert Figure-7 liveness, payload/dependency
semantics, global queue provenance, or completeness. -/
structure ReservationInvariant (certificate : Certificate)
    (state : ReservationState) : Prop where
  stack_wellShaped :
    state.stack.WellShaped certificate.formulas.size
  stack_operationalWaitingDomain :
    state.stack.OperationalWaitingDomain
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

/-- Synchronizing the independent pop-before-mark update with the production
raw-mark update preserves the exact raw-age/union-find bridge.

Both primitives write the same selected vertex with the same old top raw age.
Neither changes `sigma` or the parent carrier, so the representative equation
is inherited unchanged. -/
theorem popReadyMark_markReadyRaw_realizesSigma
    {stackBefore : SequentialStackState}
    {stackResult : PopReadyMarkResult}
    {coreBefore coreAfter : UnificationState}
    (realizes : RealizesSigma stackBefore coreBefore)
    (stackEquation :
      stackBefore.popReadyMark? = .ok stackResult)
    (coreEquation :
      coreBefore.markReadyRaw?
          stackResult.vertex stackResult.rawAge =
        .ok coreAfter) :
    RealizesSigma stackResult.after coreAfter := by
  rcases SequentialStackState.popReadyMark?_exact stackEquation with
    ⟨topEquation, sigmaTopEquation, stackUnmarked, stackMarksEquation,
      stackNextAgeEquation, stackSigmaEquation, stackReadyEquation,
      stackWaitingEquation, stackMarked⟩
  rcases UnificationState.markReadyRaw?_exact coreEquation with
    ⟨coreUnmarked, coreMarksEquation, coreParentsEquation,
      coreComponentsEquation, coreStartedEquation, coreFiredEquation,
      coreMarked⟩
  refine {
    marks_eq := ?_
    horizon_eq := ?_
    representative_eq_boundary := ?_ }
  · calc
      coreAfter.marks =
          coreBefore.marks.setIfInBounds
            stackResult.vertex (some stackResult.rawAge) :=
        coreMarksEquation
      _ =
          stackBefore.marks.setIfInBounds
            stackResult.vertex (some stackResult.rawAge) := by
        rw [realizes.marks_eq]
      _ = stackResult.after.marks := stackMarksEquation.symm
  · calc
      coreAfter.parents.size = coreBefore.parents.size := by
        rw [coreParentsEquation]
      _ = stackBefore.nextAge := realizes.horizon_eq
      _ = stackResult.after.nextAge := stackNextAgeEquation.symm
  · intro age ageBound
    have oldAgeBound : age < stackBefore.nextAge := by
      simpa [stackNextAgeEquation] using ageBound
    have representativeEquation :
        coreAfter.representative age =
          coreBefore.representative age := by
      unfold UnificationState.representative
      rw [coreParentsEquation]
    calc
      sigmaBoundary? stackResult.after.sigma age =
          sigmaBoundary? stackBefore.sigma age := by
        rw [stackSigmaEquation]
      _ = some (coreBefore.representative age) :=
        realizes.representative_eq_boundary oldAgeBound
      _ = some (coreAfter.representative age) := by
        rw [representativeEquation]

/-- The synchronized common prefix of every non-`init` Figure-7 rule preserves
the complete reservation-layer invariant.

This theorem still does not choose among `concl`/`nop`/`wait`/`forward`/`new`/
`unify`.  It only pops and marks the selected `u₁`, leaving tags unchanged.
The allocated-age side condition needed by the production abstraction follows
from the old top `sigma` membership and `RealizesSigma.horizon_eq`. -/
theorem popReadyMark_markReadyRaw_reservationInvariant
    {certificate : Certificate}
    {before : ReservationState}
    {stackResult : PopReadyMarkResult}
    {coreAfter : UnificationState}
    (invariant : ReservationInvariant certificate before)
    (stackEquation :
      before.stack.popReadyMark? = .ok stackResult)
    (coreEquation :
      before.core.markReadyRaw?
          stackResult.vertex stackResult.rawAge =
        .ok coreAfter) :
    ReservationInvariant certificate {
      stack := stackResult.after
      core := coreAfter
      tags := before.tags } := by
  rcases SequentialStackState.popReadyMark?_exact stackEquation with
    ⟨_, stackSigmaTopEquation, _, _, stackNextAgeEquation,
      stackSigmaEquation, _, stackWaitingEquation, _⟩
  rcases List.getLast?_eq_some_iff.mp stackSigmaTopEquation with
    ⟨sigmaPrefix, sigmaDecomposition⟩
  have rawAgeMembership :
      stackResult.rawAge ∈ before.stack.sigma := by
    rw [sigmaDecomposition]
    simp
  have rawAgeStackBound :
      stackResult.rawAge < before.stack.nextAge :=
    invariant.stack_wellShaped.sigma_partition.boundary_lt
      stackResult.rawAge rawAgeMembership
  have rawAgeCoreBound :
      stackResult.rawAge < before.core.parents.size := by
    rw [invariant.realizesSigma.horizon_eq]
    exact rawAgeStackBound
  have carriers :=
    UnificationState.markReadyRaw?_carriers coreEquation
  have counters :=
    UnificationState.markReadyRaw?_counters coreEquation
  exact {
    stack_wellShaped :=
      SequentialStackState.popReadyMark?_wellShaped
        invariant.stack_wellShaped stackEquation
    stack_operationalWaitingDomain := by
      exact {
        initialized_iff_inactive :=
          fun {age : RawTokenAge}
              (ageBound :
                age < stackResult.after.nextAge) => by
            have oldAgeBound : age < before.stack.nextAge := by
              simpa [stackNextAgeEquation] using ageBound
            have oldDomain :=
              OperationalWaitingDomain.initialized_iff_inactive
                invariant.stack_operationalWaitingDomain oldAgeBound
            simpa [SequentialStackState.WaitingInitializedAt,
              stackNextAgeEquation, stackSigmaEquation,
              stackWaitingEquation] using oldDomain }
    realizesSigma :=
      popReadyMark_markReadyRaw_realizesSigma
        invariant.realizesSigma stackEquation coreEquation
    core_orderedParents :=
      UnificationState.markReadyRaw?_orderedParents
        invariant.core_orderedParents coreEquation
    core_abstractable :=
      UnificationState.markReadyRaw?_abstractable
        invariant.core_abstractable rawAgeCoreBound coreEquation
    core_componentsFormulaConsistent :=
      UnificationState.markReadyRaw?_componentsFormulaConsistent
        invariant.core_componentsFormulaConsistent coreEquation
    core_carriers_aligned := by
      rw [carriers.1, carriers.2]
      exact invariant.core_carriers_aligned
    core_counter_aligned := by
      rw [counters.1, carriers.1]
      exact invariant.core_counter_aligned
    tags_size := invariant.tags_size }

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
    stack_operationalWaitingDomain :=
      SequentialStackState.empty_operationalWaitingDomain
        certificate.formulas.size
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
    stack_operationalWaitingDomain :=
      SequentialStackState.initEnqueue?_operationalWaitingDomain
        stackEquation
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
      stackBefore.operationalNewEnqueue? reached partner =
        some stackAfter)
    (coreEquation :
      certificate.reserveAxiomAt? coreBefore linkIndex = some coreAfter) :
    RealizesSigma stackAfter coreAfter := by
  rcases
      SequentialStackState.operationalNewEnqueue?_exact stackEquation with
    ⟨active, activeEquation, activeLt, stackMarksEq, stackNextAgeEq,
      stackSigmaEq, stackReadyEq, stackWaitingEq, activeInitialized,
      freshUndefined⟩
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
      _ = stackAfter.marks := stackMarksEq.symm
  · calc
      coreAfter.parents.size =
          (coreBefore.parents.push coreBefore.parents.size).size := by
        rw [parentsEq]
      _ = coreBefore.parents.size + 1 := by simp
      _ = stackBefore.nextAge + 1 := by rw [realizes.horizon_eq]
      _ = stackAfter.nextAge := stackNextAgeEq.symm
  · intro age ageBound
    have ageBound' : age < stackBefore.nextAge + 1 := by
      simpa [stackNextAgeEq] using ageBound
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ ageBound') with
      oldAge | freshAge
    · calc
        sigmaBoundary? stackAfter.sigma age =
            sigmaBoundary?
              (stackBefore.sigma ++ [stackBefore.nextAge]) age := by
          rw [stackSigmaEq]
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
          rw [stackSigmaEq]
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
      stackBefore.operationalNewEnqueue? reached partner =
        some stackAfter)
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
      stackBefore.operationalNewEnqueue? reached partner =
        some stackAfter)
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
  rcases
      SequentialStackState.operationalNewEnqueue?_exact stackEquation with
    ⟨active, activeEquation, activeLt, stackMarksEq, stackNextAgeEq,
      stackSigmaEq, stackReadyEq, stackWaitingEq, activeInitialized,
      freshUndefined⟩
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
  refine ⟨route.orientedEndpoints?_eq, stackReadyEq,
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
      SequentialStackState.operationalNewEnqueue?_wellShaped
        beforeInvariant.stack_wellShaped stackEquation
    stack_operationalWaitingDomain :=
      SequentialStackState.operationalNewEnqueue?_operationalWaitingDomain
        beforeInvariant.stack_operationalWaitingDomain
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
