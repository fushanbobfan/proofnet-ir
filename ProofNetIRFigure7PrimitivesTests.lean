import ProofNetIR.SequentialSchedulerInvariant
import ProofNetIR.SequentialComponentProvenance

namespace ProofNetIR

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState

namespace Figure7PrimitivesTests

open SequentialSchedulerBridge

private def axiomCertificate : Certificate where
  formulas := #[.atom "p" true, .atom "p" false]
  links := [.axiom 0 1]
  conclusions := [0, 1]

private theorem axiomCertificate_structural :
    axiomCertificate.StructurallyWellFormed := by
  exact
    (Certificate.wellFormed_iff_structurallyWellFormed
      axiomCertificate).mp (by native_decide)

private def parCertificate : Certificate where
  formulas := #[
    .atom "p" true,
    .atom "p" false,
    .par (.atom "p" true) (.atom "p" false)]
  links := [.axiom 0 1, .par 0 1 2]
  conclusions := [2]

private theorem parCertificate_structural :
    parCertificate.StructurallyWellFormed := by
  exact
    (Certificate.wellFormed_iff_structurallyWellFormed
      parCertificate).mp (by native_decide)

private def forgedProducedParState : ReservationState where
  stack := SequentialStackState.empty parCertificate.formulas.size
  core := {
    marks := #[none, none, none]
    parents := #[0]
    components := #[some {
      tree := .axiom "p" true
      frontier := [2] }]
    startedAxioms := 1
    firedConnectives := 0 }
  tags := Array.replicate parCertificate.formulas.size false

/-- Regression for the reviewed causal gap: structural certificate ownership
alone does not make a forged unmarked live-frontier conclusion safe. The new
predicate rejects it because its submitted premises have no concrete marks. -/
example :
    parCertificate.StructurallyWellFormed ∧
      ¬ ProducedPremisesMarked parCertificate
        forgedProducedParState := by
  refine ⟨parCertificate_structural, ?_⟩
  intro causal
  have produced : Produced forgedProducedParState 2 :=
    Or.inr (by native_decide)
  have premiseMarks :=
    causal (link := .par 0 1 2) (by native_decide) produced
  rcases premiseMarks.1 with ⟨age, lookup⟩
  simp [forgedProducedParState] at lookup

/-- The public first-occurrence wrapper retains the exact executable first
pick while keeping the recursive helper private. -/
example :
    Certificate.FirstOccurrencePick [2, 1, 2] 2 0 [1, 2] := by
  rfl

/-- The public production picker exposes the exact derivation focus, rather
than merely preserving a value-level membership fact. -/
example :
    CutFreeDerivation.pick? ([2, 1, 2] : List Vertex) 0 =
      some (2, [1, 2]) := by
  exact Certificate.FirstOccurrencePick.positional
    (show
      Certificate.FirstOccurrencePick [2, 1, 2] 2 0 [1, 2] by
        rfl)

example :
    1 ∈ ([1, 2] : List Vertex) := by
  exact Certificate.FirstOccurrencePick.mem_remaining_of_ne
    (show
      Certificate.FirstOccurrencePick [2, 1, 2] 2 0 [1, 2] by rfl)
    (by decide) (by decide)

example :
    ∃ leftIndex afterLeft rightIndex context,
      Certificate.FirstOccurrencePick [2, 1, 3] 2
          leftIndex afterLeft ∧
        Certificate.FirstOccurrencePick afterLeft 3
          rightIndex context := by
  exact Certificate.FirstOccurrencePick.two_of_mem
    (by decide) (by decide) (by decide)

private def repeatedOccurrenceCertificate : Certificate where
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

private theorem repeatedOccurrenceCertificate_structural :
    repeatedOccurrenceCertificate.StructurallyWellFormed := by
  exact
    (Certificate.wellFormed_iff_structurallyWellFormed
      repeatedOccurrenceCertificate).mp (by native_decide)

private def forgedRepeatedComponent : UnificationComponent where
  tree := .axiom "p" true
  frontier := [0, 3]

/-- Formula consistency alone accepts this forged component because vertices
`1` and `3` carry the same negative atom label. -/
example :
    forgedRepeatedComponent.FormulaConsistent
      repeatedOccurrenceCertificate := by
  exact ⟨[.atom "p" true, .atom "p" false], rfl, rfl⟩

private theorem no_submitted_axiom_zero_three :
    ¬ ∃ linkIndex : Nat,
      repeatedOccurrenceCertificate.links[linkIndex]? =
        some (Link.axiom 0 3) := by
  rintro ⟨linkIndex, lookup⟩
  have membership :
      (.axiom 0 3 : Link) ∈ repeatedOccurrenceCertificate.links :=
    List.mem_of_getElem? lookup
  have impossible :
      (.axiom 0 3 : Link) ∉ repeatedOccurrenceCertificate.links := by
    native_decide
  exact impossible membership

/-- Occurrence provenance rejects the same-label alias: no submitted axiom
connects the exact certificate vertices `0` and `3`. -/
example :
    ¬ ∃ usedLinks owned,
      Certificate.OccurrenceDerivation repeatedOccurrenceCertificate
        forgedRepeatedComponent.tree forgedRepeatedComponent.frontier
        usedLinks owned := by
  rintro ⟨usedLinks, owned, witness⟩
  cases witness with
  | «axiom» linkIndex left right name positive linkLookup leftFormula =>
      exact no_submitted_axiom_zero_three ⟨linkIndex, linkLookup⟩

/-- A real submitted axiom reservation receives exact local occurrence
provenance, including locally duplicate-free link and vertex ownership. -/
example :
    ∃ after left right name positive,
      repeatedOccurrenceCertificate.reserveAxiomAt?
          repeatedOccurrenceCertificate.initialUnificationState 0 =
        some after ∧
      after.components[
          repeatedOccurrenceCertificate.initialUnificationState
            |>.components.size]? =
        some (some {
          tree := .axiom name positive
          frontier := [left, right] }) ∧
      Certificate.ComponentOccurrenceWitness
        repeatedOccurrenceCertificate
        { tree := .axiom name positive, frontier := [left, right] }
        [0] [left, right] := by
  have success :
      (repeatedOccurrenceCertificate.reserveAxiomAt?
        repeatedOccurrenceCertificate.initialUnificationState 0).isSome =
        true := by
    native_decide
  cases equation :
      repeatedOccurrenceCertificate.reserveAxiomAt?
        repeatedOccurrenceCertificate.initialUnificationState 0 with
  | none =>
      simp [equation] at success
  | some after =>
      rcases
          Certificate.reserveAxiomAt?_componentOccurrenceWitness
            repeatedOccurrenceCertificate_structural equation with
        ⟨left, right, name, positive, linkLookup,
          componentLookup, witness⟩
      exact
        ⟨after, left, right, name, positive, rfl,
          componentLookup, witness⟩

private def crossRepresentativeState : UnificationState where
  marks := #[some 1]
  parents := #[0, 1]
  components := #[
    some forgedRepeatedComponent,
    some forgedRepeatedComponent]
  startedAxioms := 2
  firedConnectives := 0

/-- Forest accounting rejects an owned occurrence whose concrete raw mark
resolves to a different live representative slot. -/
example :
    ¬ Certificate.OwnedOccurrenceAccounted
      crossRepresentativeState 0 forgedRepeatedComponent [0] := by
  intro accounted
  rcases accounted 0 (by simp) with
    ⟨rawAge, markLookup, representative⟩ |
    ⟨unmarked, _frontier⟩
  · have rawAgeEq : 1 = rawAge := by
      simpa [crossRepresentativeState] using markLookup
    subst rawAge
    have representativeSelf :
        crossRepresentativeState.representative 1 = 1 := by
      native_decide
    exact Nat.one_ne_zero
      (representativeSelf.symm.trans representative)
  · have marked :
        crossRepresentativeState.marks[0]? = some (some 1) := by
      rfl
    have impossible := marked.symm.trans unmarked
    simp at impossible

private def orphanMarkedState : UnificationState where
  marks := #[some 0]
  parents := #[0]
  components := #[]
  startedAxioms := 0
  firedConnectives := 0

/-- Reverse forest coverage rejects a concrete raw mark when no live
component at its representative owns that occurrence. -/
example :
    ¬ Certificate.MarkedOccurrencesOwned
      orphanMarkedState (fun _index => []) := by
  intro coverage
  have marked :
      orphanMarkedState.marks[0]? = some (some 0) := by
    rfl
  rcases coverage marked with
    ⟨index, component, _representative, componentLookup, _owned⟩
  simp [orphanMarkedState] at componentLookup

/-- Initialization executes on the smallest valid axiom certificate and its
typed witness establishes the complete state-based scheduler foundation. -/
example :
    SchedulerInvariant axiomCertificate
      (ReservationState.empty axiomCertificate) :=
  empty_schedulerInvariant axiomCertificate_structural

/-- The strengthened empty scheduler invariant exposes an exact empty
occurrence forest, not only formula-level component consistency. -/
example :
    axiomCertificate.ComponentForestProvenance
      axiomCertificate.initialUnificationState :=
  (empty_schedulerInvariant axiomCertificate_structural)
    |>.component_forest_provenance

example :
    ∃ after,
      initializeReservation? axiomCertificate 0 = some after ∧
        SchedulerInvariant axiomCertificate after := by
  have existsResult :
      (initializeReservation? axiomCertificate 0).isSome = true := by
    native_decide
  cases equation :
      initializeReservation? axiomCertificate 0 with
  | none =>
      simp [equation] at existsResult
  | some after =>
      refine ⟨after, rfl, ?_⟩
      rcases initializeReservation?_some_iff.mp equation with ⟨step⟩
      exact step.schedulerInvariant axiomCertificate_structural

/-- Starting from the submitted right endpoint reverses only the scheduler
ready order; the live production frontier retains submitted orientation. -/
example :
    (match initializeReservation? axiomCertificate 1 with
    | none => false
    | some after =>
        after.stack.ready == [[1, 0]] &&
          match after.core.components[0]? with
          | some (some component) =>
              component.frontier == [0, 1]
          | _ => false) = true := by
  native_decide

example :
    ∃ after,
      initializeReservation? axiomCertificate 1 = some after ∧
        SchedulerInvariant axiomCertificate after := by
  have existsResult :
      (initializeReservation? axiomCertificate 1).isSome = true := by
    native_decide
  cases equation :
      initializeReservation? axiomCertificate 1 with
  | none =>
      simp [equation] at existsResult
  | some after =>
      refine ⟨after, rfl, ?_⟩
      rcases initializeReservation?_some_iff.mp equation with ⟨step⟩
      exact step.schedulerInvariant axiomCertificate_structural

private def axiomInitial : Option ReservationState :=
  initializeReservation? axiomCertificate 0

private theorem axiomInitial_schedulerInvariant
    {before : ReservationState}
    (equation : axiomInitial = some before) :
    SchedulerInvariant axiomCertificate before := by
  rcases initializeReservation?_some_iff.mp (by
      simpa [axiomInitial] using equation) with
    ⟨step⟩
  exact step.schedulerInvariant axiomCertificate_structural

/-- The common prepared state has removed exactly the selected endpoint,
marked it at the active raw age, and still satisfies all current state-only
fields of `SchedulerInvariant`. -/
example {before : ReservationState}
    (initialEquation : axiomInitial = some before)
    {prepared : SequentialFigure7.PreparedStep before}
    (_prepareEquation :
      SequentialFigure7.prepare? before = some prepared) :
    SchedulerInvariant axiomCertificate prepared.after := by
  exact prepared.schedulerInvariant
    (axiomInitial_schedulerInvariant initialEquation)

/-- Prepared pop/raw-mark preservation carries the exact component forest
through the newly assigned raw mark. -/
example {before : ReservationState}
    (initialEquation : axiomInitial = some before)
    {prepared : SequentialFigure7.PreparedStep before}
    (_prepareEquation :
      SequentialFigure7.prepare? before = some prepared) :
    axiomCertificate.ComponentForestProvenance prepared.after.core :=
  (prepared.schedulerInvariant
    (axiomInitial_schedulerInvariant initialEquation))
    |>.component_forest_provenance

/-- On an axiom-only certificate the selected endpoint is an exact
conclusion, so executable `concl?` returns precisely the prepared state. -/
example :
    (match initialEquation : axiomInitial with
    | none => false
    | some before =>
        match
            SequentialFigure7.concl? axiomCertificate before
              (axiomInitial_schedulerInvariant initialEquation
                |>.toReservationInvariant) with
        | none => false
        | some after =>
            after.stack.ready == [[1]] &&
              after.stack.marks[0]? == some (some 0) &&
              after.core.marks[0]? == some (some 0) &&
              after.core.firedConnectives == 0) = true := by
  native_decide

example {before after : ReservationState}
    (initialEquation : axiomInitial = some before)
    (conclEquation :
      SequentialFigure7.concl? axiomCertificate before
          (axiomInitial_schedulerInvariant initialEquation
            |>.toReservationInvariant) =
        some after) :
    SchedulerInvariant axiomCertificate after := by
  exact SequentialFigure7.concl?_schedulerInvariant
    (axiomInitial_schedulerInvariant initialEquation) conclEquation

private def parInitial : Option ReservationState :=
  initializeReservation? parCertificate 0

private theorem parInitial_schedulerInvariant
    {before : ReservationState}
    (equation : parInitial = some before) :
    SchedulerInvariant parCertificate before := by
  rcases initializeReservation?_some_iff.mp (by
      simpa [parInitial] using equation) with
    ⟨step⟩
  exact step.schedulerInvariant parCertificate_structural

/-- With the opposite par premise still raw-unmarked, executable `nop?`
performs only the synchronized prepared prefix and preserves the current
state-based scheduler invariant. -/
example :
    (match initialEquation : parInitial with
    | none => false
    | some before =>
        match
            SequentialFigure7.nop? parCertificate before
              (parInitial_schedulerInvariant initialEquation
                |>.toReservationInvariant) with
        | none => false
        | some after =>
            after.stack.ready == [[1]] &&
              after.stack.marks[0]? == some (some 0) &&
              after.core.marks[0]? == some (some 0) &&
              after.core.marks[1]? == some none &&
              after.core.firedConnectives == 0) = true := by
  native_decide

example {before after : ReservationState}
    (initialEquation : parInitial = some before)
    (nopEquation :
      SequentialFigure7.nop? parCertificate before
          (parInitial_schedulerInvariant initialEquation
            |>.toReservationInvariant) =
        some after) :
    SchedulerInvariant parCertificate after := by
  exact SequentialFigure7.nop?_schedulerInvariant
    (parInitial_schedulerInvariant initialEquation) nopEquation

/-- Counter accounting counts logical connective constructors in live trees;
exchange is bookkeeping rather than a firing. -/
example :
    CutFreeDerivation.connectiveCount
      (.exchange [0]
        (.par 0 1 (.axiom "p" true))) = 1 := by
  rfl

private def stackFixture : SequentialStackState where
  marks := #[none, none]
  nextAge := 1
  sigma := [0]
  ready := [[0]]
  waiting := #[.undefined, .undefined]

private def stackExpected : SequentialStackState where
  marks := #[some 0, none]
  nextAge := 1
  sigma := [0]
  ready := [[]]
  waiting := #[.undefined, .undefined]

/-- Popping the last vertex retains the now-empty old top ready bucket. -/
example :
    stackFixture.popReadyMark? =
      .ok {
        vertex := 0
        rawAge := 0
        remainingTop := []
        after := stackExpected } := by
  rfl

/-- Retaining the exhausted bucket is semantic: the next local pop observes
the empty top bucket instead of silently dropping to an older bucket. -/
example :
    stackExpected.popReadyMark? = .error .emptyTopBucket := by
  rfl

private def layeredStackFixture : SequentialStackState where
  marks := Array.replicate 10 none
  nextAge := 4
  sigma := [0, 3]
  ready := [[9], [1, 2]]
  waiting := Array.replicate 10 .undefined

private def layeredStackExpected : SequentialStackState where
  marks :=
    (Array.replicate 10 none).setIfInBounds 1 (some 3)
  nextAge := 4
  sigma := [0, 3]
  ready := [[9], [2]]
  waiting := Array.replicate 10 .undefined

/-- The deterministic refinement selects the head of the last ready bucket and
uses the last sigma boundary; it does not fall back to the older bucket or
boundary at the front of either outer list. -/
example :
    layeredStackFixture.popReadyMark? =
      .ok {
        vertex := 1
        rawAge := 3
        remainingTop := [2]
        after := layeredStackExpected } := by
  rfl

private def stackOutOfBounds : SequentialStackState where
  marks := #[]
  nextAge := 1
  sigma := [0]
  ready := [[7]]
  waiting := #[.undefined]

/-- A missing mark slot is reported as out of bounds, not as unmarked. -/
example :
    stackOutOfBounds.popReadyMark? =
      .error (.markOutOfBounds 7) := by
  rfl

private def stackAlreadyMarked : SequentialStackState where
  marks := #[some 9]
  nextAge := 10
  sigma := [0]
  ready := [[0]]
  waiting := Array.replicate 10 .undefined

/-- An allocated marked slot reports its exact previous raw age. -/
example :
    stackAlreadyMarked.popReadyMark? =
      .error (.alreadyMarked 0 9) := by
  rfl

private def coreFixture : UnificationState where
  marks := #[none, none]
  parents := #[0]
  components := #[none]
  startedAxioms := 1
  firedConnectives := 4

private def coreExpected : UnificationState where
  marks := #[some 0, none]
  parents := #[0]
  components := #[none]
  startedAxioms := 1
  firedConnectives := 4

/-- The production primitive changes only the requested raw mark. -/
example :
    coreFixture.markReadyRaw? 0 0 = .ok coreExpected := by
  rfl

/-- Production out-of-bounds and already-marked failures are distinct. -/
example :
    ({ coreFixture with marks := #[] } :
        UnificationState).markReadyRaw? 0 0 =
      .error (.markOutOfBounds 0) := by
  rfl

example :
    ({ coreFixture with marks := #[some 0] } :
        UnificationState).markReadyRaw? 0 0 =
      .error (.alreadyMarked 0 0) := by
  rfl

end Figure7PrimitivesTests

end ProofNetIR

def main : IO Unit :=
  IO.println "Figure-7 pop/raw-mark primitive tests passed"
