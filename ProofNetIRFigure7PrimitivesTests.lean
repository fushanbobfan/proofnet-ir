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

private def repeatedInitial : Option ReservationState :=
  initializeReservation? repeatedOccurrenceCertificate 0

private theorem repeatedInitial_schedulerInvariant
    {before : ReservationState}
    (equation : repeatedInitial = some before) :
    SchedulerInvariant repeatedOccurrenceCertificate before := by
  rcases initializeReservation?_some_iff.mp (by
      simpa [repeatedInitial] using equation) with
    ⟨step⟩
  exact step.schedulerInvariant repeatedOccurrenceCertificate_structural

/-- A real deterministic `new` transition over repeated formula labels keeps
the two exact submitted axiom occurrences separate.  The fresh ready pair is
inserted after the old ready flattening and before waiting payloads; the old
active waiting cell is initialized empty and the fresh one remains undefined. -/
example :
    (match initialEquation : repeatedInitial with
    | none => false
    | some before =>
        match
            SequentialFigure7.new? repeatedOccurrenceCertificate before
              (repeatedInitial_schedulerInvariant initialEquation
                |>.toReservationInvariant) with
        | none => false
        | some after =>
            after.stack.sigma == [0, 1] &&
              after.stack.ready == [[1], [2, 3]] &&
              after.stack.waiting[0]? ==
                some (.initialized []) &&
              after.stack.waiting[1]? == some .undefined &&
              match after.core.components[0]?, after.core.components[1]? with
              | some (some first), some (some second) =>
                  first.frontier == [0, 1] &&
                    second.frontier == [2, 3]
              | _, _ => false) = true := by
  native_decide

/-- Executable `new?` success preserves the full occurrence-exact scheduler
invariant on the repeated-label regression certificate. -/
example {before after : ReservationState}
    (initialEquation : repeatedInitial = some before)
    (newEquation :
      SequentialFigure7.new? repeatedOccurrenceCertificate before
          (repeatedInitial_schedulerInvariant initialEquation
            |>.toReservationInvariant) =
        some after) :
    SchedulerInvariant repeatedOccurrenceCertificate after := by
  exact SequentialFigure7.new?_schedulerInvariant
    (repeatedInitial_schedulerInvariant initialEquation) newEquation

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

/-! Successful executable Figure-7 `forward` on one active component. -/

/-- The active boundary may be strictly below the mate's raw age and still be
the mate's exact `sigmaBoundary?`.  This is the non-equality interval case
used by the paper's `forward` guard. -/
example : sigmaBoundary? [0] 1 = some 0 := by
  have partition : SigmaAgePartition 2 [0] := by
    exact {
      empty_iff := by simp
      head_zero := by simp
      strictIncreasing := by simp
      boundary_lt := by simp }
  exact partition.sigmaBoundary?_eq_top_of_le
    (active := 0) (age := 1) rfl (by decide) (by decide)

/-- The concrete `init → nop → forward → concl` execution constructs the
submitted par in the active production component, exposes its conclusion on
the top ready bucket, and then raw-marks that conclusion without changing the
logical firing count. -/
example :
    (match initialEquation : parInitial with
    | none => false
    | some initial =>
        let initialInvariant :=
          parInitial_schedulerInvariant initialEquation
        match nopEquation :
            SequentialFigure7.nop? parCertificate initial
              initialInvariant.toReservationInvariant with
        | none => false
        | some afterNop =>
            let nopInvariant :=
              SequentialFigure7.nop?_schedulerInvariant
                initialInvariant nopEquation
            match forwardEquation :
                SequentialFigure7.forward? parCertificate afterNop
                  nopInvariant.toReservationInvariant with
            | none => false
            | some afterForward =>
                let forwardInvariant :=
                  SequentialFigure7.forward?_reservationInvariant
                    nopInvariant.toReservationInvariant forwardEquation
                let forwardComponent :=
                  match afterForward.core.components[0]? with
                  | some (some component) =>
                      component.frontier == [2] &&
                        component.tree ==
                          (.par 0 0 (.axiom "p" true))
                  | _ => false
                afterForward.stack.sigma == [0] &&
                  afterForward.stack.ready == [[2]] &&
                  afterForward.stack.marks ==
                    #[some 0, some 0, none] &&
                  afterForward.core.marks ==
                    #[some 0, some 0, none] &&
                  afterForward.core.startedAxioms == 1 &&
                  afterForward.core.firedConnectives == 1 &&
                  forwardComponent &&
                  match _conclEquation :
                      SequentialFigure7.concl? parCertificate afterForward
                        forwardInvariant with
                  | none => false
                  | some afterConcl =>
                      afterConcl.stack.ready == [[]] &&
                        afterConcl.stack.marks[2]? == some (some 0) &&
                        afterConcl.core.marks[2]? == some (some 0) &&
                        afterConcl.core.firedConnectives == 1) = true := by
  native_decide

/-- The same successful `init → nop → forward` prefix transports the full
state-based invariant.  The exact ready/component correspondence,
occurrence-level forest provenance, and connective-counter equality remain
available through their public invariant fields. -/
example {initial afterNop afterForward afterConcl : ReservationState}
    (initialEquation : parInitial = some initial)
    (nopEquation :
      SequentialFigure7.nop? parCertificate initial
          (parInitial_schedulerInvariant initialEquation
            |>.toReservationInvariant) =
        some afterNop)
    (forwardEquation :
      SequentialFigure7.forward? parCertificate afterNop
          (SequentialFigure7.nop?_schedulerInvariant
            (parInitial_schedulerInvariant initialEquation)
            nopEquation |>.toReservationInvariant) =
        some afterForward)
    (conclEquation :
      SequentialFigure7.concl? parCertificate afterForward
          (SequentialFigure7.forward?_schedulerInvariant
            (SequentialFigure7.nop?_schedulerInvariant
              (parInitial_schedulerInvariant initialEquation)
              nopEquation)
            forwardEquation |>.toReservationInvariant) =
        some afterConcl) :
    SchedulerInvariant parCertificate afterConcl ∧
      SchedulerInvariant parCertificate afterForward ∧
      ReadyBucketFrontierExact afterForward ∧
      parCertificate.ComponentForestProvenance afterForward.core ∧
      FiredCounterExact afterForward := by
  have initialInvariant :=
    parInitial_schedulerInvariant initialEquation
  have nopInvariant :=
    SequentialFigure7.nop?_schedulerInvariant
      initialInvariant nopEquation
  have forwardInvariant :=
    SequentialFigure7.forward?_schedulerInvariant
      nopInvariant forwardEquation
  have conclInvariant :=
    SequentialFigure7.concl?_schedulerInvariant
      forwardInvariant conclEquation
  exact ⟨conclInvariant, forwardInvariant,
    forwardInvariant.ready_bucket_frontier_exact,
    forwardInvariant.component_forest_provenance,
    forwardInvariant.fired_counter_exact⟩

/-! Successful executable Figure-7 `wait` under the full scheduler invariant. -/

/-- Two axiom components are connected so the executable path first records
one par premise with `nop`, then reaches the other component through `new`,
and finally queues the par conclusion at the older raw-age boundary with
`wait`. -/
private def waitSchedulerCertificate : Certificate where
  formulas := #[
    .atom "p" true,
    .atom "p" false,
    .atom "q" true,
    .atom "q" false,
    .par (.atom "q" true) (.atom "p" true),
    .tensor (.atom "p" false)
      (.par (.atom "q" true) (.atom "p" true))]
  links := [
    .axiom 0 1,
    .axiom 2 3,
    .par 2 0 4,
    .tensor 1 4 5]
  conclusions := [3, 5]

private theorem waitSchedulerCertificate_structural :
    waitSchedulerCertificate.StructurallyWellFormed := by
  exact
    (Certificate.wellFormed_iff_structurallyWellFormed
      waitSchedulerCertificate).mp (by native_decide)

private def waitSchedulerInitial : Option ReservationState :=
  initializeReservation? waitSchedulerCertificate 0

private theorem waitSchedulerInitial_schedulerInvariant
    {before : ReservationState}
    (equation : waitSchedulerInitial = some before) :
    SchedulerInvariant waitSchedulerCertificate before := by
  rcases initializeReservation?_some_iff.mp (by
      simpa [waitSchedulerInitial] using equation) with
    ⟨step⟩
  exact step.schedulerInvariant waitSchedulerCertificate_structural

/-- The concrete `init → nop → new → wait` execution places conclusion
`4` in the initialized boundary-`0` waiting cell while leaving the fresh
boundary undefined and the second axiom's partner ready. -/
example :
    (match initialEquation : waitSchedulerInitial with
    | none => false
    | some initial =>
        let initialInvariant :=
          waitSchedulerInitial_schedulerInvariant initialEquation
        match nopEquation :
            SequentialFigure7.nop? waitSchedulerCertificate initial
              initialInvariant.toReservationInvariant with
        | none => false
        | some afterNop =>
            let nopInvariant :=
              SequentialFigure7.nop?_schedulerInvariant
                initialInvariant nopEquation
            match newEquation :
                SequentialFigure7.new? waitSchedulerCertificate afterNop
                  nopInvariant.toReservationInvariant with
            | none => false
            | some afterNew =>
                let newInvariant :=
                  SequentialFigure7.new?_schedulerInvariant
                    nopInvariant newEquation
                match _waitEquation :
                    SequentialFigure7.wait? waitSchedulerCertificate afterNew
                      newInvariant.toReservationInvariant with
                | none => false
                | some afterWait =>
                    afterWait.stack.sigma == [0, 1] &&
                    afterWait.stack.ready == [[], [3]] &&
                    afterWait.stack.waiting[0]? ==
                      some (.initialized [4]) &&
                    afterWait.stack.waiting[1]? == some .undefined &&
                    afterWait.stack.marks ==
                      #[some 0, some 0, some 1, none, none, none] &&
                    afterWait.core.marks == afterWait.stack.marks &&
                    afterWait.core.parents == #[0, 1] &&
                    afterWait.core.startedAxioms == 2 &&
                    afterWait.core.firedConnectives == 0) = true := by
  native_decide

/-- The same successful executable chain transports the complete
occurrence-exact `SchedulerInvariant`, not only `ReservationInvariant`, across
the final `wait`. -/
example {initial afterNop afterNew afterWait : ReservationState}
    (initialEquation : waitSchedulerInitial = some initial)
    (nopEquation :
      SequentialFigure7.nop? waitSchedulerCertificate initial
          (waitSchedulerInitial_schedulerInvariant initialEquation
            |>.toReservationInvariant) =
        some afterNop)
    (newEquation :
      SequentialFigure7.new? waitSchedulerCertificate afterNop
          (SequentialFigure7.nop?_schedulerInvariant
            (waitSchedulerInitial_schedulerInvariant initialEquation)
            nopEquation |>.toReservationInvariant) =
        some afterNew)
    (waitEquation :
      SequentialFigure7.wait? waitSchedulerCertificate afterNew
          (SequentialFigure7.new?_schedulerInvariant
            (SequentialFigure7.nop?_schedulerInvariant
              (waitSchedulerInitial_schedulerInvariant initialEquation)
              nopEquation)
            newEquation |>.toReservationInvariant) =
        some afterWait) :
    SchedulerInvariant waitSchedulerCertificate afterWait := by
  exact SequentialFigure7.wait?_schedulerInvariant
    (SequentialFigure7.new?_schedulerInvariant
      (SequentialFigure7.nop?_schedulerInvariant
        (waitSchedulerInitial_schedulerInvariant initialEquation)
        nopEquation)
      newEquation)
    waitEquation

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
