import ProofNetIR.SequentialSchedulerInvariant
import ProofNetIR.SequentialComponentProvenance
import ProofNetIR.SequentialFigure7UnifyOne
import ProofNetIR.SequentialFigure7Unify
import ProofNetIR.SequentialFigure7UnifyPayload
import ProofNetIR.SequentialFigure7StableEnabled
import ProofNetIR.SequentialFigure7Dispatcher
import ProofNetIR.SequentialFigure7PriorityEnabled
import ProofNetIR.SequentialFigure7NewInputNecessary
import ProofNetIR.SequentialFigure7TagHistory

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

/-- Full state-only validity is a safety condition, not dispatcher progress:
the exact empty scheduler state is invariant-valid and has no enabled rule. -/
example :
    SequentialFigure7.dispatch? axiomCertificate
        (ReservationState.empty axiomCertificate)
        (empty_schedulerInvariant axiomCertificate_structural) = none := by
  native_decide

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

private def repeatedAllTrueTags (state : ReservationState) :
    ReservationState :=
  { state with
    tags := Array.replicate
      repeatedOccurrenceCertificate.formulas.size true }

/-- The state-only scheduler invariant deliberately constrains only the tag
carrier size.  Replacing an initialized carrier by same-sized all-true tags
therefore still satisfies it; exact tag provenance requires the separate
proof-carrying canonical history. -/
example {initial : ReservationState}
    (initialEquation : repeatedInitial = some initial) :
    SchedulerInvariant repeatedOccurrenceCertificate
      (repeatedAllTrueTags initial) := by
  let invariant := repeatedInitial_schedulerInvariant initialEquation
  exact {
    invariant with
    toReservationInvariant := {
      invariant.toReservationInvariant with
      tags_size := by simp [repeatedAllTrueTags] } }

/-- This slice does not claim that the concrete forged state is unreachable.
It does prove the necessary provenance obligation: if an exact canonical
history ended there, every in-bounds all-true tag, including occurrence `4`,
would need a recorded initialization or `new` touch. -/
example {initial : ReservationState}
    {history : SequentialFigure7.ExecutedHistory
      repeatedOccurrenceCertificate (repeatedAllTrueTags initial)}
    (tagHistory : SequentialFigure7.CanonicalTagHistory
      repeatedOccurrenceCertificate history) :
    tagHistory.Touched 4 := by
  apply tagHistory.true_tag_has_touch
  simp [repeatedAllTrueTags, repeatedOccurrenceCertificate]

/-- The canonical dispatcher selects `new` on the first repeated-label state
and then selects only the general `unifyPayload` branch for the empty waiting
payload.  The legacy empty executor is deliberately not a dispatcher tag. -/
example :
    (match initialEquation : repeatedInitial with
    | none => false
    | some initial =>
        let initialInvariant :=
          repeatedInitial_schedulerInvariant initialEquation
        match firstEquation :
            SequentialFigure7.dispatch? repeatedOccurrenceCertificate initial
              initialInvariant with
        | none => false
        | some first =>
            first.kind == .new &&
              first.after.tags != initial.tags &&
              match _secondEquation :
                  SequentialFigure7.dispatch? repeatedOccurrenceCertificate
                    first.after
                    (SequentialFigure7.dispatch?_schedulerInvariant
                      initialInvariant firstEquation) with
              | none => false
              | some second =>
                  second.kind == .unifyPayload &&
                    second.after.tags == first.after.tags) = true := by
  native_decide

/-- A successful canonical dispatch has its exact priority-aware witness,
preserves the complete invariant, and extends the certified execution trace. -/
example {initial : ReservationState}
    {result : SequentialFigure7.Figure7DispatchResult}
    (initialEquation : repeatedInitial = some initial)
    (dispatchEquation :
      SequentialFigure7.dispatch? repeatedOccurrenceCertificate initial
          (repeatedInitial_schedulerInvariant initialEquation) =
        some result) :
    Nonempty
        (SequentialFigure7.DispatchStep repeatedOccurrenceCertificate initial
          (repeatedInitial_schedulerInvariant initialEquation) result) ∧
      SchedulerInvariant repeatedOccurrenceCertificate result.after ∧
      SequentialFigure7.ReachableByImplementedDispatcher
        repeatedOccurrenceCertificate result.after := by
  let invariant := repeatedInitial_schedulerInvariant initialEquation
  have typed :=
    (SequentialFigure7.dispatch?_some_iff invariant).mp dispatchEquation
  have afterInvariant :=
    SequentialFigure7.dispatch?_schedulerInvariant invariant dispatchEquation
  have initialized :
      SequentialFigure7.ReachableByImplementedDispatcher
        repeatedOccurrenceCertificate initial :=
    SequentialFigure7.dispatcher_reachable_of_initializeReservation?_eq_some
      (by simpa [repeatedInitial] using initialEquation)
  have reachable := initialized.dispatch invariant dispatchEquation
  exact ⟨typed, afterInvariant, reachable⟩

/-- Every exact canonical dispatcher success has branch-aligned tag evidence
and pointwise extends the input tag carrier. -/
example {initial : ReservationState}
    {result : SequentialFigure7.Figure7DispatchResult}
    (initialEquation : repeatedInitial = some initial)
    (dispatchEquation :
      SequentialFigure7.dispatch? repeatedOccurrenceCertificate initial
          (repeatedInitial_schedulerInvariant initialEquation) =
        some result) :
    Nonempty
        (SequentialFigure7.DispatchTagEvidence
          repeatedOccurrenceCertificate initial result) ∧
      SequentialFigure7.TagsExtend initial.tags result.after.tags := by
  let invariant := repeatedInitial_schedulerInvariant initialEquation
  rcases (SequentialFigure7.dispatch?_some_iff invariant).mp
      dispatchEquation with
    ⟨dispatchStep⟩
  rcases dispatchStep.tagEvidence with ⟨evidence⟩
  exact ⟨⟨evidence⟩, evidence.tagsExtend⟩

/-- The exact initialized/dispatcher history admits canonical tag facts:
current true tags are precisely recorded touches and submitted axiom slots do
not repeat. -/
example {initial : ReservationState}
    {result : SequentialFigure7.Figure7DispatchResult}
    (initialEquation : repeatedInitial = some initial)
    (dispatchEquation :
      SequentialFigure7.dispatch? repeatedOccurrenceCertificate initial
          (repeatedInitial_schedulerInvariant initialEquation) =
        some result) :
    ∃ (history :
        SequentialFigure7.ExecutedHistory repeatedOccurrenceCertificate
          result.after)
      (tagHistory :
        SequentialFigure7.CanonicalTagHistory repeatedOccurrenceCertificate
          history),
      tagHistory.linkIndices.Nodup ∧
        ∀ vertex,
          result.after.tags[vertex]? = some true ↔
            tagHistory.Touched vertex := by
  let invariant := repeatedInitial_schedulerInvariant initialEquation
  rcases initializeReservation?_some_iff.mp (by
      simpa [repeatedInitial] using initialEquation) with
    ⟨initialStep⟩
  rcases (SequentialFigure7.dispatch?_some_iff invariant).mp
      dispatchEquation with
    ⟨dispatchStep⟩
  let history :=
    SequentialFigure7.ExecutedHistory.later
      (SequentialFigure7.ExecutedHistory.init initialStep)
      invariant dispatchStep
  rcases history.hasCanonicalTagHistory with ⟨tagHistory⟩
  exact ⟨history, tagHistory, tagHistory.linkIndices_nodup,
    fun _vertex ↦ tagHistory.tagged_iff_touched⟩

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

/-! Bounded empty-waiting-cell Figure-7 `unify`. -/

/-- The concrete `init → new → unifyEmpty` path merges the two submitted
axiom components through the exact tensor occurrence.  The previous and
active ready buckets are combined in the project's deterministic order, the
old empty waiting cell is drained to `undefined`, and the raw allocation
horizon remains unchanged. -/
private def repeatedEmptyUnifyTransition : Option ReservationState :=
  match initialEquation : repeatedInitial with
  | none => none
  | some initial =>
      let initialInvariant :=
        repeatedInitial_schedulerInvariant initialEquation
      match newEquation :
          SequentialFigure7.new? repeatedOccurrenceCertificate initial
            initialInvariant.toReservationInvariant with
      | none => none
      | some before =>
          let beforeInvariant :=
            SequentialFigure7.new?_schedulerInvariant
              initialInvariant newEquation
          SequentialFigure7.unifyEmpty?
            repeatedOccurrenceCertificate before
            beforeInvariant.toReservationInvariant

example :
    (match repeatedEmptyUnifyTransition with
    | none => false
    | some after =>
        after.stack.sigma == [0] &&
          after.stack.nextAge == 2 &&
          after.stack.ready == [[4, 1, 3]] &&
          after.stack.waiting[0]? == some .undefined &&
          after.stack.waiting[1]? == some .undefined &&
          after.stack.marks ==
            #[some 0, none, some 1, none, none] &&
          after.core.marks == after.stack.marks &&
          after.core.parents == #[0, 0] &&
          after.core.representative 0 == 0 &&
          after.core.representative 1 == 0 &&
          after.core.startedAxioms == 2 &&
          after.core.firedConnectives == 1 &&
          match after.core.components[0]?, after.core.components[1]? with
          | some (some component), some none =>
              component.frontier == [4, 1, 3]
          | _, _ => false) = true := by
  native_decide

/-- Starting from the opposite submitted axiom makes the later selected
tensor occurrence the stored-left premise.  The same raw-age bridge therefore
returns `(leftToken, rightToken) = (active, previous)` while the scheduler
ready merge retains its own search-oriented order. -/
private def repeatedStoredLeftInitial : Option ReservationState :=
  initializeReservation? repeatedOccurrenceCertificate 2

private theorem repeatedStoredLeftInitial_schedulerInvariant
    {before : ReservationState}
    (equation : repeatedStoredLeftInitial = some before) :
    SchedulerInvariant repeatedOccurrenceCertificate before := by
  rcases initializeReservation?_some_iff.mp (by
      simpa [repeatedStoredLeftInitial] using equation) with
    ⟨step⟩
  exact step.schedulerInvariant repeatedOccurrenceCertificate_structural

private def repeatedStoredLeftUnifyTransition :
    Option ReservationState :=
  match initialEquation : repeatedStoredLeftInitial with
  | none => none
  | some initial =>
      let initialInvariant :=
        repeatedStoredLeftInitial_schedulerInvariant initialEquation
      match newEquation :
          SequentialFigure7.new? repeatedOccurrenceCertificate initial
            initialInvariant.toReservationInvariant with
      | none => none
      | some before =>
          SequentialFigure7.unifyEmpty?
            repeatedOccurrenceCertificate before
            (SequentialFigure7.new?_schedulerInvariant
              initialInvariant newEquation |>.toReservationInvariant)

example :
    (match repeatedStoredLeftUnifyTransition with
    | none => false
    | some after =>
        after.stack.sigma == [0] &&
          after.stack.nextAge == 2 &&
          after.stack.ready == [[4, 3, 1]] &&
          after.stack.waiting[0]? == some .undefined &&
          after.stack.waiting[1]? == some .undefined &&
          after.core.parents == #[0, 0] &&
          after.core.representative 0 == 0 &&
          after.core.representative 1 == 0 &&
          after.core.startedAxioms == 2 &&
          after.core.firedConnectives == 1 &&
          match after.core.components[0]?, after.core.components[1]? with
          | some (some component), some none =>
              component.frontier == [4, 1, 3]
          | _, _ => false) = true := by
  native_decide

/-- The stored-left execution reaches the complete scheduler invariant through
the empty-only executable preservation theorem. -/
example {initial before after : ReservationState}
    (initialEquation : repeatedStoredLeftInitial = some initial)
    (newEquation :
      SequentialFigure7.new? repeatedOccurrenceCertificate initial
          (repeatedStoredLeftInitial_schedulerInvariant initialEquation
            |>.toReservationInvariant) =
        some before)
    (unifyEquation :
      SequentialFigure7.unifyEmpty? repeatedOccurrenceCertificate before
          (SequentialFigure7.new?_schedulerInvariant
            (repeatedStoredLeftInitial_schedulerInvariant initialEquation)
            newEquation |>.toReservationInvariant) =
        some after) :
    SchedulerInvariant repeatedOccurrenceCertificate after :=
  SequentialFigure7.unifyEmpty?_schedulerInvariant
    (SequentialFigure7.new?_schedulerInvariant
      (repeatedStoredLeftInitial_schedulerInvariant initialEquation)
      newEquation)
    unifyEquation

/-- The stored-right regression observes the exact executable orientation
before the empty-only merge, then checks the merged frontier, representative
collapse, scheduler queues, waiting cells, and both counters. -/
private def repeatedStoredRightOrientationRegression : Bool :=
  match initialEquation : repeatedInitial with
  | none => false
  | some initial =>
      let initialInvariant :=
        repeatedInitial_schedulerInvariant initialEquation
      match newEquation :
          SequentialFigure7.new? repeatedOccurrenceCertificate initial
            initialInvariant.toReservationInvariant with
      | none => false
      | some before =>
          let beforeInvariant :=
            SequentialFigure7.new?_schedulerInvariant
              initialInvariant newEquation
          match SequentialFigure7.prepare? before with
          | none => false
          | some prepared =>
              match repeatedOccurrenceCertificate.connectiveBelow?
                  prepared.stackResult.vertex with
              | none => false
              | some consumer =>
                  match prepared.coreMarked.unifyTokens?
                      consumer.storedLeft consumer.storedRight
                      consumer.conclusion with
                  | none => false
                  | some (leftToken, rightToken) =>
                      match SequentialFigure7.unifyEmpty?
                          repeatedOccurrenceCertificate before
                          beforeInvariant.toReservationInvariant with
                      | none => false
                      | some after =>
                          consumer.side == .storedRight &&
                            consumer.linkIndex == 2 &&
                            consumer.storedLeft == 0 &&
                            consumer.storedRight == 2 &&
                            consumer.conclusion == 4 &&
                            prepared.stackResult.rawAge == 1 &&
                            leftToken == 0 &&
                            rightToken == 1 &&
                            prepared.stackResult.after.waiting[0]? ==
                              some (.initialized []) &&
                            after.stack.sigma == [0] &&
                            after.stack.ready == [[4, 1, 3]] &&
                            after.stack.waiting[0]? == some .undefined &&
                            after.stack.waiting[1]? == some .undefined &&
                            after.core.representative 0 == 0 &&
                            after.core.representative 1 == 0 &&
                            after.core.startedAxioms == 2 &&
                            after.core.firedConnectives == 1 &&
                            match after.core.components[0]?,
                                after.core.components[1]? with
                            | some (some component), some none =>
                                component.frontier == [4, 1, 3]
                            | _, _ => false

example : repeatedStoredRightOrientationRegression = true := by
  native_decide

/-- Reversing the initial axiom selects the stored-left tensor premise.  The
production frontier remains in submitted left/right order even though the
scheduler merge keeps previous-ready before active-ready. -/
private def repeatedStoredLeftOrientationRegression : Bool :=
  match initialEquation : repeatedStoredLeftInitial with
  | none => false
  | some initial =>
      let initialInvariant :=
        repeatedStoredLeftInitial_schedulerInvariant initialEquation
      match newEquation :
          SequentialFigure7.new? repeatedOccurrenceCertificate initial
            initialInvariant.toReservationInvariant with
      | none => false
      | some before =>
          let beforeInvariant :=
            SequentialFigure7.new?_schedulerInvariant
              initialInvariant newEquation
          match SequentialFigure7.prepare? before with
          | none => false
          | some prepared =>
              match repeatedOccurrenceCertificate.connectiveBelow?
                  prepared.stackResult.vertex with
              | none => false
              | some consumer =>
                  match prepared.coreMarked.unifyTokens?
                      consumer.storedLeft consumer.storedRight
                      consumer.conclusion with
                  | none => false
                  | some (leftToken, rightToken) =>
                      match SequentialFigure7.unifyEmpty?
                          repeatedOccurrenceCertificate before
                          beforeInvariant.toReservationInvariant with
                      | none => false
                      | some after =>
                          consumer.side == .storedLeft &&
                            consumer.linkIndex == 2 &&
                            consumer.storedLeft == 0 &&
                            consumer.storedRight == 2 &&
                            consumer.conclusion == 4 &&
                            prepared.stackResult.rawAge == 1 &&
                            leftToken == 1 &&
                            rightToken == 0 &&
                            prepared.stackResult.after.waiting[0]? ==
                              some (.initialized []) &&
                            after.stack.sigma == [0] &&
                            after.stack.ready == [[4, 3, 1]] &&
                            after.stack.waiting[0]? == some .undefined &&
                            after.stack.waiting[1]? == some .undefined &&
                            after.core.representative 0 == 0 &&
                            after.core.representative 1 == 0 &&
                            after.core.startedAxioms == 2 &&
                            after.core.firedConnectives == 1 &&
                            match after.core.components[0]?,
                                after.core.components[1]? with
                            | some (some component), some none =>
                                component.frontier == [4, 1, 3]
                            | _, _ => false

example : repeatedStoredLeftOrientationRegression = true := by
  native_decide

/-- Three independently reserved axiom components expose why the lower raw
age guard is not redundant.  The first component is marked at age `0`, a
middle component is reserved at age `1`, and the selected tensor premise is
reserved at age `2`.  The low-level production primitive can merge tokens
`0` and `2`, but Figure 7 must reject it because the mate is not in the
immediately previous interval: `1 ≤ 0` is false.

This fixture is reached through the exact public prepare/reservation
primitives and carries a genuine `ReservationInvariant`; it is not claimed
to be a full-rule `SchedulerInvariant` history. -/
private def nonadjacentMateCertificate : Certificate where
  formulas := #[
    .atom "p" true,
    .atom "p" false,
    .atom "r" true,
    .atom "r" false,
    .atom "q" true,
    .atom "q" false,
    .tensor (.atom "p" true) (.atom "q" true)]
  links := [
    .axiom 0 1,
    .axiom 2 3,
    .axiom 4 5,
    .tensor 0 4 6]
  conclusions := [1, 2, 3, 5, 6]

private def nonadjacentMateGuardRegression : Bool :=
  match initialEquation :
      initializeReservation? nonadjacentMateCertificate 0 with
  | none => false
  | some initial =>
      let initialInvariant :
          ReservationInvariant nonadjacentMateCertificate initial := by
        rcases initializeReservation?_some_iff.mp initialEquation with
          ⟨step⟩
        exact step.reservationInvariant
      match prepareEquation : SequentialFigure7.prepare? initial with
      | none => false
      | some preparedInitial =>
          let preparedInvariant :=
            preparedInitial.reservationInvariant initialInvariant
          match secondEquation :
              reserveNewAxiom? nonadjacentMateCertificate
                preparedInitial.after 2 with
          | none => false
          | some afterSecond =>
              let secondInvariant :
                  ReservationInvariant nonadjacentMateCertificate
                    afterSecond := by
                rcases reserveNewAxiom?_some_iff.mp secondEquation with
                  ⟨step⟩
                exact step.reservationInvariant preparedInvariant
              match thirdEquation :
                  reserveNewAxiom? nonadjacentMateCertificate
                    afterSecond 4 with
              | none => false
              | some before =>
                  let beforeInvariant :
                      ReservationInvariant nonadjacentMateCertificate
                        before := by
                    rcases reserveNewAxiom?_some_iff.mp thirdEquation with
                      ⟨step⟩
                    exact step.reservationInvariant secondInvariant
                  match SequentialFigure7.prepare? before with
                  | none => false
                  | some preparedFinal =>
                      match
                          nonadjacentMateCertificate.connectiveBelow?
                            preparedFinal.stackResult.vertex with
                      | none => false
                      | some consumer =>
                          before.stack.sigma == [0, 1, 2] &&
                            preparedFinal.stackResult.vertex == 4 &&
                            preparedFinal.stackResult.rawAge == 2 &&
                            consumer.kind == .tensor &&
                            consumer.linkIndex == 3 &&
                            consumer.storedLeft == 0 &&
                            consumer.storedRight == 4 &&
                            consumer.conclusion == 6 &&
                            consumer.side == .storedRight &&
                            consumer.mate == 0 &&
                            before.stack.marks[0]? == some (some 0) &&
                            (preparedFinal.stackResult.after.sigma.dropLast.getLast? ==
                              some 1) &&
                            preparedFinal.stackResult.after.waiting[1]? ==
                                some (.initialized []) &&
                            decide (0 < preparedFinal.stackResult.rawAge) &&
                            !(decide ((1 : Nat) ≤ 0)) &&
                            (Certificate.queueTensor?
                              preparedFinal.coreMarked 0 4 6).isSome &&
                            (SequentialFigure7.unifyEmpty?
                              nonadjacentMateCertificate before
                              beforeInvariant).isNone

example : nonadjacentMateGuardRegression = true := by
  native_decide

/-- The strict upper raw-age guard is independently observable.  Two axiom
components are reserved at ages `0` and `1`; one endpoint of the second axiom
is then prepared and marked at the active age `1`.  Preparing its tensor mate
therefore exposes `μ(mate) = i = 1`: the lower guard `0 ≤ 1` holds, but the
paper's strict upper guard `1 < 1` fails.  The state carries a genuine
`ReservationInvariant`, although this direct reservation fixture is not
claimed to be a full-rule `SchedulerInvariant` history. -/
private def sameAgeMateCertificate : Certificate where
  formulas := #[
    .atom "p" true,
    .atom "p" false,
    .atom "q" true,
    .atom "q" false,
    .tensor (.atom "q" true) (.atom "q" false)]
  links := [
    .axiom 0 1,
    .axiom 2 3,
    .tensor 2 3 4]
  conclusions := [0, 1, 4]

private def sameAgeMateUpperGuardRegression : Bool :=
  match initialEquation :
      initializeReservation? sameAgeMateCertificate 0 with
  | none => false
  | some initial =>
      let initialInvariant :
          ReservationInvariant sameAgeMateCertificate initial := by
        rcases initializeReservation?_some_iff.mp initialEquation with
          ⟨step⟩
        exact step.reservationInvariant
      match prepareEquation : SequentialFigure7.prepare? initial with
      | none => false
      | some preparedInitial =>
          let preparedInvariant :=
            preparedInitial.reservationInvariant initialInvariant
          match reserveEquation :
              reserveNewAxiom? sameAgeMateCertificate
                preparedInitial.after 2 with
          | none => false
          | some before =>
              let beforeInvariant :
                  ReservationInvariant sameAgeMateCertificate before := by
                rcases reserveNewAxiom?_some_iff.mp reserveEquation with
                  ⟨step⟩
                exact step.reservationInvariant preparedInvariant
              match mateEquation : SequentialFigure7.prepare? before with
              | none => false
              | some markedMate =>
                  let markedInvariant :=
                    markedMate.reservationInvariant beforeInvariant
                  match SequentialFigure7.prepare? markedMate.after with
                  | none => false
                  | some selected =>
                      match
                          sameAgeMateCertificate.connectiveBelow?
                            selected.stackResult.vertex with
                      | none => false
                      | some consumer =>
                          before.stack.sigma == [0, 1] &&
                            markedMate.stackResult.vertex == 2 &&
                            markedMate.stackResult.rawAge == 1 &&
                            selected.stackResult.vertex == 3 &&
                            selected.stackResult.rawAge == 1 &&
                            consumer.kind == .tensor &&
                            consumer.linkIndex == 2 &&
                            consumer.storedLeft == 2 &&
                            consumer.storedRight == 3 &&
                            consumer.conclusion == 4 &&
                            consumer.mate == 2 &&
                            markedMate.after.core.marks[2]? ==
                              some (some 1) &&
                            (markedMate.after.stack.sigma.dropLast.getLast? ==
                              some 0) &&
                            decide ((0 : Nat) ≤ 1) &&
                            !(decide ((1 : Nat) < 1)) &&
                            (SequentialFigure7.unifyEmpty?
                              sameAgeMateCertificate markedMate.after
                              markedInvariant).isNone

example : sameAgeMateUpperGuardRegression = true := by
  native_decide

/-- Executable success exposes the exact submitted tensor index/orientation
and the literal raw-age guard `j ≤ μ(u₂) < i`; neither fact is reconstructed
from erased formula labels. -/
example {initial before after : ReservationState}
    (initialEquation : repeatedInitial = some initial)
    (newEquation :
      SequentialFigure7.new? repeatedOccurrenceCertificate initial
          (repeatedInitial_schedulerInvariant initialEquation
            |>.toReservationInvariant) =
        some before)
    (unifyEquation :
      SequentialFigure7.unifyEmpty? repeatedOccurrenceCertificate before
          (SequentialFigure7.new?_schedulerInvariant
            (repeatedInitial_schedulerInvariant initialEquation)
            newEquation |>.toReservationInvariant) =
        some after) :
    ∃ step : SequentialFigure7.UnifyEmptyStep
        repeatedOccurrenceCertificate before after,
      repeatedOccurrenceCertificate.links[step.consumer.linkIndex]? =
          some (.tensor step.consumer.storedLeft
            step.consumer.storedRight step.consumer.conclusion) ∧
        step.previousBoundary ≤ step.mateRawAge ∧
        step.mateRawAge < step.prepared.stackResult.rawAge := by
  let invariant :=
    SequentialFigure7.new?_schedulerInvariant
      (repeatedInitial_schedulerInvariant initialEquation) newEquation
      |>.toReservationInvariant
  rcases
      (SequentialFigure7.unifyEmpty?_some_iff invariant).mp
        unifyEquation with
    ⟨step⟩
  exact ⟨step, step.submitted_tensor, step.lower, step.upper⟩

/-- The stored-right bounded executable success preserves the complete
occurrence-exact scheduler invariant, not only its reservation sub-bundle. -/
example {initial before after : ReservationState}
    (initialEquation : repeatedInitial = some initial)
    (newEquation :
      SequentialFigure7.new? repeatedOccurrenceCertificate initial
          (repeatedInitial_schedulerInvariant initialEquation
            |>.toReservationInvariant) =
        some before)
    (unifyEquation :
      SequentialFigure7.unifyEmpty? repeatedOccurrenceCertificate before
          (SequentialFigure7.new?_schedulerInvariant
            (repeatedInitial_schedulerInvariant initialEquation)
            newEquation |>.toReservationInvariant) =
        some after) :
    SchedulerInvariant repeatedOccurrenceCertificate after :=
  SequentialFigure7.unifyEmpty?_schedulerInvariant
    (SequentialFigure7.new?_schedulerInvariant
      (repeatedInitial_schedulerInvariant initialEquation) newEquation)
    unifyEquation

/-- A nonempty `W(j)` is rejected fail-closed.  The payload is installed by
the existing `ReservationInvariant`-preserving waiting primitive, so this
regression does not rely on a forged proof argument or an ill-shaped
reservation state.  It is not claimed to be a genuine waiting-par history or
a state satisfying the stronger full `SchedulerInvariant`. -/
private def repeatedNonemptyWaitingUnifyAttempt :
    Option ReservationState :=
  match initialEquation : repeatedInitial with
  | none => none
  | some initial =>
      let initialInvariant :=
        repeatedInitial_schedulerInvariant initialEquation
      match newEquation :
          SequentialFigure7.new? repeatedOccurrenceCertificate initial
            initialInvariant.toReservationInvariant with
      | none => none
      | some before =>
          let beforeInvariant :=
            SequentialFigure7.new?_schedulerInvariant
              initialInvariant newEquation
              |>.toReservationInvariant
          match payloadEquation :
              enqueueWaitingAtRawAge? before 0 4 with
          | none => none
          | some withPayload =>
              let payloadInvariant :=
                enqueueWaitingAtRawAge?_reservationInvariant
                  beforeInvariant payloadEquation
              SequentialFigure7.unifyEmpty?
                repeatedOccurrenceCertificate withPayload payloadInvariant

example : repeatedNonemptyWaitingUnifyAttempt.isNone = true := by
  native_decide

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

/-- The deterministic dispatcher itself drives the complete
`init → nop → forward → concl` fixture and exposes the expected rule tags. -/
example :
    (match initialEquation : parInitial with
    | none => false
    | some initial =>
        let initialInvariant :=
          parInitial_schedulerInvariant initialEquation
        match nopEquation :
            SequentialFigure7.dispatch? parCertificate initial initialInvariant with
        | none => false
        | some afterNop =>
            afterNop.kind == .nop &&
              afterNop.after.tags == initial.tags &&
              let nopInvariant :=
                SequentialFigure7.dispatch?_schedulerInvariant
                  initialInvariant nopEquation
              match forwardEquation :
                  SequentialFigure7.dispatch? parCertificate afterNop.after
                    nopInvariant with
              | none => false
              | some afterForward =>
                  afterForward.kind == .forward &&
                    afterForward.after.tags == afterNop.after.tags &&
                    let forwardInvariant :=
                      SequentialFigure7.dispatch?_schedulerInvariant
                        nopInvariant forwardEquation
                    match SequentialFigure7.dispatch? parCertificate
                        afterForward.after forwardInvariant with
                    | none => false
                    | some afterConcl =>
                        afterConcl.kind == .concl &&
                          afterConcl.after.tags ==
                            afterForward.after.tags) = true := by
  native_decide

/-! Independent Boolean-free Figure-7 `forward` correspondence. -/

/-- Equality is admitted by the paper's non-strict guard: after `nop` marks
stored-left premise `0` at raw age `0`, the selected stored-right premise `1`
is also assigned active age `0` and `forward?` succeeds. -/
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
        | some before =>
            let nopInvariant :=
              SequentialFigure7.nop?_schedulerInvariant
                initialInvariant nopEquation
            before.stack.marks == #[some 0, none, none] &&
              match SequentialFigure7.forward? parCertificate before
                  nopInvariant.toReservationInvariant with
              | none => false
              | some after =>
                  after.stack.marks == #[some 0, some 0, none]) = true := by
  native_decide

/-- The canonical executable stored-right `forward` refines the direct rule. -/
example {initial before after : ReservationState}
    (initialEquation : parInitial = some initial)
    (nopEquation :
      SequentialFigure7.nop? parCertificate initial
          (parInitial_schedulerInvariant initialEquation
            |>.toReservationInvariant) =
        some before)
    (forwardEquation :
      SequentialFigure7.forward? parCertificate before
          (SequentialFigure7.nop?_schedulerInvariant
            (parInitial_schedulerInvariant initialEquation)
            nopEquation |>.toReservationInvariant) =
        some after) :
    SequentialFigure7.ForwardRule parCertificate before after := by
  exact SequentialFigure7.forward?_sound
    (SequentialFigure7.nop?_schedulerInvariant
      (parInitial_schedulerInvariant initialEquation) nopEquation
      |>.toReservationInvariant)
    forwardEquation

/-- A direct stored-right `ForwardRule` witness reconstructs the exact
executable output from the complete scheduler invariant. -/
example {initial before after : ReservationState}
    (initialEquation : parInitial = some initial)
    (nopEquation :
      SequentialFigure7.nop? parCertificate initial
          (parInitial_schedulerInvariant initialEquation
            |>.toReservationInvariant) =
        some before)
    (rule : SequentialFigure7.ForwardRule parCertificate before after) :
    SequentialFigure7.forward? parCertificate before
        (SequentialFigure7.nop?_schedulerInvariant
          (parInitial_schedulerInvariant initialEquation)
          nopEquation |>.toReservationInvariant) =
      some after := by
  exact SequentialFigure7.forward?_complete_of_schedulerInvariant
    (SequentialFigure7.nop?_schedulerInvariant
      (parInitial_schedulerInvariant initialEquation) nopEquation)
    rule

/-- The executable and independent direct stored-right `forward` relations
are exactly equivalent; this remains a successful-rule theorem, not progress. -/
example {initial before after : ReservationState}
    (initialEquation : parInitial = some initial)
    (nopEquation :
      SequentialFigure7.nop? parCertificate initial
          (parInitial_schedulerInvariant initialEquation
            |>.toReservationInvariant) =
        some before) :
    SequentialFigure7.forward? parCertificate before
          (SequentialFigure7.nop?_schedulerInvariant
            (parInitial_schedulerInvariant initialEquation)
            nopEquation |>.toReservationInvariant) =
        some after ↔
      SequentialFigure7.ForwardRule parCertificate before after := by
  exact SequentialFigure7.forward?_some_iff_rule_of_schedulerInvariant
    (SequentialFigure7.nop?_schedulerInvariant
      (parInitial_schedulerInvariant initialEquation) nopEquation)

/-- The reachable full scheduler invariant discharges the separately stated
ready-list representation condition used by executable completeness. -/
example {initial before : ReservationState}
    (initialEquation : parInitial = some initial)
    (nopEquation :
      SequentialFigure7.nop? parCertificate initial
          (parInitial_schedulerInvariant initialEquation
            |>.toReservationInvariant) =
        some before) :
    SequentialFigure7.ForwardExecutableReadyNodup
      parCertificate before := by
  exact SequentialFigure7.SchedulerInvariant.forwardExecutableReadyNodup
    (SequentialFigure7.nop?_schedulerInvariant
      (parInitial_schedulerInvariant initialEquation) nopEquation)

/-- On the invariant-carrying stored-right fixture, two direct rule witnesses
have the same complete output state. -/
example {initial before first second : ReservationState}
    (initialEquation : parInitial = some initial)
    (nopEquation :
      SequentialFigure7.nop? parCertificate initial
          (parInitial_schedulerInvariant initialEquation
            |>.toReservationInvariant) =
        some before)
    (left : SequentialFigure7.ForwardRule parCertificate before first)
    (right : SequentialFigure7.ForwardRule parCertificate before second) :
    first = second := by
  have invariant := SequentialFigure7.nop?_schedulerInvariant
    (parInitial_schedulerInvariant initialEquation) nopEquation
  exact SequentialFigure7.ForwardRule.output_unique_of_structural
    invariant.structural invariant.toReservationInvariant
    (SequentialFigure7.SchedulerInvariant.forwardExecutableReadyNodup
      invariant) left right

/-- Starting from the submitted right axiom endpoint reverses scheduler
orientation.  After `nop` selects stored-right premise `1`, `forward` selects
stored-left premise `0`, while the production frontier remains submitted. -/
private def parStoredRightInitial : Option ReservationState :=
  initializeReservation? parCertificate 1

private theorem parStoredRightInitial_schedulerInvariant
    {before : ReservationState}
    (equation : parStoredRightInitial = some before) :
    SchedulerInvariant parCertificate before := by
  rcases initializeReservation?_some_iff.mp (by
      simpa [parStoredRightInitial] using equation) with
    ⟨step⟩
  exact step.schedulerInvariant parCertificate_structural

example :
    (match initialEquation : parStoredRightInitial with
    | none => false
    | some initial =>
        let initialInvariant :=
          parStoredRightInitial_schedulerInvariant initialEquation
        match nopEquation :
            SequentialFigure7.nop? parCertificate initial
              initialInvariant.toReservationInvariant with
        | none => false
        | some before =>
            let nopInvariant :=
              SequentialFigure7.nop?_schedulerInvariant
                initialInvariant nopEquation
            before.stack.ready == [[0]] &&
              before.stack.marks == #[none, some 0, none] &&
              match SequentialFigure7.forward? parCertificate before
                  nopInvariant.toReservationInvariant with
              | none => false
              | some after =>
                  after.stack.ready == [[2]] &&
                    after.stack.marks == #[some 0, some 0, none] &&
                    after.core.firedConnectives == 1 &&
                    match after.core.components[0]? with
                    | some (some component) =>
                        component.frontier == [2] &&
                          component.tree ==
                            (.par 0 0 (.axiom "p" true))
                    | _ => false) = true := by
  native_decide

/-- The stored-left orientation uses the same direct/executable theorem. -/
example {initial before after : ReservationState}
    (initialEquation : parStoredRightInitial = some initial)
    (nopEquation :
      SequentialFigure7.nop? parCertificate initial
          (parStoredRightInitial_schedulerInvariant initialEquation
            |>.toReservationInvariant) =
        some before) :
    SequentialFigure7.forward? parCertificate before
          (SequentialFigure7.nop?_schedulerInvariant
            (parStoredRightInitial_schedulerInvariant initialEquation)
            nopEquation |>.toReservationInvariant) =
        some after ↔
      SequentialFigure7.ForwardRule parCertificate before after := by
  exact SequentialFigure7.forward?_some_iff_rule_of_schedulerInvariant
    (SequentialFigure7.nop?_schedulerInvariant
      (parStoredRightInitial_schedulerInvariant initialEquation) nopEquation)

/-- Before either premise has been marked, `forward?` rejects the unmarked
mate and leaves the same state to the `nop?` branch. -/
example :
    (match initialEquation : parInitial with
    | none => false
    | some before =>
        (SequentialFigure7.forward? parCertificate before
          (parInitial_schedulerInvariant initialEquation
            |>.toReservationInvariant)).isNone) = true := by
  native_decide

/-- A tensor consumer is not silently accepted by the par-only `forward?`
branch, even when the selected occurrence has a full scheduler invariant. -/
example :
    (match initialEquation : repeatedInitial with
    | none => false
    | some before =>
        (SequentialFigure7.forward? repeatedOccurrenceCertificate before
          (repeatedInitial_schedulerInvariant initialEquation
            |>.toReservationInvariant)).isNone) = true := by
  native_decide

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

/-- Dispatcher precedence follows the genuine `nop → new → wait` execution;
the final par step is not misclassified as `forward` or unification. -/
example :
    (match initialEquation : waitSchedulerInitial with
    | none => false
    | some initial =>
        let initialInvariant :=
          waitSchedulerInitial_schedulerInvariant initialEquation
        match nopEquation :
            SequentialFigure7.dispatch? waitSchedulerCertificate initial
              initialInvariant with
        | none => false
        | some afterNop =>
            afterNop.kind == .nop &&
              afterNop.after.tags == initial.tags &&
              let nopInvariant :=
                SequentialFigure7.dispatch?_schedulerInvariant
                  initialInvariant nopEquation
              match newEquation :
                  SequentialFigure7.dispatch? waitSchedulerCertificate
                    afterNop.after nopInvariant with
              | none => false
              | some afterNew =>
                  afterNew.kind == .new &&
                    afterNew.after.tags != afterNop.after.tags &&
                    let newInvariant :=
                      SequentialFigure7.dispatch?_schedulerInvariant
                        nopInvariant newEquation
                    match SequentialFigure7.dispatch? waitSchedulerCertificate
                        afterNew.after newInvariant with
                    | none => false
                    | some afterWait =>
                        afterWait.kind == .wait &&
                          afterWait.after.tags == afterNew.after.tags) = true := by
  native_decide

/-- The concrete dispatcher `nop → new → wait` chain also exercises the
proof-carrying tag layer: stable branches preserve tags exactly, `new`
strictly grows them and records one axiom slot, and the complete history keeps
all recorded submitted slots duplicate-free. -/
example {initial : ReservationState}
    {afterNop afterNew afterWait :
      SequentialFigure7.Figure7DispatchResult}
    (initialEquation : waitSchedulerInitial = some initial)
    (nopEquation :
      SequentialFigure7.dispatch? waitSchedulerCertificate initial
          (waitSchedulerInitial_schedulerInvariant initialEquation) =
        some afterNop)
    (nopKind : afterNop.kind = .nop)
    (newEquation :
      SequentialFigure7.dispatch? waitSchedulerCertificate afterNop.after
          (SequentialFigure7.dispatch?_schedulerInvariant
            (waitSchedulerInitial_schedulerInvariant initialEquation)
            nopEquation) =
        some afterNew)
    (newKind : afterNew.kind = .new)
    (waitEquation :
      SequentialFigure7.dispatch? waitSchedulerCertificate afterNew.after
          (SequentialFigure7.dispatch?_schedulerInvariant
            (SequentialFigure7.dispatch?_schedulerInvariant
              (waitSchedulerInitial_schedulerInvariant initialEquation)
              nopEquation)
            newEquation) =
        some afterWait)
    (waitKind : afterWait.kind = .wait) :
    ∃ (newEvidence : SequentialFigure7.DispatchTagEvidence
        waitSchedulerCertificate afterNop.after afterNew)
      (history : SequentialFigure7.ExecutedHistory
        waitSchedulerCertificate afterWait.after)
      (tagHistory : SequentialFigure7.CanonicalTagHistory
        waitSchedulerCertificate history),
      afterNop.after.tags = initial.tags ∧
        (∃ vertex linkIndex,
          newEvidence.Touched vertex ∧
            afterNop.after.tags[vertex]? = some false ∧
            afterNew.after.tags[vertex]? = some true ∧
            newEvidence.linkIndices = [linkIndex]) ∧
        afterWait.after.tags = afterNew.after.tags ∧
        tagHistory.linkIndices.Nodup := by
  let initialInvariant :=
    waitSchedulerInitial_schedulerInvariant initialEquation
  let nopInvariant :=
    SequentialFigure7.dispatch?_schedulerInvariant
      initialInvariant nopEquation
  let newInvariant :=
    SequentialFigure7.dispatch?_schedulerInvariant
      nopInvariant newEquation
  rcases (SequentialFigure7.dispatch?_some_iff initialInvariant).mp
      nopEquation with
    ⟨nopStep⟩
  rcases (SequentialFigure7.dispatch?_some_iff nopInvariant).mp
      newEquation with
    ⟨newStep⟩
  rcases (SequentialFigure7.dispatch?_some_iff newInvariant).mp
      waitEquation with
    ⟨waitStep⟩
  rcases nopStep.tagEvidence with ⟨nopEvidence⟩
  rcases newStep.tagEvidence with ⟨newEvidence⟩
  rcases waitStep.tagEvidence with ⟨waitEvidence⟩
  rcases initializeReservation?_some_iff.mp (by
      simpa [waitSchedulerInitial] using initialEquation) with
    ⟨initialStep⟩
  let history :=
    SequentialFigure7.ExecutedHistory.later
      (SequentialFigure7.ExecutedHistory.later
        (SequentialFigure7.ExecutedHistory.later
          (SequentialFigure7.ExecutedHistory.init initialStep)
          initialInvariant nopStep)
        nopInvariant newStep)
      newInvariant waitStep
  rcases history.hasCanonicalTagHistory with ⟨tagHistory⟩
  have nopNotNew : afterNop.kind ≠ .new := by
    rw [nopKind]
    decide
  have waitNotNew : afterWait.kind ≠ .new := by
    rw [waitKind]
    decide
  exact ⟨newEvidence, history, tagHistory,
    nopEvidence.output_tags_eq_of_kind_ne_new nopNotNew,
    newEvidence.new_growth_and_singleton_link newKind,
    waitEvidence.output_tags_eq_of_kind_ne_new waitNotNew,
    tagHistory.linkIndices_nodup⟩

/-! Strict singleton waiting-payload unification regression. -/

/-- The two axiom classes first leave one exact par conclusion waiting at
boundary `0`.  The active occurrence `2` then meets the marked older
occurrence `1` at the tensor.  Strict singleton unification must construct
both the tensor and the waiting par before draining the two scheduler levels.
-/
private def unifyOneSchedulerCertificate : Certificate where
  formulas := #[
    .atom "p" true,
    .atom "p" false,
    .atom "q" true,
    .atom "q" false,
    .par (.atom "q" false) (.atom "p" true),
    .tensor (.atom "p" false) (.atom "q" true)]
  links := [
    .axiom 0 1,
    .axiom 2 3,
    .par 3 0 4,
    .tensor 1 2 5]
  conclusions := [4, 5]

private theorem unifyOneSchedulerCertificate_structural :
    unifyOneSchedulerCertificate.StructurallyWellFormed := by
  exact
    (Certificate.wellFormed_iff_structurallyWellFormed
      unifyOneSchedulerCertificate).mp (by native_decide)

private def unifyOneSchedulerBefore : ReservationState where
  stack := {
    marks := #[some 0, some 0, none, some 1, none, none]
    nextAge := 2
    sigma := [0, 1]
    ready := [[], [2]]
    waiting := #[
      .initialized [4], .undefined, .undefined,
      .undefined, .undefined, .undefined] }
  core := {
    marks := #[some 0, some 0, none, some 1, none, none]
    parents := #[0, 1]
    components := #[
      some { tree := .axiom "p" true, frontier := [0, 1] },
      some { tree := .axiom "q" true, frontier := [2, 3] }]
    startedAxioms := 2
    firedConnectives := 0 }
  tags := Array.replicate 6 false

private theorem nat_cases_lt_two {value : Nat} (bound : value < 2) :
    value = 0 ∨ value = 1 := by
  cases value with
  | zero => exact Or.inl rfl
  | succ value =>
      cases value with
      | zero => exact Or.inr rfl
      | succ value => omega

private theorem nat_cases_lt_six {value : Nat} (bound : value < 6) :
    value = 0 ∨ value = 1 ∨ value = 2 ∨
      value = 3 ∨ value = 4 ∨ value = 5 := by
  cases value with
  | zero => exact Or.inl rfl
  | succ value =>
      right
      cases value with
      | zero => exact Or.inl rfl
      | succ value =>
          right
          cases value with
          | zero => exact Or.inl rfl
          | succ value =>
              right
              cases value with
              | zero => exact Or.inl rfl
              | succ value =>
                  right
                  cases value with
                  | zero => exact Or.inl rfl
                  | succ value =>
                      right
                      cases value with
                      | zero => rfl
                      | succ value => omega

private theorem unifyOneSchedulerBefore_reservationInvariant :
    ReservationInvariant unifyOneSchedulerCertificate
      unifyOneSchedulerBefore := by
  exact {
    stack_wellShaped := {
      marks_size := rfl
      waiting_size := by native_decide
      assigned_age_bound := by
        intro vertex age assigned
        have vertexBound : vertex < 6 := by
          simpa [unifyOneSchedulerBefore] using
            (Array.getElem?_eq_some_iff.mp assigned).1
        change vertex < 6 at vertexBound
        have cases :
            vertex = 0 ∨ vertex = 1 ∨ vertex = 2 ∨
              vertex = 3 ∨ vertex = 4 ∨ vertex = 5 :=
          nat_cases_lt_six vertexBound
        rcases cases with rfl | rfl | rfl | rfl | rfl | rfl
        · have ageEquation : age = 0 := by
            simpa [unifyOneSchedulerBefore] using assigned.symm
          subst age
          decide
        · have ageEquation : age = 0 := by
            simpa [unifyOneSchedulerBefore] using assigned.symm
          subst age
          decide
        · simp [unifyOneSchedulerBefore] at assigned
        · have ageEquation : age = 1 := by
            simpa [unifyOneSchedulerBefore] using assigned.symm
          subst age
          decide
        · simp [unifyOneSchedulerBefore] at assigned
        · simp [unifyOneSchedulerBefore] at assigned
      sigma_partition := {
        empty_iff := by simp [unifyOneSchedulerBefore]
        head_zero := by simp [unifyOneSchedulerBefore]
        strictIncreasing := by simp [unifyOneSchedulerBefore]
        boundary_lt := by
          intro boundary membership
          simp [unifyOneSchedulerBefore] at membership
          rcases membership with rfl | rfl <;> decide }
      ready_aligned := rfl
      ready_nodup := by
        intro bucket membership
        simp [unifyOneSchedulerBefore] at membership
        rcases membership with rfl | rfl <;> simp
      ready_in_bounds := by
        intro bucket membership vertex vertexMembership
        simp [unifyOneSchedulerBefore] at membership
        rcases membership with rfl | rfl
        · simp at vertexMembership
        · have vertexEquation : vertex = 2 := by
            simpa using vertexMembership
          subst vertex
          decide
      nextAge_le_waiting := by native_decide }
    stack_operationalWaitingDomain := {
      initialized_iff_inactive := by
        intro age ageBound
        change age < 2 at ageBound
        have cases : age = 0 ∨ age = 1 := nat_cases_lt_two ageBound
        rcases cases with rfl | rfl <;>
          simp [SequentialStackState.WaitingInitializedAt,
            unifyOneSchedulerBefore] }
    realizesSigma := {
      marks_eq := rfl
      horizon_eq := rfl
      representative_eq_boundary := by
        intro age ageBound
        change age < 2 at ageBound
        have cases : age = 0 ∨ age = 1 := nat_cases_lt_two ageBound
        rcases cases with rfl | rfl <;> native_decide }
    core_orderedParents := by
      intro token parent lookup
      have tokenBound : token < 2 := by
        simpa [unifyOneSchedulerBefore] using
          (Array.getElem?_eq_some_iff.mp lookup).1
      have cases : token = 0 ∨ token = 1 := by omega
      rcases cases with rfl | rfl <;>
        simp [unifyOneSchedulerBefore] at lookup ⊢ <;> omega
    core_abstractable := {
      markArraySize := rfl
      markedVertexBound := by
        intro vertex token assigned
        simpa [unifyOneSchedulerCertificate,
          unifyOneSchedulerBefore] using
          (Array.getElem?_eq_some_iff.mp
            (UnificationState.assignedToken?_some_raw assigned)).1
      markedTokenBound := by
        intro vertex token assigned
        have raw := UnificationState.assignedToken?_some_raw assigned
        have vertexBound : vertex < 6 := by
          simpa [unifyOneSchedulerBefore] using
            (Array.getElem?_eq_some_iff.mp raw).1
        change vertex < 6 at vertexBound
        have cases :
            vertex = 0 ∨ vertex = 1 ∨ vertex = 2 ∨
              vertex = 3 ∨ vertex = 4 ∨ vertex = 5 :=
          nat_cases_lt_six vertexBound
        rcases cases with rfl | rfl | rfl | rfl | rfl | rfl
        · have tokenEquation : token = 0 := by
            simpa [unifyOneSchedulerBefore] using raw.symm
          subst token
          decide
        · have tokenEquation : token = 0 := by
            simpa [unifyOneSchedulerBefore] using raw.symm
          subst token
          decide
        · simp [unifyOneSchedulerBefore] at raw
        · have tokenEquation : token = 1 := by
            simpa [unifyOneSchedulerBefore] using raw.symm
          subst token
          decide
        · simp [unifyOneSchedulerBefore] at raw
        · simp [unifyOneSchedulerBefore] at raw
      representativeBound := by
        intro token tokenBound
        change token < 2 at tokenBound
        have cases : token = 0 ∨ token = 1 := by omega
        rcases cases with rfl | rfl <;> native_decide
      representativeIdempotent := by
        intro token tokenBound
        change token < 2 at tokenBound
        have cases : token = 0 ∨ token = 1 := by omega
        rcases cases with rfl | rfl <;> native_decide }
    core_componentsFormulaConsistent := by
      intro index component lookup
      have indexBound : index < 2 := by
        simpa [unifyOneSchedulerBefore] using
          (Array.getElem?_eq_some_iff.mp lookup).1
      have cases : index = 0 ∨ index = 1 := by omega
      rcases cases with rfl | rfl
      · simp [unifyOneSchedulerBefore] at lookup
        subst component
        exact ⟨[.atom "p" true, .atom "p" false],
          by native_decide, by native_decide⟩
      · simp [unifyOneSchedulerBefore] at lookup
        subst component
        exact ⟨[.atom "q" true, .atom "q" false],
          by native_decide, by native_decide⟩
    core_carriers_aligned := rfl
    core_counter_aligned := rfl
    tags_size := by native_decide }

private theorem unifyOneSchedulerBefore_componentForestProvenance :
    unifyOneSchedulerCertificate.ComponentForestProvenance
      unifyOneSchedulerBefore.core := by
  let usedAt : Nat → List Nat := fun index =>
    if index = 0 then [0] else if index = 1 then [1] else []
  let ownedAt : Nat → List Nat := fun index =>
    if index = 0 then [0, 1] else if index = 1 then [2, 3] else []
  refine ⟨usedAt, ownedAt, ?_, ?_, ?_⟩
  · intro index component lookup
    have indexBound : index < 2 := by
      simpa [unifyOneSchedulerBefore] using
        (Array.getElem?_eq_some_iff.mp lookup).1
    rcases nat_cases_lt_two indexBound with rfl | rfl
    · simp [unifyOneSchedulerBefore] at lookup
      subst component
      constructor
      · simpa [usedAt, ownedAt] using
          (Certificate.ComponentOccurrenceWitness.axiom_of_submitted
            unifyOneSchedulerCertificate_structural
            (linkIndex := 0) (left := 0) (right := 1)
            (name := "p") (positive := true)
            (by native_decide) (by native_decide))
      · intro vertex membership
        simp [ownedAt] at membership
        rcases membership with rfl | rfl
        · exact Or.inl ⟨0, by rfl, by native_decide⟩
        · exact Or.inl ⟨0, by rfl, by native_decide⟩
    · simp [unifyOneSchedulerBefore] at lookup
      subst component
      constructor
      · simpa [usedAt, ownedAt] using
          (Certificate.ComponentOccurrenceWitness.axiom_of_submitted
            unifyOneSchedulerCertificate_structural
            (linkIndex := 1) (left := 2) (right := 3)
            (name := "q") (positive := true)
            (by native_decide) (by native_decide))
      · intro vertex membership
        simp [ownedAt] at membership
        rcases membership with rfl | rfl
        · exact Or.inr ⟨by rfl, by simp⟩
        · exact Or.inl ⟨1, by rfl, by native_decide⟩
  · intro leftIndex rightIndex leftComponent rightComponent
      leftLookup rightLookup different
    have leftBound : leftIndex < 2 := by
      simpa [unifyOneSchedulerBefore] using
        (Array.getElem?_eq_some_iff.mp leftLookup).1
    have rightBound : rightIndex < 2 := by
      simpa [unifyOneSchedulerBefore] using
        (Array.getElem?_eq_some_iff.mp rightLookup).1
    rcases nat_cases_lt_two leftBound with rfl | rfl <;>
      rcases nat_cases_lt_two rightBound with rfl | rfl <;>
      simp [usedAt, ownedAt] at different ⊢
  · intro vertex rawAge marked
    have vertexBound : vertex < 6 := by
      simpa [unifyOneSchedulerBefore] using
        (Array.getElem?_eq_some_iff.mp marked).1
    rcases nat_cases_lt_six vertexBound with
      rfl | rfl | rfl | rfl | rfl | rfl
    · have rawEquation : rawAge = 0 := by
        simpa [unifyOneSchedulerBefore] using marked.symm
      subst rawAge
      refine ⟨0, {
        tree := .axiom "p" true, frontier := [0, 1] }, ?_, ?_, ?_⟩
      · native_decide
      · rfl
      · simp [ownedAt]
    · have rawEquation : rawAge = 0 := by
        simpa [unifyOneSchedulerBefore] using marked.symm
      subst rawAge
      refine ⟨0, {
        tree := .axiom "p" true, frontier := [0, 1] }, ?_, ?_, ?_⟩
      · native_decide
      · rfl
      · simp [ownedAt]
    · simp [unifyOneSchedulerBefore] at marked
    · have rawEquation : rawAge = 1 := by
        simpa [unifyOneSchedulerBefore] using marked.symm
      subst rawAge
      refine ⟨1, {
        tree := .axiom "q" true, frontier := [2, 3] }, ?_, ?_, ?_⟩
      · native_decide
      · rfl
      · simp [ownedAt]
    · simp [unifyOneSchedulerBefore] at marked
    · simp [unifyOneSchedulerBefore] at marked

private theorem unifyOneSchedulerBefore_componentDomainExact :
    ComponentDomainExact unifyOneSchedulerBefore := by
  intro token
  constructor
  · rintro ⟨component, lookup⟩
    have tokenBound : token < 2 := by
      simpa [unifyOneSchedulerBefore] using
        (Array.getElem?_eq_some_iff.mp lookup).1
    rcases nat_cases_lt_two tokenBound with rfl | rfl <;>
      simp [unifyOneSchedulerBefore]
  · intro membership
    simp [unifyOneSchedulerBefore] at membership
    rcases membership with rfl | rfl
    · exact ⟨{ tree := .axiom "p" true, frontier := [0, 1] }, rfl⟩
    · exact ⟨{ tree := .axiom "q" true, frontier := [2, 3] }, rfl⟩

private theorem unifyOneSchedulerBefore_liveFrontiersNodup :
    LiveFrontiersNodup unifyOneSchedulerBefore := by
  unfold LiveFrontiersNodup UnificationState.liveFrontierVertices
  native_decide

private theorem unifyOneSchedulerBefore_readyBucketFrontierExact :
    ReadyBucketFrontierExact unifyOneSchedulerBefore := by
  intro position boundary bucket sigmaLookup readyLookup
  have positionBound : position < 2 := by
    simpa [unifyOneSchedulerBefore] using
      (List.getElem?_eq_some_iff.mp sigmaLookup).1
  rcases nat_cases_lt_two positionBound with rfl | rfl
  · simp [unifyOneSchedulerBefore] at sigmaLookup readyLookup
    subst boundary
    subst bucket
    refine ⟨{ tree := .axiom "p" true, frontier := [0, 1] }, rfl, ?_⟩
    intro vertex
    constructor
    · simp
    · rintro ⟨frontier, unmarked⟩
      simp at frontier
      rcases frontier with rfl | rfl <;>
        simp [unifyOneSchedulerBefore] at unmarked
  · simp [unifyOneSchedulerBefore] at sigmaLookup readyLookup
    subst boundary
    subst bucket
    refine ⟨{ tree := .axiom "q" true, frontier := [2, 3] }, rfl, ?_⟩
    intro vertex
    constructor
    · intro membership
      have same : vertex = 2 := by simpa using membership
      subst vertex
      exact ⟨by simp, by rfl⟩
    · rintro ⟨frontier, unmarked⟩
      simp at frontier
      rcases frontier with rfl | rfl
      · simp
      · simp [unifyOneSchedulerBefore] at unmarked

private theorem unifyOneSchedulerBefore_queuedVerticesNodup :
    QueuedVerticesNodup unifyOneSchedulerBefore := by
  unfold QueuedVerticesNodup SequentialStackState.queuedVertices
    SequentialStackState.waitingVertices WaitingCell.vertices
  native_decide

private theorem unifyOneSchedulerBefore_queuedVerticesUnmarked :
    QueuedVerticesUnmarked unifyOneSchedulerBefore := by
  intro vertex membership
  have cases : vertex = 2 ∨ vertex = 4 := by
    simpa [unifyOneSchedulerBefore,
      SequentialStackState.queuedVertices,
      SequentialStackState.waitingVertices,
      WaitingCell.vertices] using membership
  rcases cases with rfl | rfl <;> rfl

private theorem unifyOneSchedulerBefore_notProducedFour :
    ¬ Produced unifyOneSchedulerBefore 4 := by
  rintro (⟨age, marked⟩ | frontier)
  · simp [unifyOneSchedulerBefore] at marked
  · unfold UnificationState.liveFrontierVertices at frontier
    simp [unifyOneSchedulerBefore] at frontier

private theorem unifyOneSchedulerBefore_notProducedFive :
    ¬ Produced unifyOneSchedulerBefore 5 := by
  rintro (⟨age, marked⟩ | frontier)
  · simp [unifyOneSchedulerBefore] at marked
  · unfold UnificationState.liveFrontierVertices at frontier
    simp [unifyOneSchedulerBefore] at frontier

private theorem unifyOneSchedulerBefore_producedPremisesMarked :
    ProducedPremisesMarked unifyOneSchedulerCertificate
      unifyOneSchedulerBefore := by
  intro link membership
  have cases :
      link = .axiom 0 1 ∨ link = .axiom 2 3 ∨
        link = .par 3 0 4 ∨ link = .tensor 1 2 5 := by
    simpa [unifyOneSchedulerCertificate] using membership
  rcases cases with rfl | rfl | rfl | rfl
  · trivial
  · trivial
  · intro produced
    exact False.elim (unifyOneSchedulerBefore_notProducedFour produced)
  · intro produced
    exact False.elim (unifyOneSchedulerBefore_notProducedFive produced)

private theorem unifyOneSchedulerBefore_waitingSpanExact :
    WaitingSpanExact unifyOneSchedulerCertificate
      unifyOneSchedulerBefore := by
  intro boundary payload conclusion waitingLookup conclusionMembership
  have boundaryBound : boundary < 6 := by
    simpa [unifyOneSchedulerBefore] using
      (Array.getElem?_eq_some_iff.mp waitingLookup).1
  rcases nat_cases_lt_six boundaryBound with
    rfl | rfl | rfl | rfl | rfl | rfl
  · simp [unifyOneSchedulerBefore] at waitingLookup
    subst payload
    have conclusionEquation : conclusion = 4 := by
      simpa using conclusionMembership
    subst conclusion
    refine ⟨2, 3, 0, 0, 3, 0, 1, 1, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_⟩
    · rfl
    · native_decide
    · rfl
    · exact Or.inr ⟨rfl, rfl⟩
    · rfl
    · rfl
    · native_decide
    · native_decide
    · decide
  · simp [unifyOneSchedulerBefore] at waitingLookup
  · simp [unifyOneSchedulerBefore] at waitingLookup
  · simp [unifyOneSchedulerBefore] at waitingLookup
  · simp [unifyOneSchedulerBefore] at waitingLookup
  · simp [unifyOneSchedulerBefore] at waitingLookup

private theorem unifyOneSchedulerBefore_pendingPremisesCoveredExceptReady :
    PendingPremisesCoveredExceptReady unifyOneSchedulerCertificate
      unifyOneSchedulerBefore := by
  intro link membership
  have cases :
      link = .axiom 0 1 ∨ link = .axiom 2 3 ∨
        link = .par 3 0 4 ∨ link = .tensor 1 2 5 := by
    simpa [unifyOneSchedulerCertificate] using membership
  rcases cases with rfl | rfl | rfl | rfl
  · trivial
  · trivial
  · intro _conclusionUnmarked _conclusionNotReady premise token
      premiseMembership tokenAt
    simp only [List.mem_cons, List.not_mem_nil, or_false]
      at premiseMembership
    rcases premiseMembership with rfl | rfl
    · have tokenEquation : token = 1 := by
        change some (unifyOneSchedulerBefore.core.representative 1) =
          some token at tokenAt
        have representative :
            unifyOneSchedulerBefore.core.representative 1 = 1 := by
          native_decide
        rw [representative] at tokenAt
        exact (Option.some.inj tokenAt).symm
      subst token
      refine ⟨{ tree := .axiom "q" true, frontier := [2, 3] }, ?_, by simp⟩
      native_decide
    · have tokenEquation : token = 0 := by
        change some (unifyOneSchedulerBefore.core.representative 0) =
          some token at tokenAt
        have representative :
            unifyOneSchedulerBefore.core.representative 0 = 0 := by
          native_decide
        rw [representative] at tokenAt
        exact (Option.some.inj tokenAt).symm
      subst token
      refine ⟨{ tree := .axiom "p" true, frontier := [0, 1] }, ?_, by simp⟩
      native_decide
  · intro _conclusionUnmarked _conclusionNotReady premise token
      premiseMembership tokenAt
    simp only [List.mem_cons, List.not_mem_nil, or_false]
      at premiseMembership
    rcases premiseMembership with rfl | rfl
    · have tokenEquation : token = 0 := by
        change some (unifyOneSchedulerBefore.core.representative 0) =
          some token at tokenAt
        have representative :
            unifyOneSchedulerBefore.core.representative 0 = 0 := by
          native_decide
        rw [representative] at tokenAt
        exact (Option.some.inj tokenAt).symm
      subst token
      refine ⟨{ tree := .axiom "p" true, frontier := [0, 1] }, ?_, by simp⟩
      native_decide
    · simp [unifyOneSchedulerBefore, UnificationState.tokenAt?] at tokenAt

private theorem unifyOneSchedulerBefore_firedCounterExact :
    FiredCounterExact unifyOneSchedulerBefore := by
  unfold FiredCounterExact UnificationState.liveConnectiveCount
  rfl

/-- The exact strict-singleton pre-state satisfies the full occurrence-exact
state-only scheduler invariant.  This finite-state check is deliberately not
a claim that the current partial dispatcher can reach this state. -/
private theorem unifyOneSchedulerBefore_schedulerInvariant :
    SchedulerInvariant unifyOneSchedulerCertificate
      unifyOneSchedulerBefore := by
  exact {
    toReservationInvariant :=
      unifyOneSchedulerBefore_reservationInvariant
    structural := unifyOneSchedulerCertificate_structural
    component_domain_exact :=
      unifyOneSchedulerBefore_componentDomainExact
    component_forest_provenance :=
      unifyOneSchedulerBefore_componentForestProvenance
    live_frontiers_nodup :=
      unifyOneSchedulerBefore_liveFrontiersNodup
    ready_bucket_frontier_exact :=
      unifyOneSchedulerBefore_readyBucketFrontierExact
    queued_vertices_nodup :=
      unifyOneSchedulerBefore_queuedVerticesNodup
    queued_vertices_unmarked :=
      unifyOneSchedulerBefore_queuedVerticesUnmarked
    produced_premises_marked :=
      unifyOneSchedulerBefore_producedPremisesMarked
    waiting_span_exact :=
      unifyOneSchedulerBefore_waitingSpanExact
    pending_premises_covered_except_ready :=
      unifyOneSchedulerBefore_pendingPremisesCoveredExceptReady
    fired_counter_exact :=
      unifyOneSchedulerBefore_firedCounterExact }

/-- A genuine singleton waiting payload is represented canonically by the
general dispatcher tag, not by a legacy `UnifyOne` history constructor. -/
example :
    (match SequentialFigure7.dispatch? unifyOneSchedulerCertificate
        unifyOneSchedulerBefore unifyOneSchedulerBefore_schedulerInvariant with
    | none => false
    | some result => result.kind == .unifyPayload) = true := by
  native_decide

/-- Change only the inactive boundary payload of the concrete singleton
fixture.  Reservation-layer invariants intentionally constrain the initialized
waiting domain, not the payload cardinality or its occurrence semantics. -/
private def unifyOneSchedulerBeforeWithPayload
    (payload : List Vertex) : ReservationState :=
  { unifyOneSchedulerBefore with
    stack := {
      unifyOneSchedulerBefore.stack with
      waiting :=
        #[.initialized payload, .undefined, .undefined,
          .undefined, .undefined, .undefined] } }

private theorem unifyOneSchedulerBeforeWithPayload_reservationInvariant
    (payload : List Vertex) :
    ReservationInvariant unifyOneSchedulerCertificate
      (unifyOneSchedulerBeforeWithPayload payload) := by
  have base := unifyOneSchedulerBefore_reservationInvariant
  exact {
    stack_wellShaped := {
      marks_size := base.stack_wellShaped.marks_size
      waiting_size := rfl
      assigned_age_bound := base.stack_wellShaped.assigned_age_bound
      sigma_partition := base.stack_wellShaped.sigma_partition
      ready_aligned := base.stack_wellShaped.ready_aligned
      ready_nodup := base.stack_wellShaped.ready_nodup
      ready_in_bounds := base.stack_wellShaped.ready_in_bounds
      nextAge_le_waiting := by
        change 2 ≤ 6
        decide }
    stack_operationalWaitingDomain := {
      initialized_iff_inactive := by
        intro age ageBound
        change age < 2 at ageBound
        have cases : age = 0 ∨ age = 1 := nat_cases_lt_two ageBound
        rcases cases with rfl | rfl <;>
          simp [SequentialStackState.WaitingInitializedAt,
            unifyOneSchedulerBeforeWithPayload,
            unifyOneSchedulerBefore] }
    realizesSigma := {
      marks_eq := base.realizesSigma.marks_eq
      horizon_eq := base.realizesSigma.horizon_eq
      representative_eq_boundary :=
        base.realizesSigma.representative_eq_boundary }
    core_orderedParents := base.core_orderedParents
    core_abstractable := base.core_abstractable
    core_componentsFormulaConsistent :=
      base.core_componentsFormulaConsistent
    core_carriers_aligned := base.core_carriers_aligned
    core_counter_aligned := base.core_counter_aligned
    tags_size := base.tags_size }

private def unifyOneSchedulerRun : Option ReservationState :=
  SequentialFigure7.unifyOne? unifyOneSchedulerCertificate
    unifyOneSchedulerBefore
    unifyOneSchedulerBefore_reservationInvariant

/-- From the exact two-level reservation state, `unifyOne` drains exactly
`[4]`, constructs the tensor and that par, merges the two raw-age classes, and
leaves the live ready frontier `[5, 4]`.  This fixture tests the local rule;
it does not claim a full-rule reachability theorem. -/
example :
    (match unifyOneSchedulerRun with
    | none => false
    | some afterUnify =>
                        afterUnify.stack.sigma == [0] &&
                        afterUnify.stack.ready == [[5, 4]] &&
                        afterUnify.stack.waiting[0]? == some .undefined &&
                        afterUnify.stack.waiting[1]? == some .undefined &&
                        afterUnify.stack.marks ==
                          #[some 0, some 0, some 1, some 1, none, none] &&
                        afterUnify.core.marks == afterUnify.stack.marks &&
                        afterUnify.core.parents == #[0, 0] &&
                        afterUnify.core.startedAxioms == 2 &&
                        afterUnify.core.firedConnectives == 2 &&
                        match afterUnify.core.components[0]? with
                        | some (some component) =>
                            component.frontier == [5, 4] &&
                              component.tree ==
                                (.par 2 1
                                  (.tensor 1 0
                                    (.axiom "p" true)
                                    (.axiom "q" true))) &&
                              afterUnify.core.components[1]? == some none
                        | _ => false) = true := by
  native_decide

/-- The same concrete success carries the proof-relevant typed witness and
therefore is not merely an unchecked state equality. -/
example {after : ReservationState}
    (equation : unifyOneSchedulerRun = some after) :
    Nonempty
      (SequentialFigure7.UnifyOneStep unifyOneSchedulerCertificate
        unifyOneSchedulerBefore after) := by
  exact
    (SequentialFigure7.unifyOne?_some_iff
      unifyOneSchedulerBefore_reservationInvariant).mp (by
        simpa [unifyOneSchedulerRun] using equation)

/-- The proof-relevant singleton witness itself exercises
`UnifyOneStep.schedulerInvariant` on the concrete full-invariant pre-state. -/
example {after : ReservationState}
    (equation : unifyOneSchedulerRun = some after) :
    SchedulerInvariant unifyOneSchedulerCertificate after := by
  rcases
      (SequentialFigure7.unifyOne?_some_iff
        unifyOneSchedulerBefore_schedulerInvariant.toReservationInvariant).mp
        (by simpa [unifyOneSchedulerRun] using equation) with
    ⟨step⟩
  exact step.schedulerInvariant
    unifyOneSchedulerBefore_schedulerInvariant

/-- The executable singleton result refines the independent Boolean-free
relation. -/
example {after : ReservationState}
    (equation : unifyOneSchedulerRun = some after) :
    SequentialFigure7.UnifyOneRule unifyOneSchedulerCertificate
      unifyOneSchedulerBefore after := by
  exact SequentialFigure7.unifyOne?_sound
    unifyOneSchedulerBefore_reservationInvariant (by
      simpa [unifyOneSchedulerRun] using equation)

/-- The tensor-plus-waiting-par step preserves every reservation-layer field,
including exact sigma realization and both production counter alignments. -/
example {after : ReservationState}
    (equation : unifyOneSchedulerRun = some after) :
    ReservationInvariant unifyOneSchedulerCertificate after := by
  exact SequentialFigure7.unifyOne?_reservationInvariant
    unifyOneSchedulerBefore_reservationInvariant (by
      simpa [unifyOneSchedulerRun] using equation)

/-- The same concrete singleton execution exercises the full state-only
scheduler preservation theorem, not only the reservation-layer projection. -/
example {after : ReservationState}
    (equation : unifyOneSchedulerRun = some after) :
    SchedulerInvariant unifyOneSchedulerCertificate after := by
  exact SequentialFigure7.unifyOne?_schedulerInvariant
    unifyOneSchedulerBefore_schedulerInvariant (by
      simpa [unifyOneSchedulerRun] using equation)

private def unifyOneSchedulerEmptyBefore : ReservationState :=
  unifyOneSchedulerBeforeWithPayload []

private theorem unifyOneSchedulerEmptyBefore_reservationInvariant :
    ReservationInvariant unifyOneSchedulerCertificate
      unifyOneSchedulerEmptyBefore := by
  exact unifyOneSchedulerBeforeWithPayload_reservationInvariant []

/-- An initialized but empty inactive waiting cell is a valid reservation
state, but it is outside strict singleton `unifyOne`; the executable rule must
fail closed instead of silently acting like `unifyEmpty`. -/
example :
    SequentialFigure7.unifyOne? unifyOneSchedulerCertificate
        unifyOneSchedulerEmptyBefore
        unifyOneSchedulerEmptyBefore_reservationInvariant =
      none := by
  native_decide

private def unifyOneSchedulerDuplicateBefore : ReservationState :=
  unifyOneSchedulerBeforeWithPayload [4, 4]

private theorem unifyOneSchedulerDuplicateBefore_reservationInvariant :
    ReservationInvariant unifyOneSchedulerCertificate
      unifyOneSchedulerDuplicateBefore := by
  exact unifyOneSchedulerBeforeWithPayload_reservationInvariant [4, 4]

/-- A two-element inactive payload remains a valid reservation-layer state,
including the deliberately adversarial duplicate `[4, 4]`, but strict
singleton `unifyOne` rejects it before constructing either connective. -/
example :
    SequentialFigure7.unifyOne? unifyOneSchedulerCertificate
        unifyOneSchedulerDuplicateBefore
        unifyOneSchedulerDuplicateBefore_reservationInvariant =
      none := by
  native_decide

/-! Atomic arbitrary-payload unification regressions. -/

/-- Two three-occurrence production components meet at one tensor.  The four
remaining marked premises support two distinct independent waiting pars.

This is a deliberately hand-built `ReservationInvariant` fixture.  It does
not submit the axiom origins from which the two stored component trees would
arise, so it is not a `StructurallyWellFormed` certificate fixture and does not
exercise structural completeness, scheduler provenance, or reachability. -/
private def unifyPayloadSchedulerCertificate : Certificate where
  formulas := #[
    .tensor (.atom "p" true) (.atom "p" true),
    .atom "p" false,
    .atom "p" false,
    .tensor (.atom "p" true) (.atom "p" true),
    .atom "p" false,
    .atom "p" false,
    .tensor
      (.tensor (.atom "p" true) (.atom "p" true))
      (.tensor (.atom "p" true) (.atom "p" true)),
    .par (.atom "p" false) (.atom "p" false),
    .par (.atom "p" false) (.atom "p" false)]
  links := [
    .tensor 0 3 6,
    .par 1 2 7,
    .par 4 5 8]
  conclusions := [6, 7, 8]

private theorem nat_cases_lt_nine {value : Nat} (bound : value < 9) :
    value = 0 ∨ value = 1 ∨ value = 2 ∨ value = 3 ∨
      value = 4 ∨ value = 5 ∨ value = 6 ∨ value = 7 ∨
        value = 8 := by
  omega

private def unifyPayloadSchedulerBeforeWithPayload
    (payload : List Vertex) : ReservationState where
  stack := {
    marks := #[
      none, some 1, some 1, some 0, some 0, some 0,
      none, none, none]
    nextAge := 2
    sigma := [0, 1]
    ready := [[], [0]]
    waiting := #[
      .initialized payload, .undefined, .undefined, .undefined,
      .undefined, .undefined, .undefined, .undefined, .undefined] }
  core := {
    marks := #[
      none, some 1, some 1, some 0, some 0, some 0,
      none, none, none]
    parents := #[0, 1]
    components := #[
      some {
        tree := .tensor 0 0 (.axiom "p" true) (.axiom "p" true)
        frontier := [3, 4, 5] },
      some {
        tree := .tensor 0 0 (.axiom "p" true) (.axiom "p" true)
        frontier := [0, 1, 2] }]
    startedAxioms := 2
    firedConnectives := 2 }
  tags := Array.replicate 9 false

private theorem unifyPayloadSchedulerBeforeWithPayload_reservationInvariant
    (payload : List Vertex) :
    ReservationInvariant unifyPayloadSchedulerCertificate
      (unifyPayloadSchedulerBeforeWithPayload payload) := by
  exact {
    stack_wellShaped := {
      marks_size := rfl
      waiting_size := rfl
      assigned_age_bound := by
        intro vertex age assigned
        have vertexBound : vertex < 9 := by
          simpa [unifyPayloadSchedulerBeforeWithPayload] using
            (Array.getElem?_eq_some_iff.mp assigned).1
        have cases := nat_cases_lt_nine vertexBound
        rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · simp [unifyPayloadSchedulerBeforeWithPayload] at assigned
        · have ageEquation : age = 1 := by
            simpa [unifyPayloadSchedulerBeforeWithPayload] using assigned.symm
          subst age
          simp [unifyPayloadSchedulerBeforeWithPayload]
        · have ageEquation : age = 1 := by
            simpa [unifyPayloadSchedulerBeforeWithPayload] using assigned.symm
          subst age
          simp [unifyPayloadSchedulerBeforeWithPayload]
        · have ageEquation : age = 0 := by
            simpa [unifyPayloadSchedulerBeforeWithPayload] using assigned.symm
          subst age
          simp [unifyPayloadSchedulerBeforeWithPayload]
        · have ageEquation : age = 0 := by
            simpa [unifyPayloadSchedulerBeforeWithPayload] using assigned.symm
          subst age
          simp [unifyPayloadSchedulerBeforeWithPayload]
        · have ageEquation : age = 0 := by
            simpa [unifyPayloadSchedulerBeforeWithPayload] using assigned.symm
          subst age
          simp [unifyPayloadSchedulerBeforeWithPayload]
        all_goals simp [unifyPayloadSchedulerBeforeWithPayload] at assigned
      sigma_partition := {
        empty_iff := by simp [unifyPayloadSchedulerBeforeWithPayload]
        head_zero := by simp [unifyPayloadSchedulerBeforeWithPayload]
        strictIncreasing := by simp [unifyPayloadSchedulerBeforeWithPayload]
        boundary_lt := by
          intro boundary membership
          simp [unifyPayloadSchedulerBeforeWithPayload] at membership
          rcases membership with rfl | rfl <;>
            simp [unifyPayloadSchedulerBeforeWithPayload] }
      ready_aligned := rfl
      ready_nodup := by
        intro bucket membership
        simp [unifyPayloadSchedulerBeforeWithPayload] at membership
        rcases membership with rfl | rfl <;> simp
      ready_in_bounds := by
        intro bucket membership vertex vertexMembership
        simp [unifyPayloadSchedulerBeforeWithPayload] at membership
        rcases membership with rfl | rfl
        · simp at vertexMembership
        · have vertexEquation : vertex = 0 := by
            simpa using vertexMembership
          subst vertex
          simp [unifyPayloadSchedulerCertificate]
      nextAge_le_waiting := by
        simp [unifyPayloadSchedulerBeforeWithPayload] }
    stack_operationalWaitingDomain := {
      initialized_iff_inactive := by
        intro age ageBound
        change age < 2 at ageBound
        have cases : age = 0 ∨ age = 1 := nat_cases_lt_two ageBound
        rcases cases with rfl | rfl <;>
          simp [SequentialStackState.WaitingInitializedAt,
            unifyPayloadSchedulerBeforeWithPayload] }
    realizesSigma := {
      marks_eq := rfl
      horizon_eq := rfl
      representative_eq_boundary := by
        intro age ageBound
        change age < 2 at ageBound
        have cases : age = 0 ∨ age = 1 := nat_cases_lt_two ageBound
        rcases cases with rfl | rfl <;>
          simp [unifyPayloadSchedulerBeforeWithPayload,
            UnificationState.representative] <;> native_decide }
    core_orderedParents := by
      intro token parent lookup
      have tokenBound : token < 2 := by
        simpa [unifyPayloadSchedulerBeforeWithPayload] using
          (Array.getElem?_eq_some_iff.mp lookup).1
      have cases : token = 0 ∨ token = 1 := by omega
      rcases cases with rfl | rfl <;>
        simp [unifyPayloadSchedulerBeforeWithPayload] at lookup ⊢ <;> omega
    core_abstractable := {
      markArraySize := rfl
      markedVertexBound := by
        intro vertex token assigned
        simpa [unifyPayloadSchedulerCertificate,
          unifyPayloadSchedulerBeforeWithPayload] using
          (Array.getElem?_eq_some_iff.mp
            (UnificationState.assignedToken?_some_raw assigned)).1
      markedTokenBound := by
        intro vertex token assigned
        have raw := UnificationState.assignedToken?_some_raw assigned
        have vertexBound : vertex < 9 := by
          simpa [unifyPayloadSchedulerBeforeWithPayload] using
            (Array.getElem?_eq_some_iff.mp raw).1
        have cases := nat_cases_lt_nine vertexBound
        rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · simp [unifyPayloadSchedulerBeforeWithPayload] at raw
        · have tokenEquation : token = 1 := by
            simpa [unifyPayloadSchedulerBeforeWithPayload] using raw.symm
          subst token
          simp [unifyPayloadSchedulerBeforeWithPayload]
        · have tokenEquation : token = 1 := by
            simpa [unifyPayloadSchedulerBeforeWithPayload] using raw.symm
          subst token
          simp [unifyPayloadSchedulerBeforeWithPayload]
        · have tokenEquation : token = 0 := by
            simpa [unifyPayloadSchedulerBeforeWithPayload] using raw.symm
          subst token
          simp [unifyPayloadSchedulerBeforeWithPayload]
        · have tokenEquation : token = 0 := by
            simpa [unifyPayloadSchedulerBeforeWithPayload] using raw.symm
          subst token
          simp [unifyPayloadSchedulerBeforeWithPayload]
        · have tokenEquation : token = 0 := by
            simpa [unifyPayloadSchedulerBeforeWithPayload] using raw.symm
          subst token
          simp [unifyPayloadSchedulerBeforeWithPayload]
        all_goals simp [unifyPayloadSchedulerBeforeWithPayload] at raw
      representativeBound := by
        intro token tokenBound
        change token < 2 at tokenBound
        have cases : token = 0 ∨ token = 1 := by omega
        rcases cases with rfl | rfl <;>
          simp [unifyPayloadSchedulerBeforeWithPayload,
            UnificationState.representative] <;> native_decide
      representativeIdempotent := by
        intro token tokenBound
        change token < 2 at tokenBound
        have cases : token = 0 ∨ token = 1 := by omega
        rcases cases with rfl | rfl <;>
          simp [unifyPayloadSchedulerBeforeWithPayload,
            UnificationState.representative] <;> native_decide }
    core_componentsFormulaConsistent := by
      intro index component lookup
      have indexBound : index < 2 := by
        simpa [unifyPayloadSchedulerBeforeWithPayload] using
          (Array.getElem?_eq_some_iff.mp lookup).1
      have cases : index = 0 ∨ index = 1 := by omega
      rcases cases with rfl | rfl
      · simp [unifyPayloadSchedulerBeforeWithPayload] at lookup
        subst component
        exact ⟨[
            .tensor (.atom "p" true) (.atom "p" true),
            .atom "p" false, .atom "p" false],
          by native_decide, by native_decide⟩
      · simp [unifyPayloadSchedulerBeforeWithPayload] at lookup
        subst component
        exact ⟨[
            .tensor (.atom "p" true) (.atom "p" true),
            .atom "p" false, .atom "p" false],
          by native_decide, by native_decide⟩
    core_carriers_aligned := rfl
    core_counter_aligned := rfl
    tags_size := rfl }

private def unifyPayloadSchedulerRun (payload : List Vertex) :
    Option ReservationState :=
  SequentialFigure7.unifyPayload? unifyPayloadSchedulerCertificate
    (unifyPayloadSchedulerBeforeWithPayload payload)
    (unifyPayloadSchedulerBeforeWithPayload_reservationInvariant payload)

/-- Empty payload: one tensor, no waiting par, then the exact drain. -/
example :
    (match unifyPayloadSchedulerRun [] with
    | none => false
    | some afterUnify =>
        afterUnify.stack.sigma == [0] &&
        afterUnify.stack.ready == [[6]] &&
        afterUnify.core.firedConnectives == 3) = true := by
  native_decide

/-- Empty-shape compatibility uses the canonical generic-to-tensor query
bridge and returns the old executor's exact output. -/
example :
    unifyPayloadSchedulerRun [] =
      SequentialFigure7.unifyEmpty? unifyPayloadSchedulerCertificate
        (unifyPayloadSchedulerBeforeWithPayload [])
        (unifyPayloadSchedulerBeforeWithPayload_reservationInvariant []) := by
  native_decide

example {after : ReservationState}
    (equation :
      SequentialFigure7.unifyEmpty? unifyPayloadSchedulerCertificate
          (unifyPayloadSchedulerBeforeWithPayload [])
          (unifyPayloadSchedulerBeforeWithPayload_reservationInvariant []) =
        some after) :
    unifyPayloadSchedulerRun [] = some after := by
  exact SequentialFigure7.unifyPayload?_of_unifyEmpty?_eq_some
    (unifyPayloadSchedulerBeforeWithPayload_reservationInvariant [])
    equation

/-- Singleton payload: the unified executor agrees with the old strict
singleton result through the explicit witness bridge. -/
example :
    unifyPayloadSchedulerRun [7] =
      SequentialFigure7.unifyOne? unifyPayloadSchedulerCertificate
        (unifyPayloadSchedulerBeforeWithPayload [7])
        (unifyPayloadSchedulerBeforeWithPayload_reservationInvariant [7]) := by
  native_decide

example {after : ReservationState}
    (equation :
      SequentialFigure7.unifyOne? unifyPayloadSchedulerCertificate
          (unifyPayloadSchedulerBeforeWithPayload [7])
          (unifyPayloadSchedulerBeforeWithPayload_reservationInvariant [7]) =
        some after) :
    unifyPayloadSchedulerRun [7] = some after := by
  exact SequentialFigure7.unifyPayload?_of_unifyOne?_eq_some
    (unifyPayloadSchedulerBeforeWithPayload_reservationInvariant [7])
    equation

/-- Two distinct waiting conclusions are activated in stored order and the
local counter records one tensor plus two pars. -/

example :
    (match unifyPayloadSchedulerRun [7, 8] with
    | none => false
    | some afterUnify =>
        afterUnify.stack.sigma == [0] &&
        afterUnify.stack.ready == [[6, 7, 8]] &&
        afterUnify.core.firedConnectives == 5 &&
        match afterUnify.core.components[0]? with
        | some (some component) =>
            component.frontier == [6, 7, 8] &&
              component.tree ==
                (.par 1 1
                  (.par 1 1
                    (.tensor 0 0
                      (.tensor 0 0
                        (.axiom "p" true) (.axiom "p" true))
                      (.tensor 0 0
                        (.axiom "p" true) (.axiom "p" true)))))
        | _ => false) = true := by
  native_decide

/-- The concrete two-element success reconstructs the typed witness, the
high-level-executable-independent direct relation, and the preserved
reservation invariant. -/
example {after : ReservationState}
    (equation : unifyPayloadSchedulerRun [7, 8] = some after) :
    Nonempty
        (SequentialFigure7.UnifyPayloadStep
          unifyPayloadSchedulerCertificate
          (unifyPayloadSchedulerBeforeWithPayload [7, 8]) after) ∧
      SequentialFigure7.UnifyPayloadRule
        unifyPayloadSchedulerCertificate
        (unifyPayloadSchedulerBeforeWithPayload [7, 8]) after ∧
      ReservationInvariant unifyPayloadSchedulerCertificate after := by
  have unfolded :
      SequentialFigure7.unifyPayload? unifyPayloadSchedulerCertificate
          (unifyPayloadSchedulerBeforeWithPayload [7, 8])
          (unifyPayloadSchedulerBeforeWithPayload_reservationInvariant [7, 8]) =
        some after := by
    simpa [unifyPayloadSchedulerRun] using equation
  exact ⟨
    (SequentialFigure7.unifyPayload?_some_iff
      (unifyPayloadSchedulerBeforeWithPayload_reservationInvariant [7, 8])).mp
        unfolded,
    SequentialFigure7.unifyPayload?_sound
      (unifyPayloadSchedulerBeforeWithPayload_reservationInvariant [7, 8])
      unfolded,
    SequentialFigure7.unifyPayload?_reservationInvariant
      (unifyPayloadSchedulerBeforeWithPayload_reservationInvariant [7, 8])
      unfolded⟩

/-- Duplicate activation fails on the threaded second lookup; no stale core
is replayed. -/
example : unifyPayloadSchedulerRun [7, 7] = none := by
  native_decide

/-- A malformed second payload element with no unique submitted par producer
fails closed after the first activation. -/
example : unifyPayloadSchedulerRun [7, 6] = none := by
  native_decide

/-! Arbitrary waiting-payload activation-fold regressions. -/

/-- Minimal production core in which one exact submitted par can be activated.

This fixture exercises only the local production-core fold.  It carries no
scheduler stack and makes no claim that an arbitrary waiting payload is
reachable or that the complete Figure-7 `unify` transition is applicable. -/
private def waitingPayloadFoldCertificate : Certificate where
  formulas := #[
    .atom "p" true,
    .atom "p" false,
    .par (.atom "p" true) (.atom "p" false)]
  links := [
    .axiom 0 1,
    .par 0 1 2]
  conclusions := [2]

private def waitingPayloadFoldBefore : UnificationState where
  marks := #[some 0, some 0, none]
  parents := #[0]
  components := #[
    some { tree := .axiom "p" true, frontier := [0, 1] }]
  startedAxioms := 1
  firedConnectives := 0

private def waitingPayloadFoldAfter : UnificationState where
  marks := #[some 0, some 0, none]
  parents := #[0]
  components := #[
    some {
      tree := .par 0 0 (.axiom "p" true)
      frontier := [2] }]
  startedAxioms := 1
  firedConnectives := 1

/-- The empty stored-order fold is the exact identity execution. -/
example :
    SequentialFigure7.activateWaitingPayload?
        waitingPayloadFoldCertificate waitingPayloadFoldBefore [] =
      some waitingPayloadFoldBefore := by
  rfl

/-- The empty execution also has both typed and independent direct witnesses. -/
example :
    Nonempty
        (SequentialFigure7.WaitingParActivationFoldStep
          waitingPayloadFoldCertificate waitingPayloadFoldBefore []
          waitingPayloadFoldBefore) ∧
      SequentialFigure7.WaitingParActivationFoldRule
        waitingPayloadFoldCertificate waitingPayloadFoldBefore []
        waitingPayloadFoldBefore := by
  exact ⟨⟨.nil waitingPayloadFoldBefore⟩, .nil waitingPayloadFoldBefore⟩

/-- A singleton payload is activated once in stored head-to-tail order. -/
example :
    SequentialFigure7.activateWaitingPayload?
        waitingPayloadFoldCertificate waitingPayloadFoldBefore [2] =
      some waitingPayloadFoldAfter := by
  native_decide

/-- Every concrete singleton success reconstructs the typed fold witness. -/
example {after : UnificationState}
    (equation :
      SequentialFigure7.activateWaitingPayload?
          waitingPayloadFoldCertificate waitingPayloadFoldBefore [2] =
        some after) :
    Nonempty
      (SequentialFigure7.WaitingParActivationFoldStep
        waitingPayloadFoldCertificate waitingPayloadFoldBefore [2] after) := by
  exact
    SequentialFigure7.activateWaitingPayload?_some_iff.mp equation

/-- The same singleton execution refines the independent direct fold relation. -/
example {after : UnificationState}
    (equation :
      SequentialFigure7.activateWaitingPayload?
          waitingPayloadFoldCertificate waitingPayloadFoldBefore [2] =
        some after) :
    SequentialFigure7.WaitingParActivationFoldRule
      waitingPayloadFoldCertificate waitingPayloadFoldBefore [2] after := by
  exact SequentialFigure7.activateWaitingPayload?_sound equation

/-- The project-local constructor counter increases by the payload length. -/
example {after : UnificationState}
    (equation :
      SequentialFigure7.activateWaitingPayload?
          waitingPayloadFoldCertificate waitingPayloadFoldBefore [2] =
        some after) :
    after.firedConnectives =
      waitingPayloadFoldBefore.firedConnectives + [2].length := by
  rcases
      SequentialFigure7.activateWaitingPayload?_some_iff.mp equation with
    ⟨step⟩
  exact step.firedConnectives_eq_add_length

/-- Repeating the same conclusion threads the first result into the second
activation.  The first activation succeeds, while the second fails because
its exact premises are no longer present in the updated component frontier. -/
example :
    (match SequentialFigure7.activateWaitingPar?
        waitingPayloadFoldCertificate waitingPayloadFoldBefore 2 with
    | none => false
    | some once =>
        (SequentialFigure7.activateWaitingPar?
          waitingPayloadFoldCertificate once 2).isNone) = true := by
  native_decide

/-- Consequently the duplicate payload fails closed instead of replaying the
first par against a stale production core. -/
example :
    SequentialFigure7.activateWaitingPayload?
        waitingPayloadFoldCertificate waitingPayloadFoldBefore [2, 2] =
      none := by
  native_decide

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

/-! Input-only applicability for the stable Figure-7 rules. -/

private def axiomStableState : ReservationState :=
  match axiomInitial with
  | some state => state
  | none => ReservationState.empty axiomCertificate

private theorem axiomStableState_eq :
    axiomInitial = some axiomStableState := by
  native_decide

private theorem axiomStableState_invariant :
    SchedulerInvariant axiomCertificate axiomStableState :=
  axiomInitial_schedulerInvariant axiomStableState_eq

private def axiomStableHead :
    SequentialFigure7.ReadyHeadInput axiomStableState where
  vertex := 0
  readyTail := [1]
  rawAge := 0
  top_ready := by native_decide
  sigma_top := by native_decide

private theorem axiom_concl_enabled :
    SequentialFigure7.ConclEnabled axiomCertificate axiomStableState := by
  exact ⟨{
    head := axiomStableHead
    boundary := by native_decide }⟩

/-- A genuine initialized state satisfies full `SchedulerInvariant`; its
input-only conclusion witness executes and preserves that complete invariant. -/
example :
    ∃ next,
      SequentialFigure7.concl? axiomCertificate axiomStableState
          axiomStableState_invariant.toReservationInvariant = some next ∧
        SchedulerInvariant axiomCertificate next :=
  SequentialFigure7.concl?_exists_schedulerInvariant_of_enabled
    axiomStableState_invariant axiom_concl_enabled

/-- The exact empty full-invariant state has no ready head, so none of the
four stable input-only predicates is enabled.  This is not a progress claim. -/
example :
    let state := ReservationState.empty axiomCertificate
    SchedulerInvariant axiomCertificate state ∧
      ¬ SequentialFigure7.ConclEnabled axiomCertificate state ∧
      ¬ SequentialFigure7.NopEnabled axiomCertificate state ∧
      ¬ SequentialFigure7.WaitEnabled axiomCertificate state ∧
      ¬ SequentialFigure7.ForwardEnabled axiomCertificate state := by
  let state := ReservationState.empty axiomCertificate
  have noHead :
      ¬ Nonempty (SequentialFigure7.ReadyHeadInput state) := by
    rintro ⟨head⟩
    simpa [state, ReservationState.empty, SequentialStackState.empty] using
      head.top_ready
  refine ⟨empty_schedulerInvariant axiomCertificate_structural,
    ?_, ?_, ?_, ?_⟩
  · rintro ⟨input⟩
    exact noHead ⟨input.head⟩
  · rintro ⟨input⟩
    exact noHead ⟨input.head⟩
  · rintro ⟨input⟩
    exact noHead ⟨input.head⟩
  · rintro ⟨input⟩
    exact noHead ⟨input.head⟩

private def parNopStableState : ReservationState :=
  match parInitial with
  | some state => state
  | none => ReservationState.empty parCertificate

private theorem parNopStableState_eq :
    parInitial = some parNopStableState := by
  native_decide

private theorem parNopStableState_invariant :
    SchedulerInvariant parCertificate parNopStableState :=
  parInitial_schedulerInvariant parNopStableState_eq

private def parNopStableHead :
    SequentialFigure7.ReadyHeadInput parNopStableState where
  vertex := 0
  readyTail := [1]
  rawAge := 0
  top_ready := by native_decide
  sigma_top := by native_decide

private def parNopSubmitted :
    SequentialFigure7.SubmittedParInput parCertificate
      parNopStableHead.vertex where
  linkIndex := 1
  storedLeft := 0
  storedRight := 1
  conclusion := 2
  side := .storedLeft
  link_eq := by native_decide
  premise_eq := rfl

private theorem par_nop_enabled :
    SequentialFigure7.NopEnabled parCertificate parNopStableState := by
  exact ⟨{
    head := parNopStableHead
    par := parNopSubmitted
    mate_unmarked := by native_decide }⟩

/-- The initialized par fixture is a genuine full-invariant positive `nop`
case and a genuine negative `forward` case because the mate is unmarked. -/
example :
    (∃ next,
      SequentialFigure7.nop? parCertificate parNopStableState
          parNopStableState_invariant.toReservationInvariant = some next ∧
        SchedulerInvariant parCertificate next) ∧
      ¬ SequentialFigure7.ForwardEnabled
        parCertificate parNopStableState := by
  constructor
  · exact SequentialFigure7.nop?_exists_schedulerInvariant_of_enabled
      parNopStableState_invariant par_nop_enabled
  · intro enabled
    rcases SequentialFigure7.forward?_exists_of_enabled
        parNopStableState_invariant enabled with
      ⟨next, equation⟩
    have failure :
        SequentialFigure7.forward? parCertificate parNopStableState
            parNopStableState_invariant.toReservationInvariant = none := by
      native_decide
    rw [failure] at equation
    simp at equation

private def parForwardStableState : ReservationState :=
  match SequentialFigure7.nop? parCertificate parNopStableState
      parNopStableState_invariant.toReservationInvariant with
  | some state => state
  | none => ReservationState.empty parCertificate

private theorem parForwardStableState_eq :
    SequentialFigure7.nop? parCertificate parNopStableState
        parNopStableState_invariant.toReservationInvariant =
      some parForwardStableState := by
  native_decide

private theorem parForwardStableState_invariant :
    SchedulerInvariant parCertificate parForwardStableState :=
  SequentialFigure7.nop?_schedulerInvariant
    parNopStableState_invariant parForwardStableState_eq

private def parForwardStableHead :
    SequentialFigure7.ReadyHeadInput parForwardStableState where
  vertex := 1
  readyTail := []
  rawAge := 0
  top_ready := by native_decide
  sigma_top := by native_decide

private def parForwardSubmitted :
    SequentialFigure7.SubmittedParInput parCertificate
      parForwardStableHead.vertex where
  linkIndex := 1
  storedLeft := 0
  storedRight := 1
  conclusion := 2
  side := .storedRight
  link_eq := by native_decide
  premise_eq := rfl

private theorem par_forward_enabled :
    SequentialFigure7.ForwardEnabled
      parCertificate parForwardStableState := by
  exact ⟨{
    head := parForwardStableHead
    par := parForwardSubmitted
    mateRawAge := 0
    mate_marked := by native_decide
    not_older := by decide }⟩

/-- After the real `nop` step, the same full-invariant fixture becomes a
positive `forward` case and a negative `nop` case. -/
example :
    (∃ next,
      SequentialFigure7.forward? parCertificate parForwardStableState
          parForwardStableState_invariant.toReservationInvariant = some next ∧
        SchedulerInvariant parCertificate next) ∧
      ¬ SequentialFigure7.NopEnabled
        parCertificate parForwardStableState := by
  constructor
  · exact SequentialFigure7.forward?_exists_schedulerInvariant_of_enabled
      parForwardStableState_invariant par_forward_enabled
  · intro enabled
    rcases SequentialFigure7.nop?_exists_of_enabled
        parForwardStableState_invariant enabled with
      ⟨next, equation⟩
    have failure :
        SequentialFigure7.nop? parCertificate parForwardStableState
            parForwardStableState_invariant.toReservationInvariant = none := by
      native_decide
    rw [failure] at equation
    simp at equation

private def waitStableInitialState : ReservationState :=
  match waitSchedulerInitial with
  | some state => state
  | none => ReservationState.empty waitSchedulerCertificate

private theorem waitStableInitialState_eq :
    waitSchedulerInitial = some waitStableInitialState := by
  native_decide

private theorem waitStableInitialState_invariant :
    SchedulerInvariant waitSchedulerCertificate waitStableInitialState :=
  waitSchedulerInitial_schedulerInvariant waitStableInitialState_eq

private def waitStableAfterNop : ReservationState :=
  match SequentialFigure7.nop? waitSchedulerCertificate
      waitStableInitialState
      waitStableInitialState_invariant.toReservationInvariant with
  | some state => state
  | none => ReservationState.empty waitSchedulerCertificate

private theorem waitStableAfterNop_eq :
    SequentialFigure7.nop? waitSchedulerCertificate waitStableInitialState
        waitStableInitialState_invariant.toReservationInvariant =
      some waitStableAfterNop := by
  native_decide

private theorem waitStableAfterNop_invariant :
    SchedulerInvariant waitSchedulerCertificate waitStableAfterNop :=
  SequentialFigure7.nop?_schedulerInvariant
    waitStableInitialState_invariant waitStableAfterNop_eq

private def waitStableReadyState : ReservationState :=
  match SequentialFigure7.new? waitSchedulerCertificate waitStableAfterNop
      waitStableAfterNop_invariant.toReservationInvariant with
  | some state => state
  | none => ReservationState.empty waitSchedulerCertificate

private theorem waitStableReadyState_eq :
    SequentialFigure7.new? waitSchedulerCertificate waitStableAfterNop
        waitStableAfterNop_invariant.toReservationInvariant =
      some waitStableReadyState := by
  native_decide

private theorem waitStableReadyState_invariant :
    SchedulerInvariant waitSchedulerCertificate waitStableReadyState :=
  SequentialFigure7.new?_schedulerInvariant
    waitStableAfterNop_invariant waitStableReadyState_eq

private def waitStableHead :
    SequentialFigure7.ReadyHeadInput waitStableReadyState where
  vertex := 2
  readyTail := [3]
  rawAge := 1
  top_ready := by native_decide
  sigma_top := by native_decide

private def waitStableSubmitted :
    SequentialFigure7.SubmittedParInput waitSchedulerCertificate
      waitStableHead.vertex where
  linkIndex := 2
  storedLeft := 2
  storedRight := 0
  conclusion := 4
  side := .storedLeft
  link_eq := by native_decide
  premise_eq := rfl

private theorem wait_enabled :
    SequentialFigure7.WaitEnabled
      waitSchedulerCertificate waitStableReadyState := by
  exact ⟨{
    head := waitStableHead
    par := waitStableSubmitted
    mateRawAge := 0
    mate_marked := by native_decide
    younger := by decide }⟩

/-- The real `init → nop → new` state is a full-invariant positive
`wait` case.  The enabled witness stores neither its derived boundary `0` nor
the initialized empty payload; the invariant supplies both. -/
example :
    (∃ next,
      SequentialFigure7.wait? waitSchedulerCertificate waitStableReadyState
          waitStableReadyState_invariant.toReservationInvariant = some next ∧
        SchedulerInvariant waitSchedulerCertificate next) ∧
      ¬ SequentialFigure7.ForwardEnabled
        waitSchedulerCertificate waitStableReadyState := by
  constructor
  · exact SequentialFigure7.wait?_exists_schedulerInvariant_of_enabled
      waitStableReadyState_invariant wait_enabled
  · intro enabled
    rcases SequentialFigure7.forward?_exists_of_enabled
        waitStableReadyState_invariant enabled with
      ⟨next, equation⟩
    have failure :
        SequentialFigure7.forward? waitSchedulerCertificate
            waitStableReadyState
            waitStableReadyState_invariant.toReservationInvariant = none := by
      native_decide
    rw [failure] at equation
    simp at equation

/-- The scoped exact-par classification is available on the same genuine
wait fixture without asserting anything about non-par scheduler states. -/
example :
    SequentialFigure7.NopEnabled
        waitSchedulerCertificate waitStableReadyState ∨
      SequentialFigure7.WaitEnabled
          waitSchedulerCertificate waitStableReadyState ∨
        SequentialFigure7.ForwardEnabled
          waitSchedulerCertificate waitStableReadyState :=
  SequentialFigure7.submittedParInput_enabled_cases
    waitStableReadyState_invariant waitStableHead waitStableSubmitted

private def parAfterForwardStableState : ReservationState :=
  match SequentialFigure7.forward? parCertificate parForwardStableState
      parForwardStableState_invariant.toReservationInvariant with
  | some state => state
  | none => ReservationState.empty parCertificate

private theorem parAfterForwardStableState_eq :
    SequentialFigure7.forward? parCertificate parForwardStableState
        parForwardStableState_invariant.toReservationInvariant =
      some parAfterForwardStableState := by
  native_decide

private theorem parAfterForwardStableState_invariant :
    SchedulerInvariant parCertificate parAfterForwardStableState :=
  SequentialFigure7.forward?_schedulerInvariant
    parForwardStableState_invariant parAfterForwardStableState_eq

private def parCompletedStableState : ReservationState :=
  match SequentialFigure7.concl? parCertificate parAfterForwardStableState
      parAfterForwardStableState_invariant.toReservationInvariant with
  | some state => state
  | none => ReservationState.empty parCertificate

private theorem parCompletedStableState_eq :
    SequentialFigure7.concl? parCertificate parAfterForwardStableState
        parAfterForwardStableState_invariant.toReservationInvariant =
      some parCompletedStableState := by
  native_decide

private theorem parCompletedStableState_invariant :
    SchedulerInvariant parCertificate parCompletedStableState :=
  SequentialFigure7.concl?_schedulerInvariant
    parAfterForwardStableState_invariant parCompletedStableState_eq

/-- The completed reachable par state retains the aligned empty ready bucket
`[[]]`.  It satisfies full `SchedulerInvariant` but has no nonempty ready head
and therefore enables none of the four stable predicates. -/
example :
    parCompletedStableState.stack.ready = [[]] ∧
      SchedulerInvariant parCertificate parCompletedStableState ∧
      ¬ SequentialFigure7.ConclEnabled
        parCertificate parCompletedStableState ∧
      ¬ SequentialFigure7.NopEnabled
        parCertificate parCompletedStableState ∧
      ¬ SequentialFigure7.WaitEnabled
        parCertificate parCompletedStableState ∧
      ¬ SequentialFigure7.ForwardEnabled
        parCertificate parCompletedStableState := by
  have readyEquation : parCompletedStableState.stack.ready = [[]] := by
    native_decide
  have noHead :
      ¬ Nonempty
        (SequentialFigure7.ReadyHeadInput parCompletedStableState) := by
    rintro ⟨head⟩
    have emptyTop :
        parCompletedStableState.stack.ready.getLast? = some [] := by
      rw [readyEquation]
      rfl
    have topEquation := head.top_ready
    rw [emptyTop] at topEquation
    simp at topEquation
  refine ⟨readyEquation, parCompletedStableState_invariant,
    ?_, ?_, ?_, ?_⟩
  · rintro ⟨input⟩
    exact noHead ⟨input.head⟩
  · rintro ⟨input⟩
    exact noHead ⟨input.head⟩
  · rintro ⟨input⟩
    exact noHead ⟨input.head⟩
  · rintro ⟨input⟩
    exact noHead ⟨input.head⟩

private def repeatedStableState : ReservationState :=
  match repeatedInitial with
  | some state => state
  | none => ReservationState.empty repeatedOccurrenceCertificate

private theorem repeatedStableState_eq :
    repeatedInitial = some repeatedStableState := by
  native_decide

private theorem repeatedStableState_invariant :
    SchedulerInvariant repeatedOccurrenceCertificate repeatedStableState :=
  repeatedInitial_schedulerInvariant repeatedStableState_eq

private def repeatedAfterNewStableState : ReservationState :=
  match SequentialFigure7.new? repeatedOccurrenceCertificate
      repeatedStableState
      repeatedStableState_invariant.toReservationInvariant with
  | some state => state
  | none => ReservationState.empty repeatedOccurrenceCertificate

private theorem repeatedAfterNewStableState_eq :
    SequentialFigure7.new? repeatedOccurrenceCertificate repeatedStableState
        repeatedStableState_invariant.toReservationInvariant =
      some repeatedAfterNewStableState := by
  native_decide

private theorem repeatedAfterNewStableState_invariant :
    SchedulerInvariant repeatedOccurrenceCertificate
      repeatedAfterNewStableState :=
  SequentialFigure7.new?_schedulerInvariant
    repeatedStableState_invariant repeatedAfterNewStableState_eq

/-- The genuine repeated-occurrence `new` fixture exposes a complete
`NEXTAXIOM` trace whose every occurrence was unmarked in the exact post-pop,
post-selected-mark input core. -/
example :
    ∃ step :
        SequentialFigure7.NewStep repeatedOccurrenceCertificate
          repeatedStableState repeatedAfterNewStableState,
      ∀ {vertex : Vertex}, vertex ∈ step.search.trace →
        step.coreMarked.marks[vertex]? = some none := by
  rcases
      (SequentialFigure7.new?_some_iff
        repeatedStableState_invariant.toReservationInvariant).mp
          repeatedAfterNewStableState_eq with
    ⟨step⟩
  exact ⟨step,
    SequentialUnification.nextAxiom?_traceReady step.search_eq⟩

private def repeatedAfterUnifyStableState : ReservationState :=
  match SequentialFigure7.unifyPayload? repeatedOccurrenceCertificate
      repeatedAfterNewStableState
      repeatedAfterNewStableState_invariant.toReservationInvariant with
  | some state => state
  | none => ReservationState.empty repeatedOccurrenceCertificate

private theorem repeatedAfterUnifyStableState_eq :
    SequentialFigure7.unifyPayload? repeatedOccurrenceCertificate
        repeatedAfterNewStableState
        repeatedAfterNewStableState_invariant.toReservationInvariant =
      some repeatedAfterUnifyStableState := by
  native_decide

/-- Full scheduler validity does not make the stable-par/conclusion family
exhaustive.  This genuine tensor state enables none of the four predicates;
the implemented `new` executor succeeds, and the resulting state then executes
the general `unifyPayload` rule outside this stable classification. -/
example :
    SchedulerInvariant repeatedOccurrenceCertificate repeatedStableState ∧
      ¬ SequentialFigure7.ConclEnabled
        repeatedOccurrenceCertificate repeatedStableState ∧
      ¬ SequentialFigure7.NopEnabled
        repeatedOccurrenceCertificate repeatedStableState ∧
      ¬ SequentialFigure7.WaitEnabled
        repeatedOccurrenceCertificate repeatedStableState ∧
      ¬ SequentialFigure7.ForwardEnabled
        repeatedOccurrenceCertificate repeatedStableState ∧
      SequentialFigure7.new? repeatedOccurrenceCertificate repeatedStableState
          repeatedStableState_invariant.toReservationInvariant =
        some repeatedAfterNewStableState ∧
      SequentialFigure7.unifyPayload? repeatedOccurrenceCertificate
          repeatedAfterNewStableState
          repeatedAfterNewStableState_invariant.toReservationInvariant =
        some repeatedAfterUnifyStableState := by
  have rejectConcl :
      ¬ SequentialFigure7.ConclEnabled
        repeatedOccurrenceCertificate repeatedStableState := by
    intro enabled
    rcases SequentialFigure7.concl?_exists_of_enabled
        repeatedStableState_invariant enabled with ⟨next, equation⟩
    have failure :
        SequentialFigure7.concl? repeatedOccurrenceCertificate
            repeatedStableState
            repeatedStableState_invariant.toReservationInvariant = none := by
      native_decide
    rw [failure] at equation
    simp at equation
  have rejectNop :
      ¬ SequentialFigure7.NopEnabled
        repeatedOccurrenceCertificate repeatedStableState := by
    intro enabled
    rcases SequentialFigure7.nop?_exists_of_enabled
        repeatedStableState_invariant enabled with ⟨next, equation⟩
    have failure :
        SequentialFigure7.nop? repeatedOccurrenceCertificate
            repeatedStableState
            repeatedStableState_invariant.toReservationInvariant = none := by
      native_decide
    rw [failure] at equation
    simp at equation
  have rejectWait :
      ¬ SequentialFigure7.WaitEnabled
        repeatedOccurrenceCertificate repeatedStableState := by
    intro enabled
    rcases SequentialFigure7.wait?_exists_of_enabled
        repeatedStableState_invariant enabled with ⟨next, equation⟩
    have failure :
        SequentialFigure7.wait? repeatedOccurrenceCertificate
            repeatedStableState
            repeatedStableState_invariant.toReservationInvariant = none := by
      native_decide
    rw [failure] at equation
    simp at equation
  have rejectForward :
      ¬ SequentialFigure7.ForwardEnabled
        repeatedOccurrenceCertificate repeatedStableState := by
    intro enabled
    rcases SequentialFigure7.forward?_exists_of_enabled
        repeatedStableState_invariant enabled with ⟨next, equation⟩
    have failure :
        SequentialFigure7.forward? repeatedOccurrenceCertificate
            repeatedStableState
            repeatedStableState_invariant.toReservationInvariant = none := by
      native_decide
    rw [failure] at equation
    simp at equation
  exact ⟨repeatedStableState_invariant, rejectConcl, rejectNop,
    rejectWait, rejectForward, repeatedAfterNewStableState_eq,
    repeatedAfterUnifyStableState_eq⟩

/-! Exact fixed-precedence applicability for the canonical dispatcher. -/

/-- On a genuine initialized full-invariant state, existential conclusion
execution is exactly the pure input-only conclusion predicate, and the
canonical dispatcher selects that first-priority branch. -/
example :
    ((∃ after,
        SequentialFigure7.concl? axiomCertificate axiomStableState
            axiomStableState_invariant.toReservationInvariant = some after) ↔
      SequentialFigure7.ConclEnabled axiomCertificate axiomStableState) ∧
      SequentialFigure7.PriorityEnabled axiomCertificate axiomStableState
        axiomStableState_invariant .concl ∧
      ∃ after,
        SequentialFigure7.dispatch? axiomCertificate axiomStableState
            axiomStableState_invariant = some ⟨.concl, after⟩ := by
  refine ⟨SequentialFigure7.concl?_success_iff_enabled
      axiomStableState_invariant, ?_, ?_⟩
  · exact SequentialFigure7.PriorityEnabled.concl axiom_concl_enabled
  · exact
      (SequentialFigure7.dispatch?_kind_success_iff_priorityEnabled
        axiomStableState_invariant .concl).mpr
        (SequentialFigure7.PriorityEnabled.concl axiom_concl_enabled)

/-- The real tensor fixture is selected as the operational `new` branch.
This checks the mixed input-only/operational priority boundary without calling
it an input-only `new` predicate. -/
example :
    SequentialFigure7.NewExecutableEnabled repeatedOccurrenceCertificate
        repeatedStableState repeatedStableState_invariant ∧
      SequentialFigure7.PriorityEnabled repeatedOccurrenceCertificate
        repeatedStableState repeatedStableState_invariant .new ∧
      ∃ after,
        SequentialFigure7.dispatch? repeatedOccurrenceCertificate
            repeatedStableState repeatedStableState_invariant =
          some ⟨.new, after⟩ := by
  have selected :
      ∃ after,
        SequentialFigure7.dispatch? repeatedOccurrenceCertificate
            repeatedStableState repeatedStableState_invariant =
          some ⟨.new, after⟩ := by
    exact ⟨repeatedAfterNewStableState, by native_decide⟩
  have priority :=
    (SequentialFigure7.dispatch?_kind_success_iff_priorityEnabled
      repeatedStableState_invariant .new).mp selected
  exact ⟨⟨repeatedAfterNewStableState, repeatedAfterNewStableState_eq⟩,
    priority, selected⟩

/-! Input-state necessary conditions for Figure-7 `new`. -/

private def repeatedNewTensor : TensorBelow where
  linkIndex := 2
  storedLeft := 0
  storedRight := 2
  conclusion := 4
  side := .storedLeft

private def repeatedNewHead :
    SequentialFigure7.ReadyHeadInput repeatedStableState where
  vertex := 0
  readyTail := [1]
  rawAge := 0
  top_ready := by native_decide
  sigma_top := by native_decide

private def repeatedNewGuard :
    SequentialFigure7.NewGuard repeatedOccurrenceCertificate
      repeatedStableState where
  head := repeatedNewHead
  tensor := repeatedNewTensor
  tensor_valid :=
    Certificate.tensorBelow?_eq_some_iff.mp (by native_decide)
  mate_unmarked := by native_decide

/-- A genuine successful `new` reconstructs both the shallow guard and the
result-free, equation-free fresh source-left route.  This is the proved
one-way implication, not later-`NEXTAXIOM` totality. -/
example :
    SequentialFigure7.NewInputNecessary repeatedOccurrenceCertificate
      repeatedStableState :=
  SequentialFigure7.new?_success_implies_inputNecessary
    repeatedStableState_invariant.toReservationInvariant
    repeatedAfterNewStableState_eq

private def repeatedAllTrueStableState : ReservationState :=
  repeatedAllTrueTags repeatedStableState

private theorem repeatedAllTrueStableState_invariant :
    SchedulerInvariant repeatedOccurrenceCertificate
      repeatedAllTrueStableState := by
  exact {
    repeatedStableState_invariant with
    toReservationInvariant := {
      repeatedStableState_invariant.toReservationInvariant with
      tags_size := by simp [repeatedAllTrueStableState, repeatedAllTrueTags] } }

private def repeatedAllTrueHead :
    SequentialFigure7.ReadyHeadInput repeatedAllTrueStableState where
  vertex := 0
  readyTail := [1]
  rawAge := 0
  top_ready := by native_decide
  sigma_top := by native_decide

private def repeatedAllTrueGuard :
    SequentialFigure7.NewGuard repeatedOccurrenceCertificate
      repeatedAllTrueStableState where
  head := repeatedAllTrueHead
  tensor := repeatedNewTensor
  tensor_valid :=
    Certificate.tensorBelow?_eq_some_iff.mp (by native_decide)
  mate_unmarked := by native_decide

/-- Same-sized all-true forged tags do not affect the deliberately shallow
guard, but they make `NEXTAXIOM` fail immediately.  The combined input-only
`NewInputNecessary` predicate rejects the state because its route start is not fresh.
No claim is made that this forged state is reachable. -/
example :
    Nonempty
        (SequentialFigure7.NewGuard repeatedOccurrenceCertificate
          repeatedAllTrueStableState) ∧
      ¬ SequentialFigure7.NewInputNecessary repeatedOccurrenceCertificate
        repeatedAllTrueStableState ∧
      SequentialFigure7.new? repeatedOccurrenceCertificate
          repeatedAllTrueStableState
          repeatedAllTrueStableState_invariant.toReservationInvariant = none := by
  refine ⟨⟨repeatedAllTrueGuard⟩, ?_, by native_decide⟩
  rintro ⟨input⟩
  have fresh := input.route.startFresh
  have bound : input.guard.tensor.mate < 5 :=
    (Array.getElem?_eq_some_iff.mp fresh).1
  have trueAt :
      (Array.replicate 5 true)[input.guard.tensor.mate]? = some true := by
    simp [bound]
  have freshAllTrue :
      (Array.replicate 5 true)[input.guard.tensor.mate]? = some false := by
    simpa [repeatedAllTrueStableState, repeatedAllTrueTags,
      repeatedOccurrenceCertificate] using fresh
  rw [trueAt] at freshAllTrue
  simp at freshAllTrue

private def repeatedPartnerTaggedState : ReservationState :=
  { repeatedStableState with
    tags := repeatedStableState.tags.setIfInBounds 3 true }

private theorem repeatedPartnerTaggedState_invariant :
    SchedulerInvariant repeatedOccurrenceCertificate
      repeatedPartnerTaggedState := by
  exact {
    repeatedStableState_invariant with
    toReservationInvariant := {
      repeatedStableState_invariant.toReservationInvariant with
      tags_size := by
        simp [repeatedPartnerTaggedState,
          repeatedStableState_invariant.toReservationInvariant.tags_size] } }

private def repeatedPartnerTaggedHead :
    SequentialFigure7.ReadyHeadInput repeatedPartnerTaggedState where
  vertex := 0
  readyTail := [1]
  rawAge := 0
  top_ready := by native_decide
  sigma_top := by native_decide

private def repeatedPartnerTaggedGuard :
    SequentialFigure7.NewGuard repeatedOccurrenceCertificate
      repeatedPartnerTaggedState where
  head := repeatedPartnerTaggedHead
  tensor := repeatedNewTensor
  tensor_valid :=
    Certificate.tensorBelow?_eq_some_iff.mp (by native_decide)
  mate_unmarked := by native_decide

/-- Pretagging only the terminal axiom partner leaves the ready/tensor/mate
guard intact while the executor fails at the deeper route endpoint.  This is a
concrete regression against treating `NewGuard` as sufficient. -/
example :
    Nonempty
        (SequentialFigure7.NewGuard repeatedOccurrenceCertificate
          repeatedPartnerTaggedState) ∧
      SequentialFigure7.new? repeatedOccurrenceCertificate
          repeatedPartnerTaggedState
          repeatedPartnerTaggedState_invariant.toReservationInvariant = none := by
  exact ⟨⟨repeatedPartnerTaggedGuard⟩, by native_decide⟩

/-- The exact pre-initialization state has no ready head, hence neither a
shallow `NewGuard` nor the stronger input-only `NewInputNecessary`. -/
example :
    let state := ReservationState.empty repeatedOccurrenceCertificate
    ¬ Nonempty
        (SequentialFigure7.NewGuard repeatedOccurrenceCertificate state) ∧
      ¬ SequentialFigure7.NewInputNecessary repeatedOccurrenceCertificate state := by
  let state := ReservationState.empty repeatedOccurrenceCertificate
  have noHead :
      ¬ Nonempty (SequentialFigure7.ReadyHeadInput state) := by
    rintro ⟨head⟩
    simpa [state, ReservationState.empty, SequentialStackState.empty] using
      head.top_ready
  constructor
  · rintro ⟨guard⟩
    exact noHead ⟨guard.head⟩
  · rintro ⟨input⟩
    exact noHead ⟨input.guard.head⟩

/-- The genuine completed `[[]]` state has no ready head and therefore no
`NewGuard` or `NewInputNecessary`.  This remains a terminal boundary, not a global
progress theorem. -/
example :
    ¬ Nonempty
        (SequentialFigure7.NewGuard parCertificate parCompletedStableState) ∧
      ¬ SequentialFigure7.NewInputNecessary parCertificate
        parCompletedStableState := by
  have readyEquation : parCompletedStableState.stack.ready = [[]] := by
    native_decide
  have noHead :
      ¬ Nonempty
        (SequentialFigure7.ReadyHeadInput parCompletedStableState) := by
    rintro ⟨head⟩
    have emptyTop :
        parCompletedStableState.stack.ready.getLast? = some [] := by
      rw [readyEquation]
      rfl
    have topReady := head.top_ready
    rw [emptyTop] at topReady
    simp at topReady
  constructor
  · rintro ⟨guard⟩
    exact noHead ⟨guard.head⟩
  · rintro ⟨input⟩
    exact noHead ⟨input.guard.head⟩

/-- A completed full-invariant state obtained by the existing rule chain can
have the aligned empty ready bucket and no selected rule.  This refutes only
invariant-implies-branch; it is not a counterexample to terminal-qualified
progress. -/
example :
    parCompletedStableState.stack.ready = [[]] ∧
      SchedulerInvariant parCertificate parCompletedStableState ∧
      SequentialFigure7.dispatch? parCertificate parCompletedStableState
          parCompletedStableState_invariant = none ∧
      ∀ kind,
        ¬ SequentialFigure7.PriorityEnabled parCertificate
          parCompletedStableState parCompletedStableState_invariant kind := by
  have dispatchNone :
      SequentialFigure7.dispatch? parCertificate parCompletedStableState
          parCompletedStableState_invariant = none := by
    native_decide
  exact ⟨by native_decide, parCompletedStableState_invariant, dispatchNone,
    (SequentialFigure7.dispatch?_eq_none_iff_forall_not_priorityEnabled
      parCompletedStableState_invariant).mp dispatchNone⟩

end Figure7PrimitivesTests

end ProofNetIR

def main : IO Unit :=
  IO.println "Figure-7 pop/raw-mark primitive tests passed"
