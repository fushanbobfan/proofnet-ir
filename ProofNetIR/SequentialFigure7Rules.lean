import ProofNetIR.SequentialConsumerIndex
import ProofNetIR.SequentialSchedulerBridge

namespace ProofNetIR

/-!
# Executable Figure-7 base rules

This module starts the common non-`init` rule layer of Guerrini's Figure 7.
It deliberately keeps three distinctions executable:

* a declared conclusion is locally ownership-well-formed and has an exactly
  empty consumer bucket;
* a premise occurrence has one exact submitted par or tensor consumer;
* a malformed nonempty/non-singleton bucket is neither of those cases.

The common prefix pops one occurrence from the top ready bucket and raw-marks
it at the old active `sigma` boundary in both delayed and production views.
The first three complete local rules built from that prefix are:

* `concl`: the selected occurrence is an explicit conclusion with no consumer;
* `nop`: the selected occurrence is a par premise whose mate is still raw
  unmarked;
* `wait`: the selected occurrence is a par premise whose mate carries a
  strictly older raw age, and the par conclusion is prepended to the
  initialized waiting bucket selected by `sigmaBoundary?`.

`concl` and `nop` perform only the common prefix; `wait` additionally performs
one exact waiting cons update. Par forwarding, tensor unification, global
payload ownership, full-rule reachability, and progress remain separate.
-/

/-- The submitted binary connective constructor retained by a generic
consumer-below view. -/
inductive SequentialConnectiveKind where
  | «par»
  | tensor
  deriving Repr, DecidableEq, BEq

namespace SequentialConnectiveKind

/-- Reconstruct the exact submitted link represented by a generic view. -/
def asLink : SequentialConnectiveKind →
    Vertex → Vertex → Vertex → Link
  | .par, left, right, conclusion =>
      .par left right conclusion
  | .tensor, left, right, conclusion =>
      .tensor left right conclusion

end SequentialConnectiveKind

/-- Proof-carrying exact view of the unique submitted connective consuming one
formula occurrence.

The result retains the submitted link index, constructor, stored orientation,
local well-formedness, and the exact queried premise.  Because the canonical
consumer index is fixed in the type, callers cannot supply a partial table
that hides a competing consumer. -/
structure ConnectiveBelow (certificate : Certificate)
    (vertex : Vertex) : Type where
  linkIndex : Nat
  kind : SequentialConnectiveKind
  storedLeft : Vertex
  storedRight : Vertex
  conclusion : Vertex
  side : TensorPremiseSide
  consumer_eq :
    certificate.consumerIndex.uniqueConsumer? vertex =
      some linkIndex
  link_eq :
    certificate.links[linkIndex]? =
      some (kind.asLink storedLeft storedRight conclusion)
  wellFormed :
    certificate.LinkWellFormed
      (kind.asLink storedLeft storedRight conclusion)
  premise_eq :
    vertex = side.premise storedLeft storedRight

namespace ConnectiveBelow

/-- Stored premise addressed by the generic connective view. -/
def premise {certificate : Certificate} {vertex : Vertex}
    (result : ConnectiveBelow certificate vertex) : Vertex :=
  result.side.premise result.storedLeft result.storedRight

/-- Opposite premise addressed by the generic connective view. -/
def mate {certificate : Certificate} {vertex : Vertex}
    (result : ConnectiveBelow certificate vertex) : Vertex :=
  result.side.mate result.storedLeft result.storedRight

/-- Exact submitted link retained by the view. -/
def submittedLink {certificate : Certificate} {vertex : Vertex}
    (result : ConnectiveBelow certificate vertex) : Link :=
  result.kind.asLink
    result.storedLeft result.storedRight result.conclusion

/-- A successful generic connective view never returns its queried premise as
its mate. -/
theorem mate_ne {certificate : Certificate} {vertex : Vertex}
    (result : ConnectiveBelow certificate vertex) :
    result.mate ≠ vertex := by
  have different :
      result.storedLeft ≠ result.storedRight := by
    cases kindEquation : result.kind with
    | par =>
        have wellFormed := result.wellFormed
        simp only [SequentialConnectiveKind.asLink, kindEquation,
          Certificate.LinkWellFormed] at wellFormed
        exact wellFormed.1
    | tensor =>
        have wellFormed := result.wellFormed
        simp only [SequentialConnectiveKind.asLink, kindEquation,
          Certificate.LinkWellFormed] at wellFormed
        exact wellFormed.1
  have input := result.premise_eq
  cases sideEquation : result.side with
  | storedLeft =>
      simp [mate, TensorPremiseSide.mate,
        TensorPremiseSide.premise, sideEquation] at input ⊢
      exact fun same => different (input.symm.trans same.symm)
  | storedRight =>
      simp [mate, TensorPremiseSide.mate,
        TensorPremiseSide.premise, sideEquation] at input ⊢
      exact fun same => different (same.trans input)

end ConnectiveBelow

private def connectiveBelowAt? (certificate : Certificate)
    (vertex linkIndex : Nat)
    (consumerEquation :
      certificate.consumerIndex.uniqueConsumer? vertex =
        some linkIndex) :
    Option (ConnectiveBelow certificate vertex) :=
  match linkEquation : certificate.links[linkIndex]? with
  | some (.par left right conclusion) =>
      if wellFormed :
          certificate.linkLocallyWellFormed
            (.par left right conclusion) = true then
        if storedLeft : vertex = left then
          some {
            linkIndex
            kind := .par
            storedLeft := left
            storedRight := right
            conclusion
            side := .storedLeft
            consumer_eq := consumerEquation
            link_eq := by
              simpa [SequentialConnectiveKind.asLink] using linkEquation
            wellFormed :=
              (certificate.linkLocallyWellFormed_iff
                (.par left right conclusion)).mp wellFormed
            premise_eq := by
              simpa [TensorPremiseSide.premise] using storedLeft }
        else if storedRight : vertex = right then
          some {
            linkIndex
            kind := .par
            storedLeft := left
            storedRight := right
            conclusion
            side := .storedRight
            consumer_eq := consumerEquation
            link_eq := by
              simpa [SequentialConnectiveKind.asLink] using linkEquation
            wellFormed :=
              (certificate.linkLocallyWellFormed_iff
                (.par left right conclusion)).mp wellFormed
            premise_eq := by
              simpa [TensorPremiseSide.premise] using storedRight }
        else
          none
      else
        none
  | some (.tensor left right conclusion) =>
      if wellFormed :
          certificate.linkLocallyWellFormed
            (.tensor left right conclusion) = true then
        if storedLeft : vertex = left then
          some {
            linkIndex
            kind := .tensor
            storedLeft := left
            storedRight := right
            conclusion
            side := .storedLeft
            consumer_eq := consumerEquation
            link_eq := by
              simpa [SequentialConnectiveKind.asLink] using linkEquation
            wellFormed :=
              (certificate.linkLocallyWellFormed_iff
                (.tensor left right conclusion)).mp wellFormed
            premise_eq := by
              simpa [TensorPremiseSide.premise] using storedLeft }
        else if storedRight : vertex = right then
          some {
            linkIndex
            kind := .tensor
            storedLeft := left
            storedRight := right
            conclusion
            side := .storedRight
            consumer_eq := consumerEquation
            link_eq := by
              simpa [SequentialConnectiveKind.asLink] using linkEquation
            wellFormed :=
              (certificate.linkLocallyWellFormed_iff
                (.tensor left right conclusion)).mp wellFormed
            premise_eq := by
              simpa [TensorPremiseSide.premise] using storedRight }
        else
          none
      else
        none
  | _ => none

namespace Certificate

/-- Canonical generic connective-below lookup.

An empty bucket, a non-singleton bucket, an axiom slot, a malformed submitted
link, or a vertex that is not the retained stored premise all fail closed. -/
def connectiveBelow? (certificate : Certificate)
    (vertex : Vertex) :
    Option (ConnectiveBelow certificate vertex) :=
  match consumerEquation :
      certificate.consumerIndex.uniqueConsumer? vertex with
  | none => none
  | some linkIndex =>
      connectiveBelowAt? certificate vertex linkIndex consumerEquation

end Certificate

/-- Proof-carrying locally ownership-well-formed conclusion view.

Besides declared boundary membership, this view requires the certificate's
local node-ownership condition: the occurrence is in bounds, has exactly one
source incidence/producer of the appropriate shape, and has no parent use.
The empty canonical-consumer-bucket equation is also stored directly.  In
particular,
`uniqueConsumer? = none` is not accepted as a substitute, because that query
also returns `none` for a malformed bucket containing distinct candidates. -/
structure ConclusionBelow (certificate : Certificate)
    (vertex : Vertex) : Type where
  boundary : vertex ∈ certificate.conclusions
  nodeWellFormed : certificate.NodeWellFormed vertex
  noConsumer :
    certificate.consumerIndex.bucket vertex = []

namespace ConclusionBelow

/-- A locally well-formed conclusion view and an exact connective-consumer
view cannot describe the same occurrence. -/
theorem not_connective
    {certificate : Certificate} {vertex : Vertex}
    (boundary : ConclusionBelow certificate vertex)
    (consumer : ConnectiveBelow certificate vertex) :
    False := by
  have membership :
      consumer.linkIndex ∈
        certificate.consumerIndex.bucket vertex :=
    (ConsumerIndex.uniqueConsumer?_eq_some_iff.mp
      consumer.consumer_eq).1
  rw [boundary.noConsumer] at membership
  simp at membership

end ConclusionBelow

namespace Certificate

/-- Canonical locally well-formed conclusion query with an exact empty
consumer bucket. -/
def conclusionBelow? (certificate : Certificate)
    (vertex : Vertex) :
    Option (ConclusionBelow certificate vertex) :=
  if boundary : vertex ∈ certificate.conclusions then
    if nodeWellFormed :
        certificate.nodeWellFormed vertex = true then
      if noConsumer :
          certificate.consumerIndex.bucket vertex = [] then
        some {
          boundary
          nodeWellFormed :=
            (certificate.nodeWellFormed_iff vertex).mp
              nodeWellFormed
          noConsumer }
      else
        none
    else
      none
  else
    none

end Certificate

namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge

/-- Proof-carrying synchronized common prefix of every non-`init` Figure-7
rule. -/
structure PreparedStep (before : ReservationState) : Type where
  stackResult : PopReadyMarkResult
  coreMarked : UnificationState
  stack_eq :
    before.stack.popReadyMark? = .ok stackResult
  core_mark_eq :
    before.core.markReadyRaw?
        stackResult.vertex stackResult.rawAge =
      .ok coreMarked

namespace PreparedStep

/-- Exact state after the common pop/raw-mark prefix. -/
def after {before : ReservationState}
    (step : PreparedStep before) : ReservationState where
  stack := step.stackResult.after
  core := step.coreMarked
  tags := before.tags

/-- The common prefix preserves the current reservation invariant. -/
theorem reservationInvariant
    {certificate : Certificate} {before : ReservationState}
    (step : PreparedStep before)
    (invariant : ReservationInvariant certificate before) :
    ReservationInvariant certificate step.after :=
  popReadyMark_markReadyRaw_reservationInvariant
    invariant step.stack_eq step.core_mark_eq

end PreparedStep

/-- Execute the common pop/raw-mark prefix without selecting a later rule. -/
def prepare? (before : ReservationState) :
    Option (PreparedStep before) :=
  match stackEquation : before.stack.popReadyMark? with
  | .error _ => none
  | .ok stackResult =>
      match coreEquation :
          before.core.markReadyRaw?
            stackResult.vertex stackResult.rawAge with
      | .error _ => none
      | .ok coreMarked =>
          some {
            stackResult
            coreMarked
            stack_eq := stackEquation
            core_mark_eq := coreEquation }

private theorem exists_prepare?_eq_some_of_ok
    {before : ReservationState}
    {stackResult : PopReadyMarkResult}
    {coreMarked : UnificationState}
    (stackEquation :
      before.stack.popReadyMark? = .ok stackResult)
    (coreEquation :
      before.core.markReadyRaw?
          stackResult.vertex stackResult.rawAge =
        .ok coreMarked) :
    ∃ prepared, prepare? before = some prepared := by
  let prepared : PreparedStep before := {
    stackResult
    coreMarked
    stack_eq := stackEquation
    core_mark_eq := coreEquation }
  refine ⟨prepared, ?_⟩
  unfold prepare?
  split
  next stackError stackFailure =>
    rw [stackEquation] at stackFailure
    simp at stackFailure
  next actualStack stackSuccess =>
    have actualStackEq : actualStack = stackResult :=
      Except.ok.inj (stackSuccess.symm.trans stackEquation)
    subst actualStack
    split
    next coreError coreFailure =>
      rw [coreEquation] at coreFailure
      simp at coreFailure
    next actualCore coreSuccess =>
      have actualCoreEq : actualCore = coreMarked :=
        Except.ok.inj (coreSuccess.symm.trans coreEquation)
      subst actualCore
      congr 2

/-- Independent proposition-level meaning of the synchronized common prefix
at one selected occurrence and raw age.

This relation does not mention `prepare?`, either executable query, or either
rule executable.  It directly states the list decomposition selected by the
concrete scheduler policy and the two synchronized raw-mark updates. -/
def RulePrefixAt (before after : ReservationState)
    (vertex : Vertex) (rawAge : RawTokenAge) : Prop :=
  ∃ (readyPrefix : List (List Vertex))
      (readyTail : List Vertex)
      (sigmaPrefix : List RawTokenAge),
    before.stack.ready =
        readyPrefix ++ [vertex :: readyTail] ∧
    before.stack.sigma =
        sigmaPrefix ++ [rawAge] ∧
    before.stack.marks[vertex]? = some none ∧
    before.core.marks[vertex]? = some none ∧
    after.stack = {
      before.stack with
      marks :=
        before.stack.marks.setIfInBounds vertex (some rawAge)
      ready := readyPrefix ++ [readyTail] } ∧
    after.core = {
      before.core with
      marks :=
        before.core.marks.setIfInBounds vertex (some rawAge) } ∧
    after.tags = before.tags

/-- Existential form of the independent common-prefix relation. -/
def RulePrefix (before after : ReservationState) : Prop :=
  ∃ vertex rawAge, RulePrefixAt before after vertex rawAge

namespace RulePrefix

/-- Every successful executable prefix realizes the independent direct state
relation. -/
theorem ofPrepared
    {before : ReservationState}
    (prepared : PreparedStep before) :
    RulePrefixAt before prepared.after
      prepared.stackResult.vertex prepared.stackResult.rawAge := by
  rcases
      SequentialStackState.popReadyMark?_ok_iff.mp
        prepared.stack_eq with
    ⟨stackStep⟩
  rcases
      UnificationState.markReadyRaw?_ok_iff.mp
        prepared.core_mark_eq with
    ⟨coreStep⟩
  rcases List.getLast?_eq_some_iff.mp stackStep.top_eq with
    ⟨readyPrefix, readyEquation⟩
  rcases List.getLast?_eq_some_iff.mp stackStep.sigma_top_eq with
    ⟨sigmaPrefix, sigmaEquation⟩
  refine ⟨readyPrefix, prepared.stackResult.remainingTop,
    sigmaPrefix, readyEquation, sigmaEquation,
    stackStep.unmarked, coreStep.unmarked, ?_, ?_, rfl⟩
  ·
      simp [PreparedStep.after, stackStep.after_eq,
        readyEquation]
  · simp [PreparedStep.after, coreStep.after_eq]

/-- The direct common-prefix relation has a unique output for a fixed input. -/
theorem output_unique
    {before first second : ReservationState}
    (left : RulePrefix before first)
    (right : RulePrefix before second) :
    first = second := by
  rcases left with ⟨leftVertex, leftAge, leftRule⟩
  rcases right with ⟨rightVertex, rightAge, rightRule⟩
  rcases leftRule with
    ⟨leftReadyPrefix, leftReadyTail, leftSigmaPrefix,
      leftReady, leftSigma, _leftStackUnmarked,
      _leftCoreUnmarked, leftStack, leftCore, leftTags⟩
  rcases rightRule with
    ⟨rightReadyPrefix, rightReadyTail, rightSigmaPrefix,
      rightReady, rightSigma, _rightStackUnmarked,
      _rightCoreUnmarked, rightStack, rightCore, rightTags⟩
  have readySame :
      leftVertex :: leftReadyTail =
        rightVertex :: rightReadyTail := by
    have sameLast :=
      congrArg List.getLast? (leftReady.symm.trans rightReady)
    simpa using sameLast
  have vertexSame : leftVertex = rightVertex :=
    List.cons.inj readySame |>.1
  have tailSame : leftReadyTail = rightReadyTail :=
    List.cons.inj readySame |>.2
  have readyPrefixSame :
      leftReadyPrefix = rightReadyPrefix := by
    have sameDropLast :=
      congrArg List.dropLast (leftReady.symm.trans rightReady)
    simpa using sameDropLast
  have ageSame : leftAge = rightAge := by
    have sameLast :=
      congrArg List.getLast? (leftSigma.symm.trans rightSigma)
    simpa using sameLast
  subst rightVertex
  subst rightReadyTail
  subst rightReadyPrefix
  subst rightAge
  cases first
  cases second
  simp_all

end RulePrefix

/-- Independent Boolean-free local Figure-7 `concl` relation for the
unit-free certificate model.  On structurally valid input, declared boundary
membership already entails that the occurrence has no consumer. -/
def ConclRule (certificate : Certificate)
    (before after : ReservationState) : Prop :=
  ∃ vertex rawAge,
    RulePrefixAt before after vertex rawAge ∧
    vertex ∈ certificate.conclusions

/-- Independent Boolean-free local Figure-7 `nop` relation.  The exact
submitted par slot and its stored premise orientation are retained, while the
paper guard is stated in the pre-prefix raw mark state. -/
def NopRule (certificate : Certificate)
    (before after : ReservationState) : Prop :=
  ∃ (vertex rawAge linkIndex storedLeft storedRight conclusion : Nat),
    ∃ side : TensorPremiseSide,
    RulePrefixAt before after vertex rawAge ∧
    certificate.links[linkIndex]? =
      some (Link.par storedLeft storedRight conclusion) ∧
    vertex = side.premise storedLeft storedRight ∧
    before.core.marks[
      side.mate storedLeft storedRight]? = some none

/-- Independent direct waiting-payload prepend relation.  Its equations expose
the initialized pre-cell and the exact O(1) cons update without referring to
the executable `Option` primitive. -/
def WaitingPrependAt (before after : ReservationState)
    (boundary : RawTokenAge) (conclusion : Vertex) : Prop :=
  ∃ payload,
    before.stack.waiting[boundary]? =
      some (.initialized payload) ∧
    after.stack = {
      before.stack with
      waiting :=
        before.stack.waiting.setIfInBounds boundary
          (.initialized (conclusion :: payload)) } ∧
    after.core = before.core ∧
    after.tags = before.tags

/-- Independent Boolean-free local Figure-7 `wait` relation.

The paper guard compares the mate's raw mark with the selected raw age.  Its
destination is the exact `sigmaBoundary?` result; neither a union-find
representative nor the raw age itself is used as the waiting-table index. -/
def WaitRule (certificate : Certificate)
    (before after : ReservationState) : Prop :=
  ∃ (vertex rawAge linkIndex storedLeft storedRight conclusion : Nat),
    ∃ (side : TensorPremiseSide) (middle : ReservationState)
      (mateRawAge boundary : RawTokenAge),
    RulePrefixAt before middle vertex rawAge ∧
    certificate.links[linkIndex]? =
      some (Link.par storedLeft storedRight conclusion) ∧
    vertex = side.premise storedLeft storedRight ∧
    before.core.marks[
      side.mate storedLeft storedRight]? =
        some (some mateRawAge) ∧
    mateRawAge < rawAge ∧
    sigmaBoundary? middle.stack.sigma mateRawAge =
      some boundary ∧
    WaitingPrependAt middle after boundary conclusion

/-- Execute Figure-7 `concl`: perform the common prefix only when the selected
occurrence is a locally ownership-well-formed declared conclusion with an
exactly empty consumer bucket. -/
def concl? (certificate : Certificate)
    (before : ReservationState)
    (_invariant : ReservationInvariant certificate before) :
    Option ReservationState :=
  match prepare? before with
  | none => none
  | some prepared =>
      match
          certificate.conclusionBelow?
            prepared.stackResult.vertex with
      | none => none
      | some _boundary => some prepared.after

/-- Exact proof-relevant specification of one successful `concl` rule. -/
structure ConclStep (certificate : Certificate)
    (before after : ReservationState) : Type where
  before_invariant : ReservationInvariant certificate before
  prepared : PreparedStep before
  boundary :
    ConclusionBelow certificate prepared.stackResult.vertex
  prepare_eq : prepare? before = some prepared
  boundary_eq :
    certificate.conclusionBelow? prepared.stackResult.vertex =
      some boundary
  output_eq : after = prepared.after

/-- Executable `concl` success is exactly the typed rule witness. -/
theorem concl?_some_iff
    {certificate : Certificate}
    {before after : ReservationState}
    (invariant : ReservationInvariant certificate before) :
    concl? certificate before invariant = some after ↔
      Nonempty (ConclStep certificate before after) := by
  constructor
  · intro equation
    unfold concl? at equation
    cases prepareEquation : prepare? before with
    | none =>
        simp [prepareEquation] at equation
    | some prepared =>
        cases boundaryEquation :
            certificate.conclusionBelow?
              prepared.stackResult.vertex with
        | none =>
            simp [prepareEquation, boundaryEquation] at equation
        | some boundary =>
            simp [prepareEquation, boundaryEquation] at equation
            subst after
            exact ⟨{
              before_invariant := invariant
              prepared
              boundary
              prepare_eq := prepareEquation
              boundary_eq := boundaryEquation
              output_eq := rfl }⟩
  · rintro ⟨step⟩
    rcases step with
      ⟨stepInvariant, prepared, boundary, prepareEquation,
        boundaryEquation, outputEquation⟩
    subst after
    simp [concl?, prepareEquation, boundaryEquation]

namespace ConclStep

/-- A successful `concl` rule changes only the synchronized common prefix. -/
theorem reservationInvariant
    {certificate : Certificate}
    {before after : ReservationState}
    (step : ConclStep certificate before after) :
    ReservationInvariant certificate after := by
  rw [step.output_eq]
  exact step.prepared.reservationInvariant step.before_invariant

end ConclStep

/-- Success of executable `concl` preserves the current reservation
invariant. -/
theorem concl?_reservationInvariant
    {certificate : Certificate}
    {before after : ReservationState}
    (invariant : ReservationInvariant certificate before)
    (equation : concl? certificate before invariant = some after) :
    ReservationInvariant certificate after := by
  rcases (concl?_some_iff invariant).mp equation with ⟨step⟩
  exact step.reservationInvariant

/-- The equation-backed executable witness refines the independent direct
`concl` relation. -/
theorem ConclStep.toRule
    {certificate : Certificate}
    {before after : ReservationState}
    (step : ConclStep certificate before after) :
    ConclRule certificate before after := by
  rw [step.output_eq]
  exact ⟨step.prepared.stackResult.vertex,
    step.prepared.stackResult.rawAge,
    RulePrefix.ofPrepared step.prepared, step.boundary.boundary⟩

/-- Executable `concl` is sound for the independent direct relation without
assuming global certificate validity. -/
theorem concl?_sound
    {certificate : Certificate}
    {before after : ReservationState}
    (invariant : ReservationInvariant certificate before)
    (equation : concl? certificate before invariant = some after) :
    ConclRule certificate before after := by
  rcases (concl?_some_iff invariant).mp equation with ⟨step⟩
  exact step.toRule

private theorem consumerBucket_eq_nil_of_structural_boundary
    {certificate : Certificate} {vertex : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (boundary : vertex ∈ certificate.conclusions) :
    certificate.consumerIndex.bucket vertex = [] := by
  have vertexBound : vertex < certificate.formulas.size :=
    structural.2.2.1 vertex boundary
  have node := structural.2.2.2.2.2 vertex vertexBound
  have parentCount :
      certificate.parentUseCount vertex = 0 := by
    simpa [boundary] using node.2
  cases bucketEquation :
      certificate.consumerIndex.bucket vertex with
  | nil => rfl
  | cons linkIndex rest =>
      have bucketMembership :
          linkIndex ∈ certificate.consumerIndex.bucket vertex := by
        rw [bucketEquation]
        simp
      rcases ConsumerIndex.build_origin bucketMembership with
        ⟨link, linkEquation, _connective, premiseMembership⟩
      have linkBound : linkIndex < certificate.links.length :=
        (List.getElem?_eq_some_iff.mp linkEquation).1
      have linkMembership : link ∈ certificate.links := by
        have stored :=
          List.getElem_mem (l := certificate.links) linkBound
        simpa [(List.getElem?_eq_some_iff.mp linkEquation).2] using
          stored
      have uses : link.usesAsPremise vertex = true := by
        simp [Link.usesAsPremise, premiseMembership]
      have filtered :
          link ∈
            certificate.links.filter (·.usesAsPremise vertex) :=
        List.mem_filter.mpr ⟨linkMembership, uses⟩
      have positive : 0 < certificate.parentUseCount vertex := by
        unfold Certificate.parentUseCount
        exact List.length_pos_of_mem filtered
      rw [parentCount] at positive
      exact (Nat.not_lt_zero 0 positive).elim

private theorem exists_conclusionBelow?_eq_some_of_structural
    {certificate : Certificate} {vertex : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (boundary : vertex ∈ certificate.conclusions) :
    ∃ view : ConclusionBelow certificate vertex,
      certificate.conclusionBelow? vertex = some view := by
  have vertexBound : vertex < certificate.formulas.size :=
    structural.2.2.1 vertex boundary
  have node :=
    structural.2.2.2.2.2 vertex vertexBound
  have noConsumer :=
    consumerBucket_eq_nil_of_structural_boundary structural boundary
  let view : ConclusionBelow certificate vertex := {
    boundary
    nodeWellFormed := node
    noConsumer }
  refine ⟨view, ?_⟩
  unfold Certificate.conclusionBelow?
  simp [boundary,
    (certificate.nodeWellFormed_iff vertex).mpr node,
    noConsumer, view]

/-- On structurally valid input, the independent direct `concl` guard is
complete for the executable rule. -/
theorem concl?_complete_of_structural
    {certificate : Certificate}
    {before after : ReservationState}
    (structural : certificate.StructurallyWellFormed)
    (invariant : ReservationInvariant certificate before)
    (rule : ConclRule certificate before after) :
    concl? certificate before invariant = some after := by
  rcases rule with
    ⟨vertex, rawAge, prefixRule, boundary⟩
  rcases prefixRule with
    ⟨readyPrefix, readyTail, sigmaPrefix, readyEquation,
      sigmaEquation, stackUnmarked, coreUnmarked,
      stackAfter, coreAfter, tagsAfter⟩
  let stackResult : PopReadyMarkResult := {
    vertex
    rawAge
    remainingTop := readyTail
    after := after.stack }
  have stackEquation :
      before.stack.popReadyMark? = .ok stackResult := by
    apply SequentialStackState.popReadyMark?_ok_iff.mpr
    exact ⟨{
      top_eq := by
        dsimp [stackResult]
        rw [readyEquation]
        simp
      sigma_top_eq := by
        dsimp [stackResult]
        rw [sigmaEquation]
        simp
      unmarked := stackUnmarked
      after_eq := by
        dsimp [stackResult]
        rw [stackAfter, readyEquation]
        simp }⟩
  have coreEquation :
      before.core.markReadyRaw? vertex rawAge =
        .ok after.core := by
    apply UnificationState.markReadyRaw?_ok_iff.mpr
    exact ⟨{
      unmarked := coreUnmarked
      after_eq := coreAfter }⟩
  rcases
      exists_prepare?_eq_some_of_ok
        stackEquation coreEquation with
    ⟨prepared, prepareEquation⟩
  have preparedPrefix :
      RulePrefix before prepared.after :=
    ⟨prepared.stackResult.vertex,
      prepared.stackResult.rawAge,
      RulePrefix.ofPrepared prepared⟩
  have directPrefix : RulePrefix before after :=
    ⟨vertex, rawAge,
      ⟨readyPrefix, readyTail, sigmaPrefix, readyEquation,
        sigmaEquation, stackUnmarked, coreUnmarked,
        stackAfter, coreAfter, tagsAfter⟩⟩
  have outputEquation : after = prepared.after :=
    RulePrefix.output_unique directPrefix preparedPrefix
  have preparedTop :
      before.stack.ready.getLast? =
        some (prepared.stackResult.vertex ::
          prepared.stackResult.remainingTop) :=
    (SequentialStackState.popReadyMark?_exact
      prepared.stack_eq).1
  have directTop :
      before.stack.ready.getLast? =
        some (vertex :: readyTail) := by
    rw [readyEquation]
    simp
  have vertexEquation :
      prepared.stackResult.vertex = vertex := by
    have same :
        prepared.stackResult.vertex ::
            prepared.stackResult.remainingTop =
          vertex :: readyTail :=
      Option.some.inj (preparedTop.symm.trans directTop)
    exact List.cons.inj same |>.1
  have preparedBoundaryMembership :
      prepared.stackResult.vertex ∈ certificate.conclusions := by
    simpa [vertexEquation] using boundary
  rcases
      exists_conclusionBelow?_eq_some_of_structural
        structural preparedBoundaryMembership with
    ⟨preparedBoundary, preparedBoundaryEquation⟩
  apply (concl?_some_iff invariant).mpr
  exact ⟨{
    before_invariant := invariant
    prepared
    boundary := preparedBoundary
    prepare_eq := prepareEquation
    boundary_eq := preparedBoundaryEquation
    output_eq := outputEquation }⟩

/-- Exact executable/declarative correspondence for `concl` under the
certificate validity needed to make the paper guard unambiguous. -/
theorem concl?_some_iff_rule_of_structural
    {certificate : Certificate}
    {before after : ReservationState}
    (structural : certificate.StructurallyWellFormed)
    (invariant : ReservationInvariant certificate before) :
    concl? certificate before invariant = some after ↔
      ConclRule certificate before after :=
  ⟨concl?_sound invariant,
    concl?_complete_of_structural structural invariant⟩

/-- The independent `concl` relation has a unique output. -/
theorem ConclRule.output_unique
    {certificate : Certificate}
    {before first second : ReservationState}
    (left : ConclRule certificate before first)
    (right : ConclRule certificate before second) :
    first = second := by
  apply RulePrefix.output_unique
  · rcases left with ⟨vertex, rawAge, prefixRule, _⟩
    exact ⟨vertex, rawAge, prefixRule⟩
  · rcases right with ⟨vertex, rawAge, prefixRule, _⟩
    exact ⟨vertex, rawAge, prefixRule⟩

/-- Execute Figure-7 `nop`: perform the common prefix only when the selected
occurrence has one exact par consumer and the opposite par premise remains raw
unmarked in the post-prefix production state. -/
def nop? (certificate : Certificate)
    (before : ReservationState)
    (_invariant : ReservationInvariant certificate before) :
    Option ReservationState :=
  match prepare? before with
  | none => none
  | some prepared =>
      match
          certificate.connectiveBelow?
            prepared.stackResult.vertex with
      | none => none
      | some consumer =>
          if _par : consumer.kind = .par then
            if _mateUnmarked :
                prepared.coreMarked.marks[consumer.mate]? =
                  some none then
              some prepared.after
            else
              none
          else
            none

/-- Exact proof-relevant specification of one successful `nop` rule. -/
structure NopStep (certificate : Certificate)
    (before after : ReservationState) : Type where
  before_invariant : ReservationInvariant certificate before
  prepared : PreparedStep before
  consumer :
    ConnectiveBelow certificate prepared.stackResult.vertex
  prepare_eq : prepare? before = some prepared
  consumer_eq :
    certificate.connectiveBelow? prepared.stackResult.vertex =
      some consumer
  par_eq : consumer.kind = .par
  mate_unmarked :
    prepared.coreMarked.marks[consumer.mate]? = some none
  output_eq : after = prepared.after

/-- Executable `nop` success is exactly the typed rule witness. -/
theorem nop?_some_iff
    {certificate : Certificate}
    {before after : ReservationState}
    (invariant : ReservationInvariant certificate before) :
    nop? certificate before invariant = some after ↔
      Nonempty (NopStep certificate before after) := by
  constructor
  · intro equation
    unfold nop? at equation
    cases prepareEquation : prepare? before with
    | none =>
        simp [prepareEquation] at equation
    | some prepared =>
        cases consumerEquation :
            certificate.connectiveBelow?
              prepared.stackResult.vertex with
        | none =>
            simp [prepareEquation, consumerEquation] at equation
        | some consumer =>
            by_cases parEquation : consumer.kind = .par
            · by_cases mateEquation :
                  prepared.coreMarked.marks[consumer.mate]? =
                    some none
              · simp [prepareEquation, consumerEquation, parEquation,
                  mateEquation] at equation
                subst after
                exact ⟨{
                  before_invariant := invariant
                  prepared
                  consumer
                  prepare_eq := prepareEquation
                  consumer_eq := consumerEquation
                  par_eq := parEquation
                  mate_unmarked := mateEquation
                  output_eq := rfl }⟩
              · simp [prepareEquation, consumerEquation, parEquation,
                  mateEquation] at equation
            · simp [prepareEquation, consumerEquation, parEquation]
                at equation
  · rintro ⟨step⟩
    rcases step with
      ⟨stepInvariant, prepared, consumer, prepareEquation,
        consumerEquation, parEquation, mateEquation,
        outputEquation⟩
    subst after
    simp [nop?, prepareEquation, consumerEquation, parEquation,
      mateEquation]

namespace NopStep

/-- The generic consumer retained by a `nop` witness is the exact submitted
par link. -/
theorem submitted_par
    {certificate : Certificate}
    {before after : ReservationState}
    (step : NopStep certificate before after) :
    certificate.links[step.consumer.linkIndex]? =
      some (.par step.consumer.storedLeft
        step.consumer.storedRight step.consumer.conclusion) := by
  simpa [step.par_eq, SequentialConnectiveKind.asLink] using
    step.consumer.link_eq

/-- The paper's `nop` guard holds already in the pre-prefix raw marking.

The executable rule tests the post-prefix state, but the prefix changes only
the selected premise.  Local link well-formedness makes its mate distinct, so
the test is exactly Guerrini's pre-state `μ(u₂) = ⊥` guard. -/
theorem mate_unmarked_before
    {certificate : Certificate}
    {before after : ReservationState}
    (step : NopStep certificate before after) :
    before.core.marks[step.consumer.mate]? = some none := by
  have markExact :=
    UnificationState.markReadyRaw?_exact
      step.prepared.core_mark_eq
  have selectedNeMate :
      step.prepared.stackResult.vertex ≠
        step.consumer.mate :=
    (step.consumer.mate_ne).symm
  have unchanged :
      step.prepared.coreMarked.marks[step.consumer.mate]? =
        before.core.marks[step.consumer.mate]? := by
    rw [markExact.2.1]
    simp [selectedNeMate]
  exact unchanged.symm.trans step.mate_unmarked

/-- A successful `nop` rule changes only the synchronized common prefix. -/
theorem reservationInvariant
    {certificate : Certificate}
    {before after : ReservationState}
    (step : NopStep certificate before after) :
    ReservationInvariant certificate after := by
  rw [step.output_eq]
  exact step.prepared.reservationInvariant step.before_invariant

end NopStep

/-- Success of executable `nop` preserves the current reservation invariant. -/
theorem nop?_reservationInvariant
    {certificate : Certificate}
    {before after : ReservationState}
    (invariant : ReservationInvariant certificate before)
    (equation : nop? certificate before invariant = some after) :
    ReservationInvariant certificate after := by
  rcases (nop?_some_iff invariant).mp equation with ⟨step⟩
  exact step.reservationInvariant

/-- The equation-backed executable witness refines the independent direct
`nop` relation. -/
theorem NopStep.toRule
    {certificate : Certificate}
    {before after : ReservationState}
    (step : NopStep certificate before after) :
    NopRule certificate before after := by
  rw [step.output_eq]
  exact ⟨step.prepared.stackResult.vertex,
    step.prepared.stackResult.rawAge,
    step.consumer.linkIndex,
    step.consumer.storedLeft,
    step.consumer.storedRight,
    step.consumer.conclusion,
    step.consumer.side,
    RulePrefix.ofPrepared step.prepared,
    step.submitted_par,
    step.consumer.premise_eq,
    step.mate_unmarked_before⟩

/-- Executable `nop` is sound for the independent direct relation without
assuming global certificate validity. -/
theorem nop?_sound
    {certificate : Certificate}
    {before after : ReservationState}
    (invariant : ReservationInvariant certificate before)
    (equation : nop? certificate before invariant = some after) :
    NopRule certificate before after := by
  rcases (nop?_some_iff invariant).mp equation with ⟨step⟩
  exact step.toRule

private theorem exists_connectiveBelow?_eq_some_par_of_structural
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {vertex linkIndex storedLeft storedRight conclusion : Vertex}
    {side : TensorPremiseSide}
    (linkEquation :
      certificate.links[linkIndex]? =
        some (.par storedLeft storedRight conclusion))
    (premiseEquation :
      vertex = side.premise storedLeft storedRight) :
    ∃ consumer : ConnectiveBelow certificate vertex,
      certificate.connectiveBelow? vertex = some consumer ∧
      consumer.kind = .par ∧
      consumer.side = side ∧
      consumer.conclusion = conclusion ∧
      consumer.mate =
        side.mate storedLeft storedRight := by
  have linkBound : linkIndex < certificate.links.length :=
    (List.getElem?_eq_some_iff.mp linkEquation).1
  have linkMembership :
      .par storedLeft storedRight conclusion ∈ certificate.links := by
    have stored := List.getElem_mem (l := certificate.links) linkBound
    simpa [(List.getElem?_eq_some_iff.mp linkEquation).2] using stored
  have wellFormed :
      certificate.LinkWellFormed
        (.par storedLeft storedRight conclusion) :=
    structural.2.2.2.2.1 _ linkMembership
  cases side with
  | storedLeft =>
      simp [TensorPremiseSide.premise] at premiseEquation
      subst vertex
      have unique :
          certificate.consumerIndex.uniqueConsumer? storedLeft =
            some linkIndex := by
        apply ConsumerIndex.build_uniqueConsumer?_eq_some
          structural linkEquation
        · exact wellFormed.2.2.2.1
        · simp [Link.premises]
      let consumer : ConnectiveBelow certificate storedLeft := {
        linkIndex
        kind := .par
        storedLeft
        storedRight
        conclusion
        side := .storedLeft
        consumer_eq := unique
        link_eq := by
          simpa [SequentialConnectiveKind.asLink] using linkEquation
        wellFormed
        premise_eq := rfl }
      refine ⟨consumer, ?_, rfl, rfl, rfl, rfl⟩
      unfold Certificate.connectiveBelow?
      split
      next noConsumer =>
        rw [unique] at noConsumer
        simp at noConsumer
      next actualIndex consumerLookup =>
        have indexEquation : actualIndex = linkIndex :=
          Option.some.inj (consumerLookup.symm.trans unique)
        subst actualIndex
        unfold connectiveBelowAt?
        split
        next left right target submitted =>
          have same :
              Link.par left right target =
                .par storedLeft storedRight conclusion :=
            Option.some.inj (submitted.symm.trans linkEquation)
          cases same
          simp [(certificate.linkLocallyWellFormed_iff
            (.par storedLeft storedRight conclusion)).mpr
              wellFormed,
            consumer]
        next left right target submitted =>
          have impossible :
              Link.tensor left right target =
                .par storedLeft storedRight conclusion :=
            Option.some.inj (submitted.symm.trans linkEquation)
          cases impossible
        next noPar noTensor =>
          exact
            (noPar storedLeft storedRight conclusion
              linkEquation).elim
  | storedRight =>
      simp [TensorPremiseSide.premise] at premiseEquation
      subst vertex
      have unique :
          certificate.consumerIndex.uniqueConsumer? storedRight =
            some linkIndex := by
        apply ConsumerIndex.build_uniqueConsumer?_eq_some
          structural linkEquation
        · exact wellFormed.2.2.2.2.1
        · simp [Link.premises]
      let consumer : ConnectiveBelow certificate storedRight := {
        linkIndex
        kind := .par
        storedLeft
        storedRight
        conclusion
        side := .storedRight
        consumer_eq := unique
        link_eq := by
          simpa [SequentialConnectiveKind.asLink] using linkEquation
        wellFormed
        premise_eq := rfl }
      refine ⟨consumer, ?_, rfl, rfl, rfl, rfl⟩
      unfold Certificate.connectiveBelow?
      split
      next noConsumer =>
        rw [unique] at noConsumer
        simp at noConsumer
      next actualIndex consumerLookup =>
        have indexEquation : actualIndex = linkIndex :=
          Option.some.inj (consumerLookup.symm.trans unique)
        subst actualIndex
        unfold connectiveBelowAt?
        split
        next left right target submitted =>
          have same :
              Link.par left right target =
                .par storedLeft storedRight conclusion :=
            Option.some.inj (submitted.symm.trans linkEquation)
          cases same
          have rightNeLeft : storedRight ≠ storedLeft :=
            wellFormed.1.symm
          simp [(certificate.linkLocallyWellFormed_iff
            (.par storedLeft storedRight conclusion)).mpr
              wellFormed,
            rightNeLeft, consumer]
        next left right target submitted =>
          have impossible :
              Link.tensor left right target =
                .par storedLeft storedRight conclusion :=
            Option.some.inj (submitted.symm.trans linkEquation)
          cases impossible
        next noPar noTensor =>
          exact
            (noPar storedLeft storedRight conclusion
              linkEquation).elim

/-- On structurally valid input, the independent direct `nop` guard is
complete for the executable rule. -/
theorem nop?_complete_of_structural
    {certificate : Certificate}
    {before after : ReservationState}
    (structural : certificate.StructurallyWellFormed)
    (invariant : ReservationInvariant certificate before)
    (rule : NopRule certificate before after) :
    nop? certificate before invariant = some after := by
  rcases rule with
    ⟨vertex, rawAge, linkIndex, storedLeft, storedRight,
      conclusion, side, prefixRule, linkEquation,
      premiseEquation, mateUnmarked⟩
  rcases prefixRule with
    ⟨readyPrefix, readyTail, sigmaPrefix, readyEquation,
      sigmaEquation, stackUnmarked, coreUnmarked,
      stackAfter, coreAfter, tagsAfter⟩
  let stackResult : PopReadyMarkResult := {
    vertex
    rawAge
    remainingTop := readyTail
    after := after.stack }
  have stackEquation :
      before.stack.popReadyMark? = .ok stackResult := by
    apply SequentialStackState.popReadyMark?_ok_iff.mpr
    exact ⟨{
      top_eq := by
        dsimp [stackResult]
        rw [readyEquation]
        simp
      sigma_top_eq := by
        dsimp [stackResult]
        rw [sigmaEquation]
        simp
      unmarked := stackUnmarked
      after_eq := by
        dsimp [stackResult]
        rw [stackAfter, readyEquation]
        simp }⟩
  have coreEquation :
      before.core.markReadyRaw? vertex rawAge =
        .ok after.core := by
    apply UnificationState.markReadyRaw?_ok_iff.mpr
    exact ⟨{
      unmarked := coreUnmarked
      after_eq := coreAfter }⟩
  rcases
      exists_prepare?_eq_some_of_ok
        stackEquation coreEquation with
    ⟨prepared, prepareEquation⟩
  have preparedPrefix :
      RulePrefix before prepared.after :=
    ⟨prepared.stackResult.vertex,
      prepared.stackResult.rawAge,
      RulePrefix.ofPrepared prepared⟩
  have directPrefix : RulePrefix before after :=
    ⟨vertex, rawAge,
      ⟨readyPrefix, readyTail, sigmaPrefix, readyEquation,
        sigmaEquation, stackUnmarked, coreUnmarked,
        stackAfter, coreAfter, tagsAfter⟩⟩
  have outputEquation : after = prepared.after :=
    RulePrefix.output_unique directPrefix preparedPrefix
  have preparedTop :
      before.stack.ready.getLast? =
        some (prepared.stackResult.vertex ::
          prepared.stackResult.remainingTop) :=
    (SequentialStackState.popReadyMark?_exact
      prepared.stack_eq).1
  have directTop :
      before.stack.ready.getLast? =
        some (vertex :: readyTail) := by
    rw [readyEquation]
    simp
  have vertexEquation :
      prepared.stackResult.vertex = vertex := by
    have same :
        prepared.stackResult.vertex ::
            prepared.stackResult.remainingTop =
          vertex :: readyTail :=
      Option.some.inj (preparedTop.symm.trans directTop)
    exact List.cons.inj same |>.1
  have preparedPremise :
      prepared.stackResult.vertex =
        side.premise storedLeft storedRight :=
    vertexEquation.trans premiseEquation
  rcases
      exists_connectiveBelow?_eq_some_par_of_structural
        structural linkEquation preparedPremise with
    ⟨consumer, consumerEquation, parEquation,
      sideEquation, _conclusionEquation, mateEquation⟩
  have mateUnmarkedBefore :
      before.core.marks[consumer.mate]? = some none := by
    rw [mateEquation]
    exact mateUnmarked
  have markExact :=
    UnificationState.markReadyRaw?_exact
      prepared.core_mark_eq
  have selectedNeMate :
      prepared.stackResult.vertex ≠ consumer.mate :=
    consumer.mate_ne.symm
  have mateUnmarkedAfter :
      prepared.coreMarked.marks[consumer.mate]? =
        some none := by
    rw [markExact.2.1]
    simpa [selectedNeMate] using mateUnmarkedBefore
  apply (nop?_some_iff invariant).mpr
  exact ⟨{
    before_invariant := invariant
    prepared
    consumer
    prepare_eq := prepareEquation
    consumer_eq := consumerEquation
    par_eq := parEquation
    mate_unmarked := mateUnmarkedAfter
    output_eq := outputEquation }⟩

/-- Exact executable/declarative correspondence for `nop` under the
certificate validity needed to make the paper guard unambiguous. -/
theorem nop?_some_iff_rule_of_structural
    {certificate : Certificate}
    {before after : ReservationState}
    (structural : certificate.StructurallyWellFormed)
    (invariant : ReservationInvariant certificate before) :
    nop? certificate before invariant = some after ↔
      NopRule certificate before after :=
  ⟨nop?_sound invariant,
    nop?_complete_of_structural structural invariant⟩

/-- The independent `nop` relation has a unique output. -/
theorem NopRule.output_unique
    {certificate : Certificate}
    {before first second : ReservationState}
    (left : NopRule certificate before first)
    (right : NopRule certificate before second) :
    first = second := by
  apply RulePrefix.output_unique
  · rcases left with
      ⟨vertex, rawAge, _, _, _, _, _, prefixRule, _⟩
    exact ⟨vertex, rawAge, prefixRule⟩
  · rcases right with
      ⟨vertex, rawAge, _, _, _, _, _, prefixRule, _⟩
    exact ⟨vertex, rawAge, prefixRule⟩

/-- Execute Figure-7 `wait` after the synchronized common prefix.

The mate lookup returns its stored raw age.  The strict guard compares that
raw age with the selected occurrence's raw age, then the bridge computes the
destination from `sigmaBoundary?` and prepends the connective conclusion to
the initialized boundary bucket.  There is intentionally no global
`queuedVertices` scan in this local rule. -/
def wait? (certificate : Certificate)
    (before : ReservationState)
    (_invariant : ReservationInvariant certificate before) :
    Option ReservationState :=
  match prepare? before with
  | none => none
  | some prepared =>
      match
          certificate.connectiveBelow?
            prepared.stackResult.vertex with
      | none => none
      | some consumer =>
          if _par : consumer.kind = .par then
            match
                prepared.coreMarked.marks[consumer.mate]? with
            | some (some mateRawAge) =>
                if _younger :
                    mateRawAge < prepared.stackResult.rawAge then
                  enqueueWaitingAtRawAge? prepared.after mateRawAge
                    consumer.conclusion
                else
                  none
            | _ => none
          else
            none

/-- Exact proof-relevant specification of one successful `wait` rule. -/
structure WaitStep (certificate : Certificate)
    (before after : ReservationState) : Type where
  before_invariant : ReservationInvariant certificate before
  prepared : PreparedStep before
  consumer :
    ConnectiveBelow certificate prepared.stackResult.vertex
  mateRawAge : RawTokenAge
  destination :
    WaitDestinationStep prepared.after after
      mateRawAge consumer.conclusion
  prepare_eq : prepare? before = some prepared
  consumer_eq :
    certificate.connectiveBelow? prepared.stackResult.vertex =
      some consumer
  par_eq : consumer.kind = .par
  mate_marked :
    prepared.coreMarked.marks[consumer.mate]? =
      some (some mateRawAge)
  younger : mateRawAge < prepared.stackResult.rawAge
  destination_eq :
    enqueueWaitingAtRawAge? prepared.after mateRawAge
        consumer.conclusion =
      some after

/-- Executable `wait` success is exactly the typed rule witness. -/
theorem wait?_some_iff
    {certificate : Certificate}
    {before after : ReservationState}
    (invariant : ReservationInvariant certificate before) :
    wait? certificate before invariant = some after ↔
      Nonempty (WaitStep certificate before after) := by
  constructor
  · intro equation
    unfold wait? at equation
    cases prepareEquation : prepare? before with
    | none =>
        simp [prepareEquation] at equation
    | some prepared =>
        cases consumerEquation :
            certificate.connectiveBelow?
              prepared.stackResult.vertex with
        | none =>
            simp [prepareEquation, consumerEquation] at equation
        | some consumer =>
            by_cases parEquation : consumer.kind = .par
            · cases mateEquation :
                  prepared.coreMarked.marks[consumer.mate]? with
              | none =>
                  simp [prepareEquation, consumerEquation,
                    parEquation, mateEquation] at equation
              | some mark =>
                  cases mark with
                  | none =>
                      simp [prepareEquation, consumerEquation,
                        parEquation, mateEquation] at equation
                  | some mateRawAge =>
                      by_cases youngerEquation :
                          mateRawAge <
                            prepared.stackResult.rawAge
                      · simp [prepareEquation, consumerEquation,
                          parEquation, mateEquation,
                          youngerEquation] at equation
                        rcases
                            enqueueWaitingAtRawAge?_some_iff.mp
                              equation with
                          ⟨destination⟩
                        exact ⟨{
                          before_invariant := invariant
                          prepared
                          consumer
                          mateRawAge
                          destination
                          prepare_eq := prepareEquation
                          consumer_eq := consumerEquation
                          par_eq := parEquation
                          mate_marked := mateEquation
                          younger := youngerEquation
                          destination_eq := equation }⟩
                      · simp [prepareEquation, consumerEquation,
                          parEquation, mateEquation,
                          youngerEquation] at equation
            · simp [prepareEquation, consumerEquation,
                parEquation] at equation
  · rintro ⟨step⟩
    rcases step with
      ⟨stepInvariant, prepared, consumer, mateRawAge,
        destination, prepareEquation, consumerEquation,
        parEquation, mateEquation, youngerEquation,
        destinationEquation⟩
    simp [wait?, prepareEquation, consumerEquation, parEquation,
      mateEquation, youngerEquation, destinationEquation]

namespace WaitStep

/-- The generic consumer retained by a `wait` witness is the exact submitted
par link. -/
theorem submitted_par
    {certificate : Certificate}
    {before after : ReservationState}
    (step : WaitStep certificate before after) :
    certificate.links[step.consumer.linkIndex]? =
      some (.par step.consumer.storedLeft
        step.consumer.storedRight step.consumer.conclusion) := by
  simpa [step.par_eq, SequentialConnectiveKind.asLink] using
    step.consumer.link_eq

/-- The mate raw age tested after the common prefix is exactly its pre-prefix
paper mark. -/
theorem mate_marked_before
    {certificate : Certificate}
    {before after : ReservationState}
    (step : WaitStep certificate before after) :
    before.core.marks[step.consumer.mate]? =
      some (some step.mateRawAge) := by
  have markExact :=
    UnificationState.markReadyRaw?_exact
      step.prepared.core_mark_eq
  have selectedNeMate :
      step.prepared.stackResult.vertex ≠
        step.consumer.mate :=
    step.consumer.mate_ne.symm
  have unchanged :
      step.prepared.coreMarked.marks[step.consumer.mate]? =
        before.core.marks[step.consumer.mate]? := by
    rw [markExact.2.1]
    simp [selectedNeMate]
  exact unchanged.symm.trans step.mate_marked

/-- A successful `wait` preserves the reservation invariant by composing the
common-prefix and typed destination preservation theorems. -/
theorem reservationInvariant
    {certificate : Certificate}
    {before after : ReservationState}
    (step : WaitStep certificate before after) :
    ReservationInvariant certificate after :=
  step.destination.reservationInvariant
    (step.prepared.reservationInvariant step.before_invariant)

end WaitStep

/-- Executable `wait` preserves the complete reservation invariant. -/
theorem wait?_reservationInvariant
    {certificate : Certificate}
    {before after : ReservationState}
    (invariant : ReservationInvariant certificate before)
    (equation : wait? certificate before invariant = some after) :
    ReservationInvariant certificate after := by
  rcases (wait?_some_iff invariant).mp equation with ⟨step⟩
  exact step.reservationInvariant

/-- A typed bridge destination refines the independent direct cons-update
relation. -/
theorem WaitDestinationStep.toWaitingPrependAt
    {before after : ReservationState}
    {mateRawAge : RawTokenAge} {conclusion : Vertex}
    (step :
      WaitDestinationStep before after mateRawAge conclusion) :
    WaitingPrependAt before after step.boundary conclusion := by
  rcases step with
    ⟨boundary, stackAfter, boundaryEquation, stackEquation, rfl⟩
  rcases
      SequentialStackState.prependWaiting?_some_iff.mp
        stackEquation with
    ⟨prepend⟩
  rcases prepend with ⟨payload, initialized, rfl⟩
  exact ⟨payload, initialized, rfl, rfl, rfl⟩

/-- The equation-backed executable witness refines the independent direct
`wait` relation. -/
theorem WaitStep.toRule
    {certificate : Certificate}
    {before after : ReservationState}
    (step : WaitStep certificate before after) :
    WaitRule certificate before after := by
  exact ⟨step.prepared.stackResult.vertex,
    step.prepared.stackResult.rawAge,
    step.consumer.linkIndex,
    step.consumer.storedLeft,
    step.consumer.storedRight,
    step.consumer.conclusion,
    step.consumer.side,
    step.prepared.after,
    step.mateRawAge,
    step.destination.boundary,
    RulePrefix.ofPrepared step.prepared,
    step.submitted_par,
    step.consumer.premise_eq,
    step.mate_marked_before,
    step.younger,
    step.destination.boundary_eq,
    WaitDestinationStep.toWaitingPrependAt step.destination⟩

/-- Executable `wait` is sound for the independent direct relation without a
global certificate-validity assumption. -/
theorem wait?_sound
    {certificate : Certificate}
    {before after : ReservationState}
    (invariant : ReservationInvariant certificate before)
    (equation : wait? certificate before invariant = some after) :
    WaitRule certificate before after := by
  rcases (wait?_some_iff invariant).mp equation with ⟨step⟩
  exact step.toRule

/-- A direct initialized-cell cons update is complete for the executable
raw-boundary bridge. -/
theorem WaitingPrependAt.toExecutable
    {before after : ReservationState}
    {mateRawAge boundary : RawTokenAge} {conclusion : Vertex}
    (boundaryEquation :
      sigmaBoundary? before.stack.sigma mateRawAge =
        some boundary)
    (rule :
      WaitingPrependAt before after boundary conclusion) :
    enqueueWaitingAtRawAge? before mateRawAge conclusion =
      some after := by
  rcases rule with
    ⟨payload, initialized, stackEquation, coreEquation, tagsEquation⟩
  have stackStep :
      before.stack.prependWaiting? boundary conclusion =
        some after.stack := by
    apply SequentialStackState.prependWaiting?_some_iff.mpr
    exact ⟨{
      payload
      initialized
      after_eq := stackEquation }⟩
  apply enqueueWaitingAtRawAge?_some_iff.mpr
  exact ⟨{
    boundary
    stackAfter := after.stack
    boundary_eq := boundaryEquation
    stack_eq := stackStep
    output_eq := by
      cases before
      cases after
      simp_all }⟩

private theorem exists_prepared_of_rulePrefixAt
    {before middle : ReservationState}
    {vertex : Vertex} {rawAge : RawTokenAge}
    (rule : RulePrefixAt before middle vertex rawAge) :
    ∃ prepared : PreparedStep before,
      prepare? before = some prepared ∧
      prepared.after = middle ∧
      prepared.stackResult.vertex = vertex ∧
      prepared.stackResult.rawAge = rawAge := by
  rcases rule with
    ⟨readyPrefix, readyTail, sigmaPrefix, readyEquation,
      sigmaEquation, stackUnmarked, coreUnmarked,
      stackAfter, coreAfter, tagsAfter⟩
  let stackResult : PopReadyMarkResult := {
    vertex
    rawAge
    remainingTop := readyTail
    after := middle.stack }
  have stackEquation :
      before.stack.popReadyMark? = .ok stackResult := by
    apply SequentialStackState.popReadyMark?_ok_iff.mpr
    exact ⟨{
      top_eq := by
        dsimp [stackResult]
        rw [readyEquation]
        simp
      sigma_top_eq := by
        dsimp [stackResult]
        rw [sigmaEquation]
        simp
      unmarked := stackUnmarked
      after_eq := by
        dsimp [stackResult]
        rw [stackAfter, readyEquation]
        simp }⟩
  have coreEquation :
      before.core.markReadyRaw? vertex rawAge =
        .ok middle.core := by
    apply UnificationState.markReadyRaw?_ok_iff.mpr
    exact ⟨{
      unmarked := coreUnmarked
      after_eq := coreAfter }⟩
  rcases
      exists_prepare?_eq_some_of_ok stackEquation coreEquation with
    ⟨prepared, prepareEquation⟩
  have preparedPrefix :
      RulePrefix before prepared.after :=
    ⟨prepared.stackResult.vertex,
      prepared.stackResult.rawAge,
      RulePrefix.ofPrepared prepared⟩
  have directPrefix : RulePrefix before middle :=
    ⟨vertex, rawAge,
      ⟨readyPrefix, readyTail, sigmaPrefix, readyEquation,
        sigmaEquation, stackUnmarked, coreUnmarked,
        stackAfter, coreAfter, tagsAfter⟩⟩
  have outputEquation : prepared.after = middle :=
    RulePrefix.output_unique preparedPrefix directPrefix
  have preparedTop :
      before.stack.ready.getLast? =
        some (prepared.stackResult.vertex ::
          prepared.stackResult.remainingTop) :=
    (SequentialStackState.popReadyMark?_exact
      prepared.stack_eq).1
  have directTop :
      before.stack.ready.getLast? = some (vertex :: readyTail) := by
    rw [readyEquation]
    simp
  have vertexEquation :
      prepared.stackResult.vertex = vertex := by
    have same :
        prepared.stackResult.vertex ::
            prepared.stackResult.remainingTop =
          vertex :: readyTail :=
      Option.some.inj (preparedTop.symm.trans directTop)
    exact List.cons.inj same |>.1
  have preparedSigmaTop :
      before.stack.sigma.getLast? =
        some prepared.stackResult.rawAge :=
    (SequentialStackState.popReadyMark?_exact
      prepared.stack_eq).2.1
  have directSigmaTop :
      before.stack.sigma.getLast? = some rawAge := by
    rw [sigmaEquation]
    simp
  have rawAgeEquation :
      prepared.stackResult.rawAge = rawAge :=
    Option.some.inj (preparedSigmaTop.symm.trans directSigmaTop)
  exact ⟨prepared, prepareEquation, outputEquation,
    vertexEquation, rawAgeEquation⟩

/-- On structurally valid input, the independent direct `wait` guard is
complete for the executable local rule. -/
theorem wait?_complete_of_structural
    {certificate : Certificate}
    {before after : ReservationState}
    (structural : certificate.StructurallyWellFormed)
    (invariant : ReservationInvariant certificate before)
    (rule : WaitRule certificate before after) :
    wait? certificate before invariant = some after := by
  rcases rule with
    ⟨vertex, rawAge, linkIndex, storedLeft, storedRight,
      conclusion, side, middle, mateRawAge, boundary,
      prefixRule, linkEquation, premiseEquation,
      mateMarkedBefore, younger, boundaryEquation,
      waitingRule⟩
  rcases exists_prepared_of_rulePrefixAt prefixRule with
    ⟨prepared, prepareEquation, middleEquation,
      vertexEquation, rawAgeEquation⟩
  have preparedPremise :
      prepared.stackResult.vertex =
        side.premise storedLeft storedRight := by
    rw [vertexEquation]
    exact premiseEquation
  rcases
      exists_connectiveBelow?_eq_some_par_of_structural
        structural linkEquation preparedPremise with
    ⟨consumer, consumerEquation, parEquation,
      sideEquation, conclusionEquation, mateEquation⟩
  have mateMarkedBefore' :
      before.core.marks[consumer.mate]? =
        some (some mateRawAge) := by
    rw [mateEquation]
    exact mateMarkedBefore
  have markExact :=
    UnificationState.markReadyRaw?_exact
      prepared.core_mark_eq
  have selectedNeMate :
      prepared.stackResult.vertex ≠ consumer.mate :=
    consumer.mate_ne.symm
  have mateMarkedAfter :
      prepared.coreMarked.marks[consumer.mate]? =
        some (some mateRawAge) := by
    rw [markExact.2.1]
    simpa [selectedNeMate] using mateMarkedBefore'
  have youngerPrepared :
      mateRawAge < prepared.stackResult.rawAge := by
    simpa [rawAgeEquation] using younger
  have boundaryPrepared :
      sigmaBoundary? prepared.after.stack.sigma mateRawAge =
        some boundary := by
    rw [middleEquation]
    exact boundaryEquation
  have waitingPrepared :
      WaitingPrependAt prepared.after after boundary conclusion := by
    rw [middleEquation]
    exact waitingRule
  have destinationEquation :
      enqueueWaitingAtRawAge? prepared.after mateRawAge consumer.conclusion =
        some after :=
    by
      rw [conclusionEquation]
      exact waitingPrepared.toExecutable boundaryPrepared
  rcases
      enqueueWaitingAtRawAge?_some_iff.mp destinationEquation with
    ⟨destination⟩
  apply (wait?_some_iff invariant).mpr
  exact ⟨{
    before_invariant := invariant
    prepared
    consumer
    mateRawAge
    destination
    prepare_eq := prepareEquation
    consumer_eq := consumerEquation
    par_eq := parEquation
    mate_marked := mateMarkedAfter
    younger := youngerPrepared
    destination_eq := destinationEquation }⟩

/-- Exact executable/declarative correspondence for `wait` under the
certificate validity needed to make the par consumer unambiguous. -/
theorem wait?_some_iff_rule_of_structural
    {certificate : Certificate}
    {before after : ReservationState}
    (structural : certificate.StructurallyWellFormed)
    (invariant : ReservationInvariant certificate before) :
    wait? certificate before invariant = some after ↔
      WaitRule certificate before after :=
  ⟨wait?_sound invariant,
    wait?_complete_of_structural structural invariant⟩

/-- Under structural certificate validity and the supplied reservation
invariant, the independent `wait` relation has one exact output. -/
theorem WaitRule.output_unique_of_structural
    {certificate : Certificate}
    {before first second : ReservationState}
    (structural : certificate.StructurallyWellFormed)
    (invariant : ReservationInvariant certificate before)
    (left : WaitRule certificate before first)
    (right : WaitRule certificate before second) :
    first = second := by
  have leftExecutable :=
    wait?_complete_of_structural structural invariant left
  have rightExecutable :=
    wait?_complete_of_structural structural invariant right
  exact Option.some.inj (leftExecutable.symm.trans rightExecutable)

/-- The direct cons-update relation has one exact output. -/
theorem WaitingPrependAt.output_unique
    {before first second : ReservationState}
    {boundary : RawTokenAge} {conclusion : Vertex}
    (left : WaitingPrependAt before first boundary conclusion)
    (right : WaitingPrependAt before second boundary conclusion) :
    first = second := by
  rcases left with
    ⟨leftPayload, leftInitialized, leftStack, leftCore, leftTags⟩
  rcases right with
    ⟨rightPayload, rightInitialized,
      rightStack, rightCore, rightTags⟩
  have payloadEquation : leftPayload = rightPayload := by
    exact WaitingCell.initialized.inj
      (Option.some.inj
        (leftInitialized.symm.trans rightInitialized))
  subst rightPayload
  cases first
  cases second
  simp_all

end SequentialFigure7

end ProofNetIR
