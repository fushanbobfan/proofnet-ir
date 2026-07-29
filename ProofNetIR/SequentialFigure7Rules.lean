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
The first two complete rules built from that prefix are:

* `concl`: the selected occurrence is an explicit conclusion with no consumer;
* `nop`: the selected occurrence is a par premise whose mate is still raw
  unmarked.

Both rules perform only the common prefix.  Waiting transfer, par forwarding,
tensor unification, full-rule reachability, and progress remain separate.
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

end SequentialFigure7

end ProofNetIR
