import ProofNetIR.SequentialFigure7Rules

namespace ProofNetIR

/-!
# Singleton waiting-payload activation and unification

This module extends the bounded Figure-7 rule layer by exactly one nonempty
waiting case.  A waiting par producer is recovered from the reusable
occurrence source index with its exact submitted-link position.  The local
activation primitive then constructs that exact par in the production forest.

The composite `unifyOne?` rule is deliberately singleton-only.  It accepts
exactly `W(j) = [c]` and executes, in order:

1. the synchronized ready-pop/raw-mark prefix;
2. the selected tensor construction;
3. activation of the one waiting par conclusion `c`;
4. the two-level ready/waiting merge.

Thus the successful core contains both a tensor and a par construction and
increments the connective counter twice.  Empty and multi-element waiting
payloads fail closed and remain covered by neither this rule nor an implicit
iteration claim.
-/

namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge
open SequentialUnification

/-- Exact submitted par producer retained for one waiting conclusion.

The source bucket is required to be the singleton containing the exact link
position and value.  The submitted link lookup and local well-formedness are
stored separately so clients never have to replace occurrence identity with a
formula-label equality. -/
structure WaitingParProducer (certificate : Certificate)
    (conclusion : Vertex) : Type where
  linkIndex : Nat
  storedLeft : Vertex
  storedRight : Vertex
  source_eq :
    (SequentialUnification.sourceIndex certificate)[conclusion]? =
      some [{
        linkIndex := linkIndex
        link := .par storedLeft storedRight conclusion }]
  link_eq :
    certificate.links[linkIndex]? =
      some (.par storedLeft storedRight conclusion)
  wellFormed :
    certificate.LinkWellFormed
      (.par storedLeft storedRight conclusion)

/-- Look up the unique exact submitted par producer of a waiting conclusion.

Zero-source, multiple-source, non-par, position-mismatched, and malformed
producer cases all fail closed. -/
def waitingParProducer? (certificate : Certificate)
    (conclusion : Vertex) :
    Option (WaitingParProducer certificate conclusion) :=
  match sourceEquation :
      (SequentialUnification.sourceIndex certificate)[conclusion]? with
  | some [{ linkIndex, link := .par left right actualConclusion }] =>
      if conclusionEquation : actualConclusion = conclusion then
        if linkEquation :
            certificate.links[linkIndex]? =
              some (.par left right actualConclusion) then
          if wellFormedEquation :
              certificate.linkLocallyWellFormed
                  (.par left right actualConclusion) = true then
            some {
              linkIndex
              storedLeft := left
              storedRight := right
              source_eq := by
                simpa [conclusionEquation] using sourceEquation
              link_eq := by
                simpa [conclusionEquation] using linkEquation
              wellFormed := by
                simpa [conclusionEquation] using
                  (certificate.linkLocallyWellFormed_iff
                    (.par left right actualConclusion)).mp
                      wellFormedEquation }
          else
            none
        else
          none
      else
        none
  | _ => none

/-- Every proof-relevant exact producer witness is the canonical executable
lookup result.  Proof irrelevance identifies the stored evidence fields. -/
theorem waitingParProducer?_eq_some
    {certificate : Certificate} {conclusion : Vertex}
    (producer : WaitingParProducer certificate conclusion) :
    waitingParProducer? certificate conclusion = some producer := by
  rcases producer with
    ⟨producerIndex, producerLeft, producerRight,
      producerSource, producerLink, producerWellFormed⟩
  unfold waitingParProducer?
  split
  next linkIndex left right actualConclusion sourceEquation =>
    have singletonEquation :
        ({
          linkIndex := linkIndex
          link := .par left right actualConclusion } :
            SequentialUnification.SourceIncidence) =
          {
            linkIndex := producerIndex
            link := .par producerLeft producerRight conclusion } := by
      exact List.singleton_inj.mp
        (Option.some.inj (sourceEquation.symm.trans producerSource))
    have indexEquation : linkIndex = producerIndex :=
      congrArg SequentialUnification.SourceIncidence.linkIndex
        singletonEquation
    have linkValueEquation :
        (.par left right actualConclusion : Link) =
          .par producerLeft producerRight conclusion :=
      congrArg SequentialUnification.SourceIncidence.link
        singletonEquation
    injection linkValueEquation with leftEquation rightEquation conclusionEquation
    subst linkIndex
    subst left
    subst right
    subst actualConclusion
    simp [producerLink,
      (certificate.linkLocallyWellFormed_iff
        (.par producerLeft producerRight conclusion)).mpr
          producerWellFormed]
  next sourceEquation =>
    exact False.elim
      (sourceEquation producerIndex producerLeft producerRight
        conclusion producerSource)

/-- Independent direct production-state relation for activating one waiting
par conclusion.

The relation uses the read-only source index, token query, component query,
and exact first-occurrence selections, but does not mention
`activateWaitingPar?` or `queuePar?`. -/
def WaitingParActivationRule (certificate : Certificate)
    (before after : UnificationState) (conclusion : Vertex) : Prop :=
  ∃ (linkIndex storedLeft storedRight outputToken : Nat)
      (component : UnificationComponent)
      (leftFocus : Nat) (afterLeft : List Vertex)
      (rightFocus : Nat) (context : List Vertex),
    (SequentialUnification.sourceIndex certificate)[conclusion]? =
      some [{
        linkIndex := linkIndex
        link := .par storedLeft storedRight conclusion }] ∧
    certificate.links[linkIndex]? =
      some (.par storedLeft storedRight conclusion) ∧
    certificate.LinkWellFormed
      (.par storedLeft storedRight conclusion) ∧
    before.forwardToken? storedLeft storedRight conclusion =
      some outputToken ∧
    before.componentAt? outputToken = some component ∧
    Certificate.FirstOccurrencePick component.frontier storedLeft
      leftFocus afterLeft ∧
    Certificate.FirstOccurrencePick afterLeft storedRight
      rightFocus context ∧
    after = {
      before with
      components :=
        before.components.setIfInBounds outputToken
          (some {
            tree := .par leftFocus rightFocus component.tree
            frontier := context ++ [conclusion] })
      firedConnectives := before.firedConnectives + 1 }

/-- Execute one exact waiting-par activation in the production state. -/
def activateWaitingPar? (certificate : Certificate)
    (before : UnificationState) (conclusion : Vertex) :
    Option UnificationState :=
  match waitingParProducer? certificate conclusion with
  | none => none
  | some producer =>
      Certificate.queuePar? before producer.storedLeft
        producer.storedRight conclusion

/-- Exact proof-relevant witness for one waiting-par activation. -/
structure WaitingParActivationStep (certificate : Certificate)
    (before after : UnificationState) (conclusion : Vertex) : Type where
  producer : WaitingParProducer certificate conclusion
  queueStep :
    Certificate.QueueParStep before after producer.storedLeft
      producer.storedRight conclusion
  producer_eq :
    waitingParProducer? certificate conclusion = some producer
  queue_eq :
    Certificate.queuePar? before producer.storedLeft
        producer.storedRight conclusion = some after

/-- Waiting-par activation succeeds exactly when the typed activation witness
exists. -/
theorem activateWaitingPar?_some_iff
    {certificate : Certificate} {before after : UnificationState}
    {conclusion : Vertex} :
    activateWaitingPar? certificate before conclusion = some after ↔
      Nonempty
        (WaitingParActivationStep certificate before after conclusion) := by
  constructor
  · intro equation
    unfold activateWaitingPar? at equation
    cases producerEquation :
        waitingParProducer? certificate conclusion with
    | none => simp [producerEquation] at equation
    | some producer =>
        simp [producerEquation] at equation
        rcases Certificate.queuePar?_some_iff.mp equation with
          ⟨queueStep⟩
        exact ⟨{
          producer
          queueStep
          producer_eq := producerEquation
          queue_eq := equation }⟩
  · rintro ⟨step⟩
    simp [activateWaitingPar?, step.producer_eq, step.queue_eq]

namespace WaitingParActivationStep

/-- The typed activation witness retains the exact submitted par slot and
stored orientation. -/
theorem submitted_par
    {certificate : Certificate} {before after : UnificationState}
    {conclusion : Vertex}
    (step : WaitingParActivationStep certificate before after conclusion) :
    certificate.links[step.producer.linkIndex]? =
      some (.par step.producer.storedLeft
        step.producer.storedRight conclusion) :=
  step.producer.link_eq

/-- A typed executable activation refines the independent direct relation. -/
theorem toRule
    {certificate : Certificate} {before after : UnificationState}
    {conclusion : Vertex}
    (step : WaitingParActivationStep certificate before after conclusion) :
    WaitingParActivationRule certificate before after conclusion := by
  exact ⟨step.producer.linkIndex,
    step.producer.storedLeft,
    step.producer.storedRight,
    step.queueStep.outputToken,
    step.queueStep.component,
    step.queueStep.leftFocus,
    step.queueStep.afterLeft,
    step.queueStep.rightFocus,
    step.queueStep.context,
    step.producer.source_eq,
    step.producer.link_eq,
    step.producer.wellFormed,
    step.queueStep.token_guard,
    step.queueStep.component_lookup,
    step.queueStep.left_pick,
    step.queueStep.right_pick,
    step.queueStep.after_eq⟩

/-- A typed activation changes only the selected component slot and increments
the connective counter once. -/
theorem exact
    {certificate : Certificate} {before after : UnificationState}
    {conclusion : Vertex}
    (step : WaitingParActivationStep certificate before after conclusion) :
    after.components =
        before.components.setIfInBounds step.queueStep.outputToken
          (some {
            tree := .par step.queueStep.leftFocus
              step.queueStep.rightFocus step.queueStep.component.tree
            frontier := step.queueStep.context ++ [conclusion] }) ∧
      after.marks = before.marks ∧
      after.parents = before.parents ∧
      after.startedAxioms = before.startedAxioms ∧
      after.firedConnectives = before.firedConnectives + 1 := by
  rcases step with
    ⟨producer, queueStep, producerEquation, queueEquation⟩
  rcases queueStep with
    ⟨outputToken, component, leftFocus, afterLeft,
      rightFocus, context, tokenGuard, componentLookup,
      leftPick, rightPick, rfl⟩
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The proof-relevant executable activation has one exact output. -/
theorem output_unique
    {certificate : Certificate} {before first second : UnificationState}
    {conclusion : Vertex}
    (left :
      WaitingParActivationStep certificate before first conclusion)
    (right :
      WaitingParActivationStep certificate before second conclusion) :
    first = second := by
  have leftExecutable :
      activateWaitingPar? certificate before conclusion = some first :=
    activateWaitingPar?_some_iff.mpr ⟨left⟩
  have rightExecutable :
      activateWaitingPar? certificate before conclusion = some second :=
    activateWaitingPar?_some_iff.mpr ⟨right⟩
  exact Option.some.inj (leftExecutable.symm.trans rightExecutable)

end WaitingParActivationStep

/-- Executable activation is sound for the independent direct relation. -/
theorem activateWaitingPar?_sound
    {certificate : Certificate} {before after : UnificationState}
    {conclusion : Vertex}
    (equation :
      activateWaitingPar? certificate before conclusion = some after) :
    WaitingParActivationRule certificate before after conclusion := by
  rcases activateWaitingPar?_some_iff.mp equation with ⟨step⟩
  exact step.toRule

/-- Every direct activation witness reconstructs the executable activation.

The direct relation already records the exact singleton source bucket, so this
stronger theorem does not need structural validity. -/
theorem activateWaitingPar?_complete
    {certificate : Certificate} {before after : UnificationState}
    {conclusion : Vertex}
    (rule :
      WaitingParActivationRule certificate before after conclusion) :
    activateWaitingPar? certificate before conclusion = some after := by
  rcases rule with
    ⟨linkIndex, storedLeft, storedRight, outputToken,
      component, leftFocus, afterLeft, rightFocus, context,
      sourceEquation, linkEquation, wellFormed,
      tokenGuard, componentLookup, leftPick, rightPick, afterEquation⟩
  let producer : WaitingParProducer certificate conclusion := {
    linkIndex
    storedLeft
    storedRight
    source_eq := sourceEquation
    link_eq := linkEquation
    wellFormed }
  have producerEquation :
      waitingParProducer? certificate conclusion = some producer := by
    exact waitingParProducer?_eq_some producer
  let queueStep :
      Certificate.QueueParStep before after storedLeft storedRight
        conclusion := {
    outputToken
    component
    leftFocus
    afterLeft
    rightFocus
    context
    token_guard := tokenGuard
    component_lookup := componentLookup
    left_pick := leftPick
    right_pick := rightPick
    after_eq := afterEquation }
  have queueEquation :
      Certificate.queuePar? before storedLeft storedRight conclusion =
        some after :=
    Certificate.queuePar?_some_iff.mpr ⟨queueStep⟩
  simp [activateWaitingPar?, producerEquation, producer, queueEquation]

/-- Structural-validity-specialized completeness API for downstream scheduler
proofs.  Structural validity is stronger than this local exact relation needs. -/
theorem activateWaitingPar?_complete_of_structural
    {certificate : Certificate} {before after : UnificationState}
    {conclusion : Vertex}
    (_structural : certificate.StructurallyWellFormed)
    (rule :
      WaitingParActivationRule certificate before after conclusion) :
    activateWaitingPar? certificate before conclusion = some after :=
  activateWaitingPar?_complete rule

/-- Exact executable/direct correspondence for one waiting-par activation. -/
theorem activateWaitingPar?_some_iff_rule
    {certificate : Certificate} {before after : UnificationState}
    {conclusion : Vertex} :
    activateWaitingPar? certificate before conclusion = some after ↔
      WaitingParActivationRule certificate before after conclusion :=
  ⟨activateWaitingPar?_sound, activateWaitingPar?_complete⟩

/-- The independent direct activation relation has one exact output. -/
theorem WaitingParActivationRule.output_unique
    {certificate : Certificate} {before first second : UnificationState}
    {conclusion : Vertex}
    (left :
      WaitingParActivationRule certificate before first conclusion)
    (right :
      WaitingParActivationRule certificate before second conclusion) :
    first = second := by
  have leftExecutable := activateWaitingPar?_complete left
  have rightExecutable := activateWaitingPar?_complete right
  exact Option.some.inj (leftExecutable.symm.trans rightExecutable)

/-! ## Strict singleton unification -/

/-- Independent Boolean-free Figure-7 `unify` relation for exactly one
waiting par conclusion.

The relation does not mention `unifyOne?`, `prepare?`, `queueTensor?`,
`activateWaitingPar?`, or `mergeTopReadyWaiting?`.  It first states the tensor
mutation propositionally, then applies the independent waiting-par activation
relation to that tensor state, and finally states the exact singleton drain.
The stored tensor orientation and exact submitted tensor position are retained.
-/
def UnifyOneRule (certificate : Certificate)
    (before after : ReservationState) : Prop :=
  ∃ (vertex activeRawAge tensorLinkIndex tensorLeft tensorRight
      tensorConclusion waitingConclusion : Nat),
    ∃ (side : TensorPremiseSide) (middle : ReservationState)
      (mateRawAge previousBoundary : RawTokenAge)
      (leftToken rightToken : Nat)
      (leftComponent rightComponent : UnificationComponent)
      (leftFocus : Nat) (leftContext : List Vertex)
      (rightFocus : Nat) (rightContext : List Vertex)
      (sigmaPrefix : List RawTokenAge)
      (readyPrefix : List (List Vertex))
      (previousReady activeReady : List Vertex)
      (coreTensor : UnificationState),
    RulePrefixAt before middle vertex activeRawAge ∧
    certificate.links[tensorLinkIndex]? =
      some (.tensor tensorLeft tensorRight tensorConclusion) ∧
    certificate.LinkWellFormed
      (.tensor tensorLeft tensorRight tensorConclusion) ∧
    vertex = side.premise tensorLeft tensorRight ∧
    before.core.marks[side.mate tensorLeft tensorRight]? =
      some (some mateRawAge) ∧
    middle.stack.sigma =
      sigmaPrefix ++ [previousBoundary, activeRawAge] ∧
    previousBoundary ≤ mateRawAge ∧
    mateRawAge < activeRawAge ∧
    middle.stack.waiting[previousBoundary]? =
      some (.initialized [waitingConclusion]) ∧
    middle.stack.ready =
      readyPrefix ++ [previousReady, activeReady] ∧
    middle.core.unifyTokens? tensorLeft tensorRight tensorConclusion =
      some (leftToken, rightToken) ∧
    ((side = .storedLeft ∧
        leftToken = activeRawAge ∧
        rightToken = previousBoundary) ∨
      (side = .storedRight ∧
        leftToken = previousBoundary ∧
        rightToken = activeRawAge)) ∧
    middle.core.componentAt? leftToken = some leftComponent ∧
    middle.core.componentAt? rightToken = some rightComponent ∧
    Certificate.FirstOccurrencePick leftComponent.frontier tensorLeft
      leftFocus leftContext ∧
    Certificate.FirstOccurrencePick rightComponent.frontier tensorRight
      rightFocus rightContext ∧
    coreTensor = {
      middle.core with
      parents :=
        middle.core.parents.setIfInBounds
          (max leftToken rightToken) (min leftToken rightToken)
      components :=
        (middle.core.components.setIfInBounds
          (min leftToken rightToken)
          (some {
            tree :=
              .tensor leftFocus rightFocus
                leftComponent.tree rightComponent.tree
            frontier := tensorConclusion :: (leftContext ++ rightContext) }))
          |>.setIfInBounds (max leftToken rightToken) none
      firedConnectives := middle.core.firedConnectives + 1 } ∧
    WaitingParActivationRule certificate coreTensor after.core
      waitingConclusion ∧
    after.stack = {
      middle.stack with
      sigma := sigmaPrefix ++ [previousBoundary]
      ready :=
        readyPrefix ++
          [tensorConclusion ::
            (waitingConclusion :: previousReady ++ activeReady)]
      waiting :=
        middle.stack.waiting.setIfInBounds previousBoundary .undefined } ∧
    after.tags = middle.tags

/-- Representation-only duplicate-freedom required by the deterministic list
refinement of singleton `unify`. -/
def UnifyOneExecutableReadyNodup (certificate : Certificate)
    (before : ReservationState) : Prop :=
  ∀ {after : ReservationState},
    UnifyOneRule certificate before after →
    ∀ {merged : List Vertex},
      after.stack.ready.getLast? = some merged → merged.Nodup

/-- Execute the strict singleton waiting-payload unification slice.

The mutation order is definitionally tensor, then one par activation, then
the scheduler merge.  The waiting-cell pattern accepts exactly one element;
empty and two-or-more payloads fall through to `none`. -/
def unifyOne? (certificate : Certificate)
    (before : ReservationState)
    (_invariant : ReservationInvariant certificate before) :
    Option ReservationState :=
  match prepare? before with
  | none => none
  | some prepared =>
      match certificate.tensorBelow? prepared.stackResult.vertex with
      | none => none
      | some consumer =>
          match prepared.coreMarked.marks[consumer.mate]? with
          | some (some mateRawAge) =>
              match prepared.stackResult.after.sigma.dropLast.getLast? with
              | none => none
              | some previousBoundary =>
                  if _lower : previousBoundary ≤ mateRawAge then
                    if _upper : mateRawAge < prepared.stackResult.rawAge then
                      match prepared.stackResult.after.waiting[
                          previousBoundary]? with
                      | some (.initialized [waitingConclusion]) =>
                          match Certificate.queueTensor? prepared.coreMarked
                              consumer.storedLeft consumer.storedRight
                              consumer.conclusion with
                          | none => none
                          | some coreTensor =>
                              match activateWaitingPar? certificate coreTensor
                                  waitingConclusion with
                              | none => none
                              | some coreAfter =>
                                  match prepared.stackResult.after
                                      |>.mergeTopReadyWaiting?
                                        previousBoundary consumer.conclusion with
                                  | none => none
                                  | some stackAfter =>
                                      match stackAfter.ready.getLast? with
                                      | none => none
                                      | some merged =>
                                          if _readyNodup : merged.Nodup then
                                            some {
                                              stack := stackAfter
                                              core := coreAfter
                                              tags := before.tags }
                                          else
                                            none
                      | _ => none
                    else
                      none
                  else
                    none
          | _ => none

/-- Exact proof-relevant witness for one successful strict singleton
unification. -/
structure UnifyOneStep (certificate : Certificate)
    (before after : ReservationState) : Type where
  before_invariant : ReservationInvariant certificate before
  prepared : PreparedStep before
  consumer : TensorBelow
  mateRawAge : RawTokenAge
  previousBoundary : RawTokenAge
  waitingConclusion : Vertex
  coreTensor : UnificationState
  coreAfter : UnificationState
  stackAfter : SequentialStackState
  merged : List Vertex
  tensorStep :
    Certificate.QueueTensorStep prepared.coreMarked coreTensor
      consumer.storedLeft consumer.storedRight consumer.conclusion
  activationStep :
    WaitingParActivationStep certificate coreTensor coreAfter
      waitingConclusion
  mergeStep :
    MergeTopReadyWaitingStep prepared.stackResult.after stackAfter
      previousBoundary consumer.conclusion
  prepare_eq : prepare? before = some prepared
  consumer_eq :
    certificate.tensorBelow? prepared.stackResult.vertex = some consumer
  mate_marked :
    prepared.coreMarked.marks[consumer.mate]? = some (some mateRawAge)
  lower : previousBoundary ≤ mateRawAge
  upper : mateRawAge < prepared.stackResult.rawAge
  waiting_one :
    prepared.stackResult.after.waiting[previousBoundary]? =
      some (.initialized [waitingConclusion])
  tensor_queue_eq :
    Certificate.queueTensor? prepared.coreMarked
        consumer.storedLeft consumer.storedRight consumer.conclusion =
      some coreTensor
  activation_eq :
    activateWaitingPar? certificate coreTensor waitingConclusion =
      some coreAfter
  stack_merge_eq :
    prepared.stackResult.after.mergeTopReadyWaiting?
        previousBoundary consumer.conclusion = some stackAfter
  merged_eq : stackAfter.ready.getLast? = some merged
  ready_nodup : merged.Nodup
  tokens_eq_adjacent :
    (consumer.side = .storedLeft ∧
        tensorStep.leftToken = prepared.stackResult.rawAge ∧
        tensorStep.rightToken = previousBoundary) ∨
      (consumer.side = .storedRight ∧
        tensorStep.leftToken = previousBoundary ∧
        tensorStep.rightToken = prepared.stackResult.rawAge)
  output_eq :
    after = {
      stack := stackAfter
      core := coreAfter
      tags := before.tags }

private theorem unifyOne_tensor_tokens_eq_adjacent
    {certificate : Certificate} {before : ReservationState}
    {coreTensor : UnificationState}
    (invariant : ReservationInvariant certificate before)
    (prepared : PreparedStep before)
    (consumer : TensorBelow)
    (consumerEquation :
      certificate.tensorBelow? prepared.stackResult.vertex = some consumer)
    (mateRawAge previousBoundary : RawTokenAge)
    (sigmaPrefix : List RawTokenAge)
    (sigmaEquation :
      prepared.stackResult.after.sigma =
        sigmaPrefix ++ [previousBoundary, prepared.stackResult.rawAge])
    (mateMarked :
      prepared.coreMarked.marks[consumer.mate]? =
        some (some mateRawAge))
    (lower : previousBoundary ≤ mateRawAge)
    (upper : mateRawAge < prepared.stackResult.rawAge)
    (step :
      Certificate.QueueTensorStep prepared.coreMarked coreTensor
        consumer.storedLeft consumer.storedRight consumer.conclusion) :
    (consumer.side = .storedLeft ∧
        step.leftToken = prepared.stackResult.rawAge ∧
        step.rightToken = previousBoundary) ∨
      (consumer.side = .storedRight ∧
        step.leftToken = previousBoundary ∧
        step.rightToken = prepared.stackResult.rawAge) := by
  have preparedInvariant :
      ReservationInvariant certificate prepared.after :=
    prepared.reservationInvariant invariant
  have stackWellShaped :
      prepared.stackResult.after.WellShaped certificate.formulas.size := by
    simpa [PreparedStep.after] using preparedInvariant.stack_wellShaped
  have realization :
      RealizesSigma prepared.stackResult.after prepared.coreMarked := by
    simpa [PreparedStep.after] using preparedInvariant.realizesSigma
  rcases SequentialStackState.popReadyMark?_exact prepared.stack_eq with
    ⟨_, _, _, _, _, _, _, _, stackSelectedMarked⟩
  rcases UnificationState.markReadyRaw?_exact prepared.core_mark_eq with
    ⟨_, _, _, _, _, _, coreSelectedMarked⟩
  have activeAgeBound :
      prepared.stackResult.rawAge < prepared.stackResult.after.nextAge :=
    stackWellShaped.assigned_age_bound prepared.stackResult.vertex
      prepared.stackResult.rawAge stackSelectedMarked
  have activeBoundaryLookup :
      sigmaBoundary? prepared.stackResult.after.sigma
          prepared.stackResult.rawAge =
        some prepared.stackResult.rawAge :=
    stackWellShaped.sigma_partition.sigmaBoundary?_eq_top (by
      rw [sigmaEquation]
      simp)
  have activeRealized :
      sigmaBoundary? prepared.stackResult.after.sigma
          prepared.stackResult.rawAge =
        some (prepared.coreMarked.representative
          prepared.stackResult.rawAge) :=
    realization.representative_eq_boundary activeAgeBound
  have activeRoot :
      prepared.coreMarked.representative prepared.stackResult.rawAge =
        prepared.stackResult.rawAge :=
    Option.some.inj (activeRealized.symm.trans activeBoundaryLookup)
  have selectedToken :
      prepared.coreMarked.tokenAt? prepared.stackResult.vertex =
        some prepared.stackResult.rawAge := by
    unfold UnificationState.tokenAt?
    rw [coreSelectedMarked]
    simp [activeRoot]
  have stackMateMarked :
      prepared.stackResult.after.marks[consumer.mate]? =
        some (some mateRawAge) := by
    rw [← realization.marks_eq]
    exact mateMarked
  have mateAgeBound : mateRawAge < prepared.stackResult.after.nextAge :=
    stackWellShaped.assigned_age_bound consumer.mate mateRawAge
      stackMateMarked
  have mateBoundaryLookup :
      sigmaBoundary? prepared.stackResult.after.sigma mateRawAge =
        some previousBoundary :=
    stackWellShaped.sigma_partition
      |>.sigmaBoundary?_eq_previous_of_between sigmaEquation lower upper
  have mateRealized :
      sigmaBoundary? prepared.stackResult.after.sigma mateRawAge =
        some (prepared.coreMarked.representative mateRawAge) :=
    realization.representative_eq_boundary mateAgeBound
  have mateRoot :
      prepared.coreMarked.representative mateRawAge = previousBoundary :=
    Option.some.inj (mateRealized.symm.trans mateBoundaryLookup)
  have mateToken :
      prepared.coreMarked.tokenAt? consumer.mate = some previousBoundary := by
    unfold UnificationState.tokenAt?
    rw [mateMarked]
    simp [mateRoot]
  have tokenGuards :=
    UnificationState.unifyTokens?_success step.token_guard
  cases sideEquation : consumer.side with
  | storedLeft =>
      left
      refine ⟨rfl, ?_, ?_⟩
      · have selectedEquation :
            prepared.stackResult.vertex = consumer.storedLeft := by
          simpa [TensorBelow.premise, TensorPremiseSide.premise,
            sideEquation] using
              Certificate.tensorBelow?_premise consumerEquation
        have selectedStored :
            prepared.coreMarked.tokenAt? consumer.storedLeft =
              some prepared.stackResult.rawAge := by
          simpa [selectedEquation] using selectedToken
        exact Option.some.inj
          (tokenGuards.2.1.symm.trans selectedStored)
      · have mateEquation : consumer.mate = consumer.storedRight := by
          simp [TensorBelow.mate, TensorPremiseSide.mate,
            sideEquation]
        have mateStored :
            prepared.coreMarked.tokenAt? consumer.storedRight =
              some previousBoundary := by
          simpa [mateEquation] using mateToken
        exact Option.some.inj
          (tokenGuards.2.2.1.symm.trans mateStored)
  | storedRight =>
      right
      refine ⟨rfl, ?_, ?_⟩
      · have mateEquation : consumer.mate = consumer.storedLeft := by
          simp [TensorBelow.mate, TensorPremiseSide.mate,
            sideEquation]
        have mateStored :
            prepared.coreMarked.tokenAt? consumer.storedLeft =
              some previousBoundary := by
          simpa [mateEquation] using mateToken
        exact Option.some.inj
          (tokenGuards.2.1.symm.trans mateStored)
      · have selectedEquation :
            prepared.stackResult.vertex = consumer.storedRight := by
          simpa [TensorBelow.premise, TensorPremiseSide.premise,
            sideEquation] using
              Certificate.tensorBelow?_premise consumerEquation
        have selectedStored :
            prepared.coreMarked.tokenAt? consumer.storedRight =
              some prepared.stackResult.rawAge := by
          simpa [selectedEquation] using selectedToken
        exact Option.some.inj
          (tokenGuards.2.2.1.symm.trans selectedStored)

/-- Strict singleton unification succeeds exactly when its typed witness
exists. -/
theorem unifyOne?_some_iff
    {certificate : Certificate} {before after : ReservationState}
    (invariant : ReservationInvariant certificate before) :
    unifyOne? certificate before invariant = some after ↔
      Nonempty (UnifyOneStep certificate before after) := by
  constructor
  · intro equation
    unfold unifyOne? at equation
    cases prepareEquation : prepare? before with
    | none => simp [prepareEquation] at equation
    | some prepared =>
        cases consumerEquation :
            certificate.tensorBelow? prepared.stackResult.vertex with
        | none => simp [prepareEquation, consumerEquation] at equation
        | some consumer =>
            cases mateEquation :
                  prepared.coreMarked.marks[consumer.mate]? with
              | none =>
                  simp [prepareEquation, consumerEquation,
                    mateEquation] at equation
              | some mark =>
                  cases mark with
                  | none =>
                      simp [prepareEquation, consumerEquation,
                        mateEquation] at equation
                  | some mateRawAge =>
                      cases previousEquation :
                          prepared.stackResult.after.sigma.dropLast.getLast? with
                      | none =>
                          simp [prepareEquation, consumerEquation,
                            mateEquation,
                            previousEquation] at equation
                      | some previousBoundary =>
                          by_cases lowerEquation :
                              previousBoundary ≤ mateRawAge
                          · by_cases upperEquation :
                                mateRawAge < prepared.stackResult.rawAge
                            · cases waitingEquation :
                                  prepared.stackResult.after.waiting[
                                    previousBoundary]? with
                              | none =>
                                  simp [prepareEquation, consumerEquation,
                                    mateEquation,
                                    previousEquation, lowerEquation,
                                    upperEquation, waitingEquation] at equation
                              | some cell =>
                                  cases cell with
                                  | undefined =>
                                      simp [prepareEquation, consumerEquation,
                                        mateEquation,
                                        previousEquation, lowerEquation,
                                        upperEquation, waitingEquation]
                                        at equation
                                  | initialized payload =>
                                      cases payload with
                                      | nil =>
                                          simp [prepareEquation,
                                            consumerEquation,
                                            mateEquation, previousEquation,
                                            lowerEquation, upperEquation,
                                            waitingEquation] at equation
                                      | cons waitingConclusion tail =>
                                          cases tail with
                                          | cons second rest =>
                                              simp [prepareEquation,
                                                consumerEquation,
                                                mateEquation,
                                                previousEquation,
                                                lowerEquation, upperEquation,
                                                waitingEquation] at equation
                                          | nil =>
                                              cases tensorQueueEquation :
                                                  Certificate.queueTensor?
                                                    prepared.coreMarked
                                                    consumer.storedLeft
                                                    consumer.storedRight
                                                    consumer.conclusion with
                                              | none =>
                                                  simp [prepareEquation,
                                                    consumerEquation,
                                                    mateEquation,
                                                    previousEquation,
                                                    lowerEquation,
                                                    upperEquation,
                                                    waitingEquation,
                                                    tensorQueueEquation]
                                                    at equation
                                              | some coreTensor =>
                                                  cases activationEquation :
                                                      activateWaitingPar?
                                                        certificate coreTensor
                                                        waitingConclusion with
                                                  | none =>
                                                      simp [prepareEquation,
                                                        consumerEquation,
                                                        mateEquation,
                                                        previousEquation,
                                                        lowerEquation,
                                                        upperEquation,
                                                        waitingEquation,
                                                        tensorQueueEquation,
                                                        activationEquation]
                                                        at equation
                                                  | some coreAfter =>
                                                      cases stackEquation :
                                                          prepared.stackResult.after
                                                            |>.mergeTopReadyWaiting?
                                                              previousBoundary
                                                              consumer.conclusion with
                                                      | none =>
                                                          simp [prepareEquation,
                                                            consumerEquation,
                                                            mateEquation,
                                                            previousEquation,
                                                            lowerEquation,
                                                            upperEquation,
                                                            waitingEquation,
                                                            tensorQueueEquation,
                                                            activationEquation,
                                                            stackEquation]
                                                            at equation
                                                      | some stackAfter =>
                                                          cases mergedEquation :
                                                              stackAfter.ready.getLast? with
                                                          | none =>
                                                              simp [prepareEquation,
                                                                consumerEquation,
                                                                mateEquation,
                                                                previousEquation,
                                                                lowerEquation,
                                                                upperEquation,
                                                                waitingEquation,
                                                                tensorQueueEquation,
                                                                activationEquation,
                                                                stackEquation,
                                                                mergedEquation]
                                                                at equation
                                                          | some merged =>
                                                              by_cases readyNodupEquation :
                                                                  merged.Nodup
                                                              · simp [prepareEquation,
                                                                    consumerEquation,
                                                                    mateEquation,
                                                                    previousEquation,
                                                                    lowerEquation,
                                                                    upperEquation,
                                                                    waitingEquation,
                                                                    tensorQueueEquation,
                                                                    activationEquation,
                                                                    stackEquation,
                                                                    mergedEquation,
                                                                    readyNodupEquation]
                                                                    at equation
                                                                subst after
                                                                rcases
                                                                    Certificate.queueTensor?_some_iff.mp
                                                                      tensorQueueEquation with
                                                                  ⟨tensorStep⟩
                                                                rcases
                                                                    activateWaitingPar?_some_iff.mp
                                                                      activationEquation with
                                                                  ⟨activationStep⟩
                                                                rcases
                                                                    SequentialStackState.mergeTopReadyWaiting?_some_iff.mp
                                                                      stackEquation with
                                                                  ⟨mergeStep⟩
                                                                have activeBoundaryEquation :
                                                                    mergeStep.activeBoundary =
                                                                      prepared.stackResult.rawAge := by
                                                                  have mergeTop :
                                                                      prepared.stackResult.after.sigma.getLast? =
                                                                        some mergeStep.activeBoundary := by
                                                                    rw [mergeStep.sigma_eq]
                                                                    simp
                                                                  have preparedTop :
                                                                      prepared.stackResult.after.sigma.getLast? =
                                                                        some prepared.stackResult.rawAge := by
                                                                    rcases
                                                                        SequentialStackState.popReadyMark?_exact
                                                                          prepared.stack_eq with
                                                                      ⟨_, sigmaTop, _, _, _, sigmaAfter,
                                                                        _, _, _⟩
                                                                    rw [sigmaAfter]
                                                                    exact sigmaTop
                                                                  exact Option.some.inj
                                                                    (mergeTop.symm.trans preparedTop)
                                                                have exactSigma :
                                                                    prepared.stackResult.after.sigma =
                                                                      mergeStep.sigmaPrefix ++
                                                                        [previousBoundary,
                                                                          prepared.stackResult.rawAge] := by
                                                                  simpa [activeBoundaryEquation] using
                                                                    mergeStep.sigma_eq
                                                                have tokenOrientation :=
                                                                  unifyOne_tensor_tokens_eq_adjacent
                                                                    invariant prepared consumer
                                                                    consumerEquation
                                                                    mateRawAge previousBoundary
                                                                    mergeStep.sigmaPrefix exactSigma
                                                                    mateEquation lowerEquation
                                                                    upperEquation tensorStep
                                                                exact ⟨{
                                                                  before_invariant := invariant
                                                                  prepared
                                                                  consumer
                                                                  mateRawAge
                                                                  previousBoundary
                                                                  waitingConclusion
                                                                  coreTensor
                                                                  coreAfter
                                                                  stackAfter
                                                                  merged
                                                                  tensorStep
                                                                  activationStep
                                                                  mergeStep
                                                                  prepare_eq := prepareEquation
                                                                  consumer_eq := consumerEquation
                                                                  mate_marked := mateEquation
                                                                  lower := lowerEquation
                                                                  upper := upperEquation
                                                                  waiting_one := waitingEquation
                                                                  tensor_queue_eq := tensorQueueEquation
                                                                  activation_eq := activationEquation
                                                                  stack_merge_eq := stackEquation
                                                                  merged_eq := mergedEquation
                                                                  ready_nodup := readyNodupEquation
                                                                  tokens_eq_adjacent := tokenOrientation
                                                                  output_eq := rfl }⟩
                                                              · simp [prepareEquation,
                                                                  consumerEquation,
                                                                  mateEquation,
                                                                  previousEquation,
                                                                  lowerEquation,
                                                                  upperEquation,
                                                                  waitingEquation,
                                                                  tensorQueueEquation,
                                                                  activationEquation,
                                                                  stackEquation,
                                                                  mergedEquation,
                                                                  readyNodupEquation]
                                                                  at equation
                            · simp [prepareEquation, consumerEquation,
                                mateEquation,
                                previousEquation, lowerEquation,
                                upperEquation] at equation
                          · simp [prepareEquation, consumerEquation,
                              mateEquation,
                              previousEquation, lowerEquation] at equation
  · rintro ⟨step⟩
    rcases step with
      ⟨stepInvariant, prepared, consumer, mateRawAge,
        previousBoundary, waitingConclusion, coreTensor, coreAfter,
        stackAfter, merged, tensorStep, activationStep, mergeStep,
        prepareEquation, consumerEquation,
        mateEquation, lowerEquation, upperEquation, waitingEquation,
        tensorQueueEquation, activationEquation, stackEquation,
        mergedEquation, readyNodupEquation, tokenOrientation,
        outputEquation⟩
    subst after
    have previousEquation :
        prepared.stackResult.after.sigma.dropLast.getLast? =
          some previousBoundary := by
      rw [mergeStep.sigma_eq]
      simp
    simp [unifyOne?, prepareEquation, consumerEquation,
      mateEquation, previousEquation,
      lowerEquation, upperEquation, waitingEquation,
      tensorQueueEquation, activationEquation, stackEquation,
      mergedEquation, readyNodupEquation]

namespace UnifyOneStep

private theorem activeBoundary_eq
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyOneStep certificate before after) :
    step.mergeStep.activeBoundary = step.prepared.stackResult.rawAge := by
  have mergeTop :
      step.prepared.stackResult.after.sigma.getLast? =
        some step.mergeStep.activeBoundary := by
    rw [step.mergeStep.sigma_eq]
    simp
  have preparedTop :
      step.prepared.stackResult.after.sigma.getLast? =
        some step.prepared.stackResult.rawAge := by
    rcases SequentialStackState.popReadyMark?_exact
        step.prepared.stack_eq with
      ⟨_, sigmaTop, _, _, _, sigmaAfter, _, _, _⟩
    rw [sigmaAfter]
    exact sigmaTop
  exact Option.some.inj (mergeTop.symm.trans preparedTop)

/-- The selected tensor consumer is the exact submitted tensor occurrence. -/
theorem submitted_tensor
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyOneStep certificate before after) :
    certificate.links[step.consumer.linkIndex]? =
      some (.tensor step.consumer.storedLeft
        step.consumer.storedRight step.consumer.conclusion) := by
  exact Certificate.tensorBelow?_link step.consumer_eq

/-- The activated waiting conclusion retains its exact submitted par
position and stored orientation. -/
theorem submitted_waiting_par
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyOneStep certificate before after) :
    certificate.links[step.activationStep.producer.linkIndex]? =
      some (.par step.activationStep.producer.storedLeft
        step.activationStep.producer.storedRight step.waitingConclusion) :=
  step.activationStep.submitted_par

/-- The mate raw age tested after the prefix is its exact pre-prefix mark. -/
theorem mate_marked_before
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyOneStep certificate before after) :
    before.core.marks[step.consumer.mate]? =
      some (some step.mateRawAge) := by
  have markExact :=
    UnificationState.markReadyRaw?_exact step.prepared.core_mark_eq
  have selectedNeMate :
      step.prepared.stackResult.vertex ≠ step.consumer.mate :=
    (Certificate.tensorBelow?_mate_ne step.consumer_eq).symm
  have unchanged :
      step.prepared.coreMarked.marks[step.consumer.mate]? =
        before.core.marks[step.consumer.mate]? := by
    rw [markExact.2.1]
    simp [selectedNeMate]
  exact unchanged.symm.trans step.mate_marked

/-- The equation-backed singleton witness refines the independent direct
relation. -/
theorem toRule
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyOneStep certificate before after) :
    UnifyOneRule certificate before after := by
  have tensorWellFormed :
      certificate.LinkWellFormed
        (.tensor step.consumer.storedLeft step.consumer.storedRight
          step.consumer.conclusion) := by
    exact Certificate.tensorBelow?_wellFormed step.consumer_eq
  have payloadEquation :
      step.mergeStep.payload = [step.waitingConclusion] := by
    exact WaitingCell.initialized.inj
      (Option.some.inj
        (step.mergeStep.waiting_initialized.symm.trans step.waiting_one))
  refine ⟨step.prepared.stackResult.vertex,
    step.prepared.stackResult.rawAge,
    step.consumer.linkIndex,
    step.consumer.storedLeft,
    step.consumer.storedRight,
    step.consumer.conclusion,
    step.waitingConclusion,
    step.consumer.side,
    step.prepared.after,
    step.mateRawAge,
    step.previousBoundary,
    step.tensorStep.leftToken,
    step.tensorStep.rightToken,
    step.tensorStep.leftComponent,
    step.tensorStep.rightComponent,
    step.tensorStep.leftFocus,
    step.tensorStep.leftContext,
    step.tensorStep.rightFocus,
    step.tensorStep.rightContext,
    step.mergeStep.sigmaPrefix,
    step.mergeStep.readyPrefix,
    step.mergeStep.previousReady,
    step.mergeStep.activeReady,
    step.coreTensor,
    RulePrefix.ofPrepared step.prepared,
    step.submitted_tensor,
    tensorWellFormed,
    Certificate.tensorBelow?_premise step.consumer_eq,
    step.mate_marked_before,
    ?_, step.lower, step.upper, step.waiting_one,
    step.mergeStep.ready_eq,
    step.tensorStep.token_guard,
    step.tokens_eq_adjacent,
    step.tensorStep.left_component,
    step.tensorStep.right_component,
    step.tensorStep.left_pick,
    step.tensorStep.right_pick,
    ?_, ?_, ?_, ?_⟩
  · simpa [PreparedStep.after, activeBoundary_eq step] using
      step.mergeStep.sigma_eq
  · simpa [PreparedStep.after] using step.tensorStep.after_eq
  · have coreEquation : after.core = step.coreAfter :=
      congrArg (fun state : ReservationState => state.core) step.output_eq
    rw [coreEquation]
    exact step.activationStep.toRule
  · calc
      after.stack = step.stackAfter :=
        congrArg (fun state : ReservationState => state.stack) step.output_eq
      _ = {
          step.prepared.after.stack with
          sigma := step.mergeStep.sigmaPrefix ++ [step.previousBoundary]
          ready :=
            step.mergeStep.readyPrefix ++
              [step.consumer.conclusion ::
                (step.waitingConclusion :: step.mergeStep.previousReady ++
                  step.mergeStep.activeReady)]
          waiting :=
            step.prepared.after.stack.waiting.setIfInBounds
              step.previousBoundary .undefined } := by
        simpa [PreparedStep.after, payloadEquation] using
          step.mergeStep.after_eq
  · calc
      after.tags = before.tags := by
        simpa using congrArg
          (fun state : ReservationState => state.tags) step.output_eq
      _ = step.prepared.after.tags := rfl

/-- Tensor queuing and the two-level scheduler merge preserve the exact
boundary/representative correspondence before the waiting par changes only
component-tree data. -/
private theorem tensor_realizesSigma
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyOneStep certificate before after) :
    RealizesSigma step.stackAfter step.coreTensor := by
  have middleInvariant :
      ReservationInvariant certificate step.prepared.after :=
    step.prepared.reservationInvariant step.before_invariant
  have middleWellShaped :
      step.prepared.stackResult.after.WellShaped
        certificate.formulas.size := by
    simpa [PreparedStep.after] using middleInvariant.stack_wellShaped
  have middleRealizes :
      RealizesSigma step.prepared.stackResult.after
        step.prepared.coreMarked := by
    simpa [PreparedStep.after] using middleInvariant.realizesSigma
  have middleOrdered : step.prepared.coreMarked.OrderedParents := by
    intro token parent lookup
    exact middleInvariant.core_orderedParents lookup
  have sigmaEquation :
      step.prepared.stackResult.after.sigma =
        step.mergeStep.sigmaPrefix ++
          [step.previousBoundary, step.prepared.stackResult.rawAge] := by
    simpa [activeBoundary_eq step] using step.mergeStep.sigma_eq
  have previousLtActive :
      step.previousBoundary < step.prepared.stackResult.rawAge := by
    have increasing := middleWellShaped.sigma_partition.strictIncreasing
    rw [sigmaEquation] at increasing
    have tailIncreasing :
        [step.previousBoundary,
          step.prepared.stackResult.rawAge].Pairwise (· < ·) :=
      (List.pairwise_append.mp increasing).2.1
    simpa using tailIncreasing
  have maxTokenEquation :
      max step.tensorStep.leftToken step.tensorStep.rightToken =
        step.prepared.stackResult.rawAge := by
    rcases step.tokens_eq_adjacent with orientation | orientation
    · rw [orientation.2.1, orientation.2.2]
      exact Nat.max_eq_left (Nat.le_of_lt previousLtActive)
    · rw [orientation.2.1, orientation.2.2]
      exact Nat.max_eq_right (Nat.le_of_lt previousLtActive)
  have minTokenEquation :
      min step.tensorStep.leftToken step.tensorStep.rightToken =
        step.previousBoundary := by
    rcases step.tokens_eq_adjacent with orientation | orientation
    · rw [orientation.2.1, orientation.2.2]
      exact Nat.min_eq_right (Nat.le_of_lt previousLtActive)
    · rw [orientation.2.1, orientation.2.2]
      exact Nat.min_eq_left (Nat.le_of_lt previousLtActive)
  have stackMarksEquation :
      step.stackAfter.marks = step.prepared.stackResult.after.marks := by
    rw [step.mergeStep.after_eq]
  have stackNextAgeEquation :
      step.stackAfter.nextAge = step.prepared.stackResult.after.nextAge := by
    rw [step.mergeStep.after_eq]
  have stackSigmaEquation :
      step.stackAfter.sigma =
        step.mergeStep.sigmaPrefix ++ [step.previousBoundary] := by
    simpa using congrArg
      (fun state : SequentialStackState => state.sigma)
      step.mergeStep.after_eq
  have coreMarksEquation :
      step.coreTensor.marks = step.prepared.coreMarked.marks := by
    rw [step.tensorStep.after_eq]
  have coreParentsEquation :
      step.coreTensor.parents =
        step.prepared.coreMarked.parents.setIfInBounds
          step.prepared.stackResult.rawAge step.previousBoundary := by
    rw [step.tensorStep.after_eq, maxTokenEquation, minTokenEquation]
  have coreRepresentativeEquation (age : RawTokenAge) :
      step.coreTensor.representative age =
        (step.prepared.coreMarked.setParent
          step.prepared.stackResult.rawAge
          step.previousBoundary).representative age := by
    unfold UnificationState.representative
    rw [coreParentsEquation]
    rfl
  have activeTop :
      step.prepared.stackResult.after.sigma.getLast? =
        some step.prepared.stackResult.rawAge := by
    rw [sigmaEquation]
    simp
  have activeMembership :
      step.prepared.stackResult.rawAge ∈
        step.prepared.stackResult.after.sigma := by
    rw [sigmaEquation]
    simp
  have activeStackBound :
      step.prepared.stackResult.rawAge <
        step.prepared.stackResult.after.nextAge :=
    middleWellShaped.sigma_partition.boundary_lt
      step.prepared.stackResult.rawAge activeMembership
  have previousStackBound :
      step.previousBoundary < step.prepared.stackResult.after.nextAge :=
    Nat.lt_trans previousLtActive activeStackBound
  have activeCoreBound :
      step.prepared.stackResult.rawAge <
        step.prepared.coreMarked.parents.size := by
    rw [middleRealizes.horizon_eq]
    exact activeStackBound
  have previousCoreBound :
      step.previousBoundary < step.prepared.coreMarked.parents.size := by
    rw [middleRealizes.horizon_eq]
    exact previousStackBound
  have activeBoundaryLookup :
      sigmaBoundary? step.prepared.stackResult.after.sigma
          step.prepared.stackResult.rawAge =
        some step.prepared.stackResult.rawAge :=
    middleWellShaped.sigma_partition.sigmaBoundary?_eq_top activeTop
  have activeRealized :
      sigmaBoundary? step.prepared.stackResult.after.sigma
          step.prepared.stackResult.rawAge =
        some (step.prepared.coreMarked.representative
          step.prepared.stackResult.rawAge) :=
    middleRealizes.representative_eq_boundary activeStackBound
  have activeRoot :
      step.prepared.coreMarked.representative
          step.prepared.stackResult.rawAge =
        step.prepared.stackResult.rawAge :=
    Option.some.inj (activeRealized.symm.trans activeBoundaryLookup)
  have previousBoundaryLookup :
      sigmaBoundary? step.prepared.stackResult.after.sigma
          step.previousBoundary = some step.previousBoundary :=
    middleWellShaped.sigma_partition
      |>.sigmaBoundary?_eq_previous_of_between sigmaEquation
        (Nat.le_refl _) previousLtActive
  have previousRealized :
      sigmaBoundary? step.prepared.stackResult.after.sigma
          step.previousBoundary =
        some (step.prepared.coreMarked.representative
          step.previousBoundary) :=
    middleRealizes.representative_eq_boundary previousStackBound
  have previousRoot :
      step.prepared.coreMarked.representative step.previousBoundary =
        step.previousBoundary :=
    Option.some.inj (previousRealized.symm.trans previousBoundaryLookup)
  exact {
    marks_eq := by
      rw [coreMarksEquation, stackMarksEquation]
      exact middleRealizes.marks_eq
    horizon_eq := by
      rw [coreParentsEquation, stackNextAgeEquation]
      simpa using middleRealizes.horizon_eq
    representative_eq_boundary := by
      intro age ageBound
      have oldAgeBound :
          age < step.prepared.stackResult.after.nextAge := by
        simpa [stackNextAgeEquation] using ageBound
      have ageCoreBound :
          age < step.prepared.coreMarked.parents.size := by
        rw [middleRealizes.horizon_eq]
        exact oldAgeBound
      have updatedRepresentative :=
        middleOrdered.setParent_representative
          (survivor := step.previousBoundary)
          (retired := step.prepared.stackResult.rawAge)
          previousCoreBound activeCoreBound previousLtActive
          previousRoot activeRoot ageCoreBound
      by_cases activeLe : step.prepared.stackResult.rawAge ≤ age
      · have oldBoundaryLookup :
            sigmaBoundary? step.prepared.stackResult.after.sigma age =
              some step.prepared.stackResult.rawAge :=
          middleWellShaped.sigma_partition
            |>.sigmaBoundary?_eq_top_of_le activeTop activeLe oldAgeBound
        have oldRealizedAtAge :
            sigmaBoundary? step.prepared.stackResult.after.sigma age =
              some (step.prepared.coreMarked.representative age) :=
          middleRealizes.representative_eq_boundary oldAgeBound
        have oldRepresentativeEquation :
            step.prepared.coreMarked.representative age =
              step.prepared.stackResult.rawAge :=
          Option.some.inj
            (oldRealizedAtAge.symm.trans oldBoundaryLookup)
        have reducedPartition :
            SigmaAgePartition step.prepared.stackResult.after.nextAge
              (step.mergeStep.sigmaPrefix ++ [step.previousBoundary]) :=
          middleWellShaped.sigma_partition.popActive sigmaEquation
        have reducedLookup :
            sigmaBoundary?
                (step.mergeStep.sigmaPrefix ++ [step.previousBoundary]) age =
              some step.previousBoundary :=
          reducedPartition.sigmaBoundary?_eq_top_of_le (by simp)
            (Nat.le_trans (Nat.le_of_lt previousLtActive) activeLe)
            oldAgeBound
        calc
          sigmaBoundary? step.stackAfter.sigma age =
              some step.previousBoundary := by
            rw [stackSigmaEquation]
            exact reducedLookup
          _ = some (step.coreTensor.representative age) := by
            rw [coreRepresentativeEquation, updatedRepresentative,
              if_pos oldRepresentativeEquation]
      · have ageLtActive : age < step.prepared.stackResult.rawAge :=
          Nat.lt_of_not_ge activeLe
        have unchangedBoundary :
            sigmaBoundary? step.stackAfter.sigma age =
              sigmaBoundary? step.prepared.stackResult.after.sigma age := by
          rw [stackSigmaEquation, sigmaEquation]
          rw [show step.mergeStep.sigmaPrefix ++
                [step.previousBoundary, step.prepared.stackResult.rawAge] =
              (step.mergeStep.sigmaPrefix ++ [step.previousBoundary]) ++
                [step.prepared.stackResult.rawAge] by
            simp [List.append_assoc]]
          rw [sigmaBoundary?_append_fresh_old ageLtActive]
        have oldRealizedAtAge :
            sigmaBoundary? step.prepared.stackResult.after.sigma age =
              some (step.prepared.coreMarked.representative age) :=
          middleRealizes.representative_eq_boundary oldAgeBound
        have oldRepresentativeNe :
            step.prepared.coreMarked.representative age ≠
              step.prepared.stackResult.rawAge := by
          intro same
          rw [same] at oldRealizedAtAge
          have boundaryLe := sigmaBoundary?_le oldRealizedAtAge
          exact (Nat.not_le_of_lt ageLtActive) boundaryLe
        calc
          sigmaBoundary? step.stackAfter.sigma age =
              sigmaBoundary? step.prepared.stackResult.after.sigma age :=
            unchangedBoundary
          _ = some (step.prepared.coreMarked.representative age) :=
            middleRealizes.representative_eq_boundary oldAgeBound
          _ = some (step.coreTensor.representative age) := by
            rw [coreRepresentativeEquation, updatedRepresentative,
              if_neg oldRepresentativeNe] }

/-- The waiting par activation leaves marks and parents unchanged, so the
tensor/stack realization transports to the final core. -/
theorem realizesSigma
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyOneStep certificate before after) :
    RealizesSigma step.stackAfter step.coreAfter := by
  have tensorRealizes := step.tensor_realizesSigma
  have activationExact := step.activationStep.exact
  exact {
    marks_eq := by
      rw [activationExact.2.1]
      exact tensorRealizes.marks_eq
    horizon_eq := by
      rw [activationExact.2.2.1]
      exact tensorRealizes.horizon_eq
    representative_eq_boundary := by
      intro age ageBound
      calc
        sigmaBoundary? step.stackAfter.sigma age =
            some (step.coreTensor.representative age) :=
          tensorRealizes.representative_eq_boundary ageBound
        _ = some (step.coreAfter.representative age) := by
          unfold UnificationState.representative
          rw [activationExact.2.2.1] }

/-- Strict singleton tensor-plus-par unification preserves the complete
reservation invariant. -/
theorem reservationInvariant
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyOneStep certificate before after) :
    ReservationInvariant certificate after := by
  have middleInvariant :
      ReservationInvariant certificate step.prepared.after :=
    step.prepared.reservationInvariant step.before_invariant
  have tensorWellFormed :
      certificate.LinkWellFormed
        (.tensor step.consumer.storedLeft step.consumer.storedRight
          step.consumer.conclusion) := by
    exact Certificate.tensorBelow?_wellFormed step.consumer_eq
  have parWellFormed :
      certificate.LinkWellFormed
        (.par step.activationStep.producer.storedLeft
          step.activationStep.producer.storedRight
          step.waitingConclusion) :=
    step.activationStep.producer.wellFormed
  have tensorConclusionBound :
      step.consumer.conclusion < certificate.formulas.size :=
    tensorWellFormed.2.2.2.2.2.1
  have waitingConclusionBound :
      step.waitingConclusion < certificate.formulas.size :=
    parWellFormed.2.2.2.2.2.1
  have payloadInBounds :
      ∀ {payload},
        step.prepared.stackResult.after.waiting[
            step.previousBoundary]? = some (.initialized payload) →
          ∀ vertex ∈ payload, vertex < certificate.formulas.size := by
    intro payload lookup vertex membership
    have payloadEquation : payload = [step.waitingConclusion] :=
      WaitingCell.initialized.inj
        (Option.some.inj (lookup.symm.trans step.waiting_one))
    subst payload
    simp only [List.mem_singleton] at membership
    subst vertex
    exact waitingConclusionBound
  have previousReadyLookup :
      step.prepared.stackResult.after.ready.dropLast.getLast? =
        some step.mergeStep.previousReady := by
    rw [step.mergeStep.ready_eq]
    simp
  have activeReadyLookup :
      step.prepared.stackResult.after.ready.getLast? =
        some step.mergeStep.activeReady := by
    rw [step.mergeStep.ready_eq]
    simp
  have mergedLookup :
      step.stackAfter.ready.getLast? =
        some (step.consumer.conclusion ::
          (step.mergeStep.payload ++ step.mergeStep.previousReady ++
            step.mergeStep.activeReady)) := by
    have readyEquation :
        step.stackAfter.ready =
          step.mergeStep.readyPrefix ++
            [step.consumer.conclusion ::
              (step.mergeStep.payload ++ step.mergeStep.previousReady ++
                step.mergeStep.activeReady)] := by
      simpa using congrArg
        (fun state : SequentialStackState => state.ready)
        step.mergeStep.after_eq
    rw [readyEquation]
    simp
  have exactMerged :
      step.merged =
        step.consumer.conclusion ::
          (step.mergeStep.payload ++ step.mergeStep.previousReady ++
            step.mergeStep.activeReady) :=
    Option.some.inj (step.merged_eq.symm.trans mergedLookup)
  have mergedNodup :
      ∀ {previousReady activeReady payload},
        step.prepared.stackResult.after.ready.dropLast.getLast? =
            some previousReady →
        step.prepared.stackResult.after.ready.getLast? =
            some activeReady →
        step.prepared.stackResult.after.waiting[step.previousBoundary]? =
            some (.initialized payload) →
          (step.consumer.conclusion ::
            (payload ++ previousReady ++ activeReady)).Nodup := by
    intro previousReady activeReady payload
      previousLookup activeLookup waitingLookup
    have previousEquation : previousReady = step.mergeStep.previousReady :=
      Option.some.inj (previousLookup.symm.trans previousReadyLookup)
    have activeEquation : activeReady = step.mergeStep.activeReady :=
      Option.some.inj (activeLookup.symm.trans activeReadyLookup)
    have payloadEquation : payload = step.mergeStep.payload :=
      WaitingCell.initialized.inj
        (Option.some.inj
          (waitingLookup.symm.trans step.mergeStep.waiting_initialized))
    subst previousReady
    subst activeReady
    subst payload
    rw [← exactMerged]
    exact step.ready_nodup
  have stackWellShaped :
      step.stackAfter.WellShaped certificate.formulas.size :=
    SequentialStackState.mergeTopReadyWaiting?_wellShaped
      (by
        simpa [PreparedStep.after] using middleInvariant.stack_wellShaped)
      step.stack_merge_eq tensorConclusionBound payloadInBounds mergedNodup
  have middleWellShapedSelf :
      step.prepared.stackResult.after.WellShaped
        step.prepared.stackResult.after.marks.size := by
    have marksSize :
        step.prepared.stackResult.after.marks.size =
          certificate.formulas.size := by
      simpa [PreparedStep.after] using
        middleInvariant.stack_wellShaped.marks_size
    rw [marksSize]
    simpa [PreparedStep.after] using middleInvariant.stack_wellShaped
  have stackDomain : step.stackAfter.OperationalWaitingDomain :=
    SequentialStackState.mergeTopReadyWaiting?_operationalWaitingDomain
      middleWellShapedSelf
      (by
        simpa [PreparedStep.after] using
          middleInvariant.stack_operationalWaitingDomain)
      step.stack_merge_eq
  have middleOrdered : step.prepared.coreMarked.OrderedParents := by
    intro token parent lookup
    exact middleInvariant.core_orderedParents lookup
  have middleAbstractable :
      step.prepared.coreMarked.Abstractable certificate := by
    simpa [PreparedStep.after] using middleInvariant.core_abstractable
  have middleConsistent :
      step.prepared.coreMarked.ComponentsFormulaConsistent certificate := by
    intro index component lookup
    exact middleInvariant.core_componentsFormulaConsistent lookup
  have tensorAlignment :=
    Certificate.queueTensor?_reservationAlignment
      middleInvariant.core_carriers_aligned
      middleInvariant.core_counter_aligned step.tensor_queue_eq
  have tensorOrdered : step.coreTensor.OrderedParents :=
    Certificate.queueTensor?_orderedParents middleOrdered step.tensor_queue_eq
  have tensorAbstractable : step.coreTensor.Abstractable certificate :=
    Certificate.queueTensor?_abstractable middleAbstractable middleOrdered
      step.tensor_queue_eq
  have tensorConsistent :
      step.coreTensor.ComponentsFormulaConsistent certificate :=
    Certificate.queueTensor?_componentsFormulaConsistent middleConsistent
      tensorWellFormed step.tensor_queue_eq
  have finalAlignment :=
    Certificate.queuePar?_reservationAlignment tensorAlignment.1
      tensorAlignment.2 step.activationStep.queue_eq
  have finalOrdered : step.coreAfter.OrderedParents :=
    Certificate.queuePar?_orderedParents tensorOrdered
      step.activationStep.queue_eq
  have finalAbstractable : step.coreAfter.Abstractable certificate :=
    Certificate.queuePar?_abstractable tensorAbstractable
      step.activationStep.queue_eq
  have finalConsistent :
      step.coreAfter.ComponentsFormulaConsistent certificate :=
    Certificate.queuePar?_componentsFormulaConsistent tensorConsistent
      parWellFormed step.activationStep.queue_eq
  rw [step.output_eq]
  exact {
    stack_wellShaped := stackWellShaped
    stack_operationalWaitingDomain := stackDomain
    realizesSigma := step.realizesSigma
    core_orderedParents := finalOrdered
    core_abstractable := finalAbstractable
    core_componentsFormulaConsistent := finalConsistent
    core_carriers_aligned := finalAlignment.1
    core_counter_aligned := finalAlignment.2
    tags_size := step.before_invariant.tags_size }

/-- The executable core performs exactly two connective constructions: one
tensor followed by one par activation. -/
theorem firedConnectives_eq_add_two
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyOneStep certificate before after) :
    step.coreAfter.firedConnectives =
      step.prepared.coreMarked.firedConnectives + 2 := by
  rcases Certificate.queueTensor?_exact step.tensor_queue_eq with
    ⟨_leftToken, _rightToken, _leftComponent, _rightComponent,
      _leftFocus, _leftContext, _rightFocus, _rightContext,
      _tokenGuard, _leftComponentLookup, _rightComponentLookup,
      _leftPick, _rightPick, _parentsEquation, _componentsEquation,
      _marksEquation, _startedEquation, tensorCounter⟩
  have parCounter := step.activationStep.exact.2.2.2.2
  omega

/-- The successful composite contains both concrete component-tree writes in
the required order: the tensor state is constructed first, and the final core
is obtained by wrapping one component with the exact waiting par. -/
theorem tensor_then_par_components
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyOneStep certificate before after) :
    step.coreTensor.components =
        (step.prepared.coreMarked.components.setIfInBounds
            (min step.tensorStep.leftToken step.tensorStep.rightToken)
            (some {
              tree :=
                .tensor step.tensorStep.leftFocus step.tensorStep.rightFocus
                  step.tensorStep.leftComponent.tree
                  step.tensorStep.rightComponent.tree
              frontier :=
                step.consumer.conclusion ::
                  (step.tensorStep.leftContext ++
                    step.tensorStep.rightContext) })).setIfInBounds
          (max step.tensorStep.leftToken step.tensorStep.rightToken) none ∧
      step.coreAfter.components =
        step.coreTensor.components.setIfInBounds
          step.activationStep.queueStep.outputToken
          (some {
            tree :=
              .par step.activationStep.queueStep.leftFocus
                step.activationStep.queueStep.rightFocus
                step.activationStep.queueStep.component.tree
            frontier :=
              step.activationStep.queueStep.context ++
                [step.waitingConclusion] }) := by
  constructor
  · simpa using congrArg
      (fun state : UnificationState => state.components)
      step.tensorStep.after_eq
  · exact step.activationStep.exact.1

/-- Exact scheduler fields, total counter delta, and stored tensor orientation
of one successful singleton witness. -/
theorem exact
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyOneStep certificate before after) :
    step.stackAfter.sigma =
        step.mergeStep.sigmaPrefix ++ [step.previousBoundary] ∧
      step.stackAfter.ready =
        step.mergeStep.readyPrefix ++
          [step.consumer.conclusion ::
            (step.waitingConclusion :: step.mergeStep.previousReady ++
              step.mergeStep.activeReady)] ∧
      step.stackAfter.waiting =
        step.prepared.stackResult.after.waiting.setIfInBounds
          step.previousBoundary .undefined ∧
      step.coreAfter.firedConnectives = before.core.firedConnectives + 2 ∧
      ((step.consumer.side = .storedLeft ∧
          step.tensorStep.leftToken = step.prepared.stackResult.rawAge ∧
          step.tensorStep.rightToken = step.previousBoundary) ∨
        (step.consumer.side = .storedRight ∧
          step.tensorStep.leftToken = step.previousBoundary ∧
          step.tensorStep.rightToken = step.prepared.stackResult.rawAge)) := by
  have payloadEquation :
      step.mergeStep.payload = [step.waitingConclusion] :=
    WaitingCell.initialized.inj
      (Option.some.inj
        (step.mergeStep.waiting_initialized.symm.trans step.waiting_one))
  have stackFields := congrArg
    (fun state : SequentialStackState =>
      (state.sigma, state.ready, state.waiting))
    step.mergeStep.after_eq
  have counterAfterPrepared := step.firedConnectives_eq_add_two
  rcases UnificationState.markReadyRaw?_exact step.prepared.core_mark_eq with
    ⟨_, _, _, _, _, preparedCounter, _⟩
  refine ⟨?_, ?_, ?_, ?_, step.tokens_eq_adjacent⟩
  · simpa using congrArg Prod.fst stackFields
  · simpa [payloadEquation] using
      congrArg (fun fields => fields.2.1) stackFields
  · simpa using congrArg (fun fields => fields.2.2) stackFields
  · omega

/-- The typed singleton witness has one exact output for fixed input and
invariant proof. -/
theorem output_unique
    {certificate : Certificate}
    {before first second : ReservationState}
    (left : UnifyOneStep certificate before first)
    (right : UnifyOneStep certificate before second) :
    first = second := by
  have invariantEquation :
      left.before_invariant = right.before_invariant :=
    Subsingleton.elim _ _
  cases invariantEquation
  have leftExecutable :
      unifyOne? certificate before left.before_invariant = some first :=
    (unifyOne?_some_iff left.before_invariant).mpr ⟨left⟩
  have rightExecutable :
      unifyOne? certificate before left.before_invariant = some second :=
    (unifyOne?_some_iff left.before_invariant).mpr ⟨right⟩
  exact Option.some.inj (leftExecutable.symm.trans rightExecutable)

end UnifyOneStep

/-- Executable strict singleton unification is sound for the independent
direct relation. -/
theorem unifyOne?_sound
    {certificate : Certificate} {before after : ReservationState}
    (invariant : ReservationInvariant certificate before)
    (equation : unifyOne? certificate before invariant = some after) :
    UnifyOneRule certificate before after := by
  rcases (unifyOne?_some_iff invariant).mp equation with ⟨step⟩
  exact step.toRule

/-- Executable strict singleton tensor-plus-par unification preserves the
complete reservation invariant. -/
theorem unifyOne?_reservationInvariant
    {certificate : Certificate} {before after : ReservationState}
    (invariant : ReservationInvariant certificate before)
    (equation : unifyOne? certificate before invariant = some after) :
    ReservationInvariant certificate after := by
  rcases (unifyOne?_some_iff invariant).mp equation with ⟨step⟩
  exact step.reservationInvariant

private theorem unifyOne_exists_prepared_of_rulePrefixAt
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
      before.core.markReadyRaw? vertex rawAge = .ok middle.core := by
    apply UnificationState.markReadyRaw?_ok_iff.mpr
    exact ⟨{ unmarked := coreUnmarked, after_eq := coreAfter }⟩
  let prepared : PreparedStep before := {
    stackResult
    coreMarked := middle.core
    stack_eq := stackEquation
    core_mark_eq := coreEquation }
  have prepareEquation : prepare? before = some prepared := by
    unfold prepare?
    split
    next stackError stackFailure =>
      rw [stackEquation] at stackFailure
      simp at stackFailure
    next actualStack stackSuccess =>
      have actualStackEquation : actualStack = stackResult :=
        Except.ok.inj (stackSuccess.symm.trans stackEquation)
      subst actualStack
      split
      next coreError coreFailure =>
        rw [coreEquation] at coreFailure
        simp at coreFailure
      next actualCore coreSuccess =>
        have actualCoreEquation : actualCore = middle.core :=
          Except.ok.inj (coreSuccess.symm.trans coreEquation)
        subst actualCore
        congr 2
  refine ⟨prepared, prepareEquation, ?_, rfl, rfl⟩
  cases before
  cases middle
  simp_all [PreparedStep.after, prepared, stackResult]

private theorem unifyOne_exists_tensorBelow
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {vertex linkIndex storedLeft storedRight conclusion : Vertex}
    {side : TensorPremiseSide}
    (linkEquation :
      certificate.links[linkIndex]? =
        some (.tensor storedLeft storedRight conclusion))
    (premiseEquation :
      vertex = side.premise storedLeft storedRight) :
    ∃ consumer : TensorBelow,
      certificate.tensorBelow? vertex = some consumer ∧
      consumer.side = side ∧
      consumer.linkIndex = linkIndex ∧
      consumer.storedLeft = storedLeft ∧
      consumer.storedRight = storedRight ∧
      consumer.conclusion = conclusion ∧
      consumer.mate = side.mate storedLeft storedRight := by
  have linkMembership :
      .tensor storedLeft storedRight conclusion ∈ certificate.links :=
    List.mem_of_getElem? linkEquation
  have wellFormed :
      certificate.LinkWellFormed
        (.tensor storedLeft storedRight conclusion) :=
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
      let consumer : TensorBelow := {
        linkIndex
        storedLeft
        storedRight
        conclusion
        side := .storedLeft }
      refine ⟨consumer, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
      apply Certificate.tensorBelow?_eq_some_iff.mpr
      exact ⟨unique, linkEquation, wellFormed, rfl⟩
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
      let consumer : TensorBelow := {
        linkIndex
        storedLeft
        storedRight
        conclusion
        side := .storedRight }
      refine ⟨consumer, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
      apply Certificate.tensorBelow?_eq_some_iff.mpr
      exact ⟨unique, linkEquation, wellFormed, rfl⟩

/-- On structurally valid input, the independent strict singleton relation is
complete for the executable query when the separate deterministic-list
duplicate-freedom condition is supplied. -/
theorem unifyOne?_complete_of_structural
    {certificate : Certificate} {before after : ReservationState}
    (structural : certificate.StructurallyWellFormed)
    (invariant : ReservationInvariant certificate before)
    (readyShape : UnifyOneExecutableReadyNodup certificate before)
    (rule : UnifyOneRule certificate before after) :
    unifyOne? certificate before invariant = some after := by
  have directRule := rule
  rcases rule with
    ⟨vertex, activeRawAge, tensorLinkIndex, tensorLeft, tensorRight,
      tensorConclusion, waitingConclusion, side, middle, mateRawAge,
      previousBoundary, leftToken, rightToken, leftComponent,
      rightComponent, leftFocus, leftContext, rightFocus, rightContext,
      sigmaPrefix, readyPrefix, previousReady, activeReady, coreTensor,
      prefixRule, tensorLinkEquation, tensorWellFormed,
      premiseEquation, mateMarkedBefore, sigmaEquation, lower, upper,
      waitingOne, readyEquation, tokenGuard, tokenOrientation,
      leftComponentLookup, rightComponentLookup, leftPick, rightPick,
      coreTensorEquation, activationRule, stackAfterEquation,
      tagsAfterEquation⟩
  rcases unifyOne_exists_prepared_of_rulePrefixAt prefixRule with
    ⟨prepared, prepareEquation, middleEquation,
      vertexEquation, rawAgeEquation⟩
  subst middle
  subst vertex
  subst activeRawAge
  rcases unifyOne_exists_tensorBelow structural tensorLinkEquation
      vertexEquation with
    ⟨consumer, consumerEquation, sideEquation, indexEquation,
      leftEquation, rightEquation, conclusionEquation, mateEquation⟩
  subst side
  subst tensorLinkIndex
  subst tensorLeft
  subst tensorRight
  subst tensorConclusion
  have markExact :=
    UnificationState.markReadyRaw?_exact prepared.core_mark_eq
  have selectedNeMate :
      prepared.stackResult.vertex ≠ consumer.mate :=
    (Certificate.tensorBelow?_mate_ne consumerEquation).symm
  have mateMarkedBefore' :
      before.core.marks[consumer.mate]? = some (some mateRawAge) := by
    rw [mateEquation]
    exact mateMarkedBefore
  have mateMarkedAfter :
      prepared.coreMarked.marks[consumer.mate]? =
        some (some mateRawAge) := by
    rw [markExact.2.1]
    simpa [selectedNeMate] using mateMarkedBefore'
  let tensorStep :
      Certificate.QueueTensorStep prepared.coreMarked coreTensor
        consumer.storedLeft consumer.storedRight consumer.conclusion := {
    leftToken
    rightToken
    leftComponent
    rightComponent
    leftFocus
    leftContext
    rightFocus
    rightContext
    token_guard := by
      simpa [PreparedStep.after] using tokenGuard
    left_component := by
      simpa [PreparedStep.after] using leftComponentLookup
    right_component := by
      simpa [PreparedStep.after] using rightComponentLookup
    left_pick := leftPick
    right_pick := rightPick
    after_eq := by
      simpa [PreparedStep.after] using coreTensorEquation }
  have tensorQueueEquation :
      Certificate.queueTensor? prepared.coreMarked
          consumer.storedLeft consumer.storedRight consumer.conclusion =
        some coreTensor :=
    Certificate.queueTensor?_some_iff.mpr ⟨tensorStep⟩
  have activationEquation :
      activateWaitingPar? certificate coreTensor waitingConclusion =
        some after.core :=
    activateWaitingPar?_complete activationRule
  rcases activateWaitingPar?_some_iff.mp activationEquation with
    ⟨activationStep⟩
  let mergeStep :
      MergeTopReadyWaitingStep prepared.stackResult.after after.stack
        previousBoundary consumer.conclusion := {
    sigmaPrefix
    activeBoundary := prepared.stackResult.rawAge
    readyPrefix
    previousReady
    activeReady
    payload := [waitingConclusion]
    sigma_eq := by
      simpa [PreparedStep.after] using sigmaEquation
    ready_eq := by
      simpa [PreparedStep.after] using readyEquation
    waiting_initialized := by
      simpa [PreparedStep.after] using waitingOne
    after_eq := by
      simpa [PreparedStep.after] using stackAfterEquation }
  have stackEquation :
      prepared.stackResult.after.mergeTopReadyWaiting?
          previousBoundary consumer.conclusion = some after.stack :=
    SequentialStackState.mergeTopReadyWaiting?_some_iff.mpr ⟨mergeStep⟩
  let merged : List Vertex :=
    consumer.conclusion ::
      (waitingConclusion :: previousReady ++ activeReady)
  have mergedEquation : after.stack.ready.getLast? = some merged := by
    rw [stackAfterEquation]
    simp [merged]
  have readyNodup : merged.Nodup := readyShape directRule mergedEquation
  have tokenOrientation' :
      (consumer.side = .storedLeft ∧
          tensorStep.leftToken = prepared.stackResult.rawAge ∧
          tensorStep.rightToken = previousBoundary) ∨
        (consumer.side = .storedRight ∧
          tensorStep.leftToken = previousBoundary ∧
          tensorStep.rightToken = prepared.stackResult.rawAge) := by
    simpa [tensorStep] using tokenOrientation
  have outputEquation :
      after = {
        stack := after.stack
        core := after.core
        tags := before.tags } := by
    cases before
    cases after
    simp_all [PreparedStep.after]
  apply (unifyOne?_some_iff invariant).mpr
  exact ⟨{
    before_invariant := invariant
    prepared
    consumer
    mateRawAge
    previousBoundary
    waitingConclusion
    coreTensor
    coreAfter := after.core
    stackAfter := after.stack
    merged
    tensorStep
    activationStep
    mergeStep
    prepare_eq := prepareEquation
    consumer_eq := consumerEquation
    mate_marked := mateMarkedAfter
    lower
    upper
    waiting_one := by
      simpa [PreparedStep.after] using waitingOne
    tensor_queue_eq := tensorQueueEquation
    activation_eq := activationEquation
    stack_merge_eq := stackEquation
    merged_eq := mergedEquation
    ready_nodup := readyNodup
    tokens_eq_adjacent := tokenOrientation'
    output_eq := outputEquation }⟩

/-- Exact executable/declarative correspondence for strict singleton
unification. -/
theorem unifyOne?_some_iff_rule_of_structural
    {certificate : Certificate} {before after : ReservationState}
    (structural : certificate.StructurallyWellFormed)
    (invariant : ReservationInvariant certificate before)
    (readyShape : UnifyOneExecutableReadyNodup certificate before) :
    unifyOne? certificate before invariant = some after ↔
      UnifyOneRule certificate before after :=
  ⟨unifyOne?_sound invariant,
    unifyOne?_complete_of_structural structural invariant readyShape⟩

/-- Under the explicit correspondence premises, the independent strict
singleton relation has one exact output. -/
theorem UnifyOneRule.output_unique_of_structural
    {certificate : Certificate} {before first second : ReservationState}
    (structural : certificate.StructurallyWellFormed)
    (invariant : ReservationInvariant certificate before)
    (readyShape : UnifyOneExecutableReadyNodup certificate before)
    (left : UnifyOneRule certificate before first)
    (right : UnifyOneRule certificate before second) :
    first = second := by
  have leftExecutable :=
    unifyOne?_complete_of_structural structural invariant readyShape left
  have rightExecutable :=
    unifyOne?_complete_of_structural structural invariant readyShape right
  exact Option.some.inj (leftExecutable.symm.trans rightExecutable)

end SequentialFigure7

end ProofNetIR
