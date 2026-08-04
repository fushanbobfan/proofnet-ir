import ProofNetIR.SequentialFigure7UnifyPayloadInvariant

namespace ProofNetIR

/-!
# Input-only applicability for arbitrary-payload Figure-7 unification

This module isolates the read-only conditions which select the general
`UnifyPayload` branch.  `UnifyPayloadEnabled` stores no executor result, no
post-state, and no success equation.  The complete scheduler invariant must
still derive every hidden mutation precondition, including the synchronized
raw mark, exact live-component frontier picks, waiting-payload activation, the
two-level drain, and final ready-bucket duplicate freedom.

The resulting theorem is conditional applicability only.  It does not claim
that every reachable state is enabled, that the canonical dispatcher is
total, or that the worklist strategy is progressive, complete, terminating,
or linear.
-/

namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge
open SequentialUnification

/-- Pure input conditions selecting the arbitrary-payload unification rule.

The ready query fixes the concrete top occurrence.  The sigma decomposition
fixes two adjacent active levels, while the canonical tensor view records one
unique, exact, locally well-formed submitted tensor consumer.  The remaining
fields say that the opposite premise already has a raw age lying in the
previous scheduler interval.  No executable output, intermediate state, or
success equation is stored here. -/
structure UnifyPayloadInput (certificate : Certificate)
    (before : ReservationState) : Type where
  vertex : Vertex
  readyTail : List Vertex
  consumer : TensorBelow
  mateRawAge : RawTokenAge
  sigmaPrefix : List RawTokenAge
  previousBoundary : RawTokenAge
  activeBoundary : RawTokenAge
  top_ready :
    before.stack.ready.getLast? = some (vertex :: readyTail)
  sigma_two_levels :
    before.stack.sigma =
      sigmaPrefix ++ [previousBoundary, activeBoundary]
  consumer_valid :
    consumer.Valid certificate certificate.consumerIndex vertex
  mate_marked :
    before.core.marks[consumer.mate]? = some (some mateRawAge)
  lower : previousBoundary ≤ mateRawAge
  upper : mateRawAge < activeBoundary

/-- Input-only applicability proposition for arbitrary-payload unification.

The data-bearing witness retains the exact selected occurrence, consumer, and
adjacent boundaries without violating proof irrelevance. -/
def UnifyPayloadEnabled (certificate : Certificate)
    (before : ReservationState) : Prop :=
  Nonempty (UnifyPayloadInput certificate before)

namespace UnifyPayloadInput

private theorem vertex_mem_ready
    {certificate : Certificate} {before : ReservationState}
    (enabled : UnifyPayloadInput certificate before) :
    enabled.vertex ∈ before.stack.ready.flatten := by
  apply List.mem_flatten.mpr
  exact ⟨enabled.vertex :: enabled.readyTail,
    List.mem_of_getLast? enabled.top_ready, by simp⟩

private theorem vertex_mem_queued
    {certificate : Certificate} {before : ReservationState}
    (enabled : UnifyPayloadInput certificate before) :
    enabled.vertex ∈ before.stack.queuedVertices := by
  unfold SequentialStackState.queuedVertices
  exact List.mem_append_left _ enabled.vertex_mem_ready

private theorem core_vertex_unmarked
    {certificate : Certificate} {before : ReservationState}
    (enabled : UnifyPayloadInput certificate before)
    (invariant : SchedulerInvariant certificate before) :
    before.core.marks[enabled.vertex]? = some none :=
  invariant.queued_vertices_unmarked enabled.vertex enabled.vertex_mem_queued

private theorem stack_vertex_unmarked
    {certificate : Certificate} {before : ReservationState}
    (enabled : UnifyPayloadInput certificate before)
    (invariant : SchedulerInvariant certificate before) :
    before.stack.marks[enabled.vertex]? = some none := by
  rw [← invariant.realizesSigma.marks_eq]
  exact enabled.core_vertex_unmarked invariant

private theorem sigma_top
    {certificate : Certificate} {before : ReservationState}
    (enabled : UnifyPayloadInput certificate before) :
    before.stack.sigma.getLast? = some enabled.activeBoundary := by
  rw [enabled.sigma_two_levels]
  simp

private theorem previous_lt_active
    {certificate : Certificate} {before : ReservationState}
    (enabled : UnifyPayloadInput certificate before) :
    enabled.previousBoundary < enabled.activeBoundary :=
  Nat.lt_of_le_of_lt enabled.lower enabled.upper

private def stackResult
    {certificate : Certificate} {before : ReservationState}
    (enabled : UnifyPayloadInput certificate before) :
    PopReadyMarkResult where
  vertex := enabled.vertex
  rawAge := enabled.activeBoundary
  remainingTop := enabled.readyTail
  after := {
    before.stack with
    marks :=
      before.stack.marks.setIfInBounds
        enabled.vertex (some enabled.activeBoundary)
    ready := before.stack.ready.dropLast ++ [enabled.readyTail] }

private def coreMarked
    {certificate : Certificate} {before : ReservationState}
    (enabled : UnifyPayloadInput certificate before) :
    UnificationState := {
  before.core with
  marks :=
    before.core.marks.setIfInBounds
      enabled.vertex (some enabled.activeBoundary) }

private theorem stack_pop_eq
    {certificate : Certificate} {before : ReservationState}
    (enabled : UnifyPayloadInput certificate before)
    (invariant : SchedulerInvariant certificate before) :
    before.stack.popReadyMark? = .ok enabled.stackResult := by
  simp [SequentialStackState.popReadyMark?, enabled.top_ready,
    enabled.sigma_top, enabled.stack_vertex_unmarked invariant,
    stackResult]

private theorem core_mark_eq
    {certificate : Certificate} {before : ReservationState}
    (enabled : UnifyPayloadInput certificate before)
    (invariant : SchedulerInvariant certificate before) :
    before.core.markReadyRaw? enabled.vertex enabled.activeBoundary =
      .ok enabled.coreMarked := by
  unfold UnificationState.markReadyRaw?
  rw [enabled.core_vertex_unmarked invariant]
  rfl

private def prepared
    {certificate : Certificate} {before : ReservationState}
    (enabled : UnifyPayloadInput certificate before)
    (invariant : SchedulerInvariant certificate before) :
    PreparedStep before where
  stackResult := enabled.stackResult
  coreMarked := enabled.coreMarked
  stack_eq := enabled.stack_pop_eq invariant
  core_mark_eq := enabled.core_mark_eq invariant

private theorem prepare_eq
    {certificate : Certificate} {before : ReservationState}
    (enabled : UnifyPayloadInput certificate before)
    (invariant : SchedulerInvariant certificate before) :
    prepare? before = some (enabled.prepared invariant) := by
  unfold prepare?
  split
  next stackError stackFailure =>
    rw [enabled.stack_pop_eq invariant] at stackFailure
    simp at stackFailure
  next actualStack stackSuccess =>
    have actualStackEq : actualStack = enabled.stackResult :=
      Except.ok.inj
        (stackSuccess.symm.trans (enabled.stack_pop_eq invariant))
    subst actualStack
    split
    next coreError coreFailure =>
      change
        before.core.markReadyRaw? enabled.vertex enabled.activeBoundary =
          .error coreError at coreFailure
      rw [enabled.core_mark_eq invariant] at coreFailure
      simp at coreFailure
    next actualCore coreSuccess =>
      change
        before.core.markReadyRaw? enabled.vertex enabled.activeBoundary =
          .ok actualCore at coreSuccess
      have actualCoreEq : actualCore = enabled.coreMarked :=
        Except.ok.inj
          (coreSuccess.symm.trans (enabled.core_mark_eq invariant))
      subst actualCore
      congr 2

private theorem consumer_eq
    {certificate : Certificate} {before : ReservationState}
    (enabled : UnifyPayloadInput certificate before) :
    certificate.tensorBelow? enabled.vertex = some enabled.consumer :=
  Certificate.tensorBelow?_eq_some_iff.mpr enabled.consumer_valid

private theorem selected_ne_mate
    {certificate : Certificate} {before : ReservationState}
    (enabled : UnifyPayloadInput certificate before) :
    enabled.vertex ≠ enabled.consumer.mate := by
  exact (Certificate.tensorBelow?_mate_ne enabled.consumer_eq).symm

private theorem prepared_mate_marked
    {certificate : Certificate} {before : ReservationState}
    (enabled : UnifyPayloadInput certificate before)
    (invariant : SchedulerInvariant certificate before) :
    (enabled.prepared invariant).coreMarked.marks[enabled.consumer.mate]? =
      some (some enabled.mateRawAge) := by
  change
    (before.core.marks.setIfInBounds
      enabled.vertex (some enabled.activeBoundary))[enabled.consumer.mate]? =
        some (some enabled.mateRawAge)
  rw [Array.getElem?_setIfInBounds_ne enabled.selected_ne_mate]
  exact enabled.mate_marked

private theorem ready_two_levels
    {certificate : Certificate} {before : ReservationState}
    (enabled : UnifyPayloadInput certificate before)
    (invariant : SchedulerInvariant certificate before) :
    ∃ readyPrefix previousReady,
      before.stack.ready =
        readyPrefix ++
          [previousReady, enabled.vertex :: enabled.readyTail] := by
  rcases List.getLast?_eq_some_iff.mp enabled.top_ready with
    ⟨activePrefix, readyEquation⟩
  have lengthEquation :
      activePrefix.length + 1 = enabled.sigmaPrefix.length + 2 := by
    calc
      activePrefix.length + 1 = before.stack.ready.length := by
        rw [readyEquation]
        simp
      _ = before.stack.sigma.length :=
        invariant.stack_wellShaped.ready_aligned
      _ = enabled.sigmaPrefix.length + 2 := by
        rw [enabled.sigma_two_levels]
        simp
  have activePrefixNonempty : activePrefix ≠ [] := by
    intro empty
    rw [empty] at lengthEquation
    simp at lengthEquation
  cases previousLookup : activePrefix.getLast? with
  | none =>
      have : activePrefix = [] :=
        List.getLast?_eq_none_iff.mp previousLookup
      exact False.elim (activePrefixNonempty this)
  | some previousReady =>
      rcases List.getLast?_eq_some_iff.mp previousLookup with
        ⟨readyPrefix, activePrefixEquation⟩
      refine ⟨readyPrefix, previousReady, ?_⟩
      rw [readyEquation, activePrefixEquation]
      simp [List.append_assoc]

private theorem waiting_payload_exists
    {certificate : Certificate} {before : ReservationState}
    (enabled : UnifyPayloadInput certificate before)
    (invariant : SchedulerInvariant certificate before) :
    ∃ payload,
      before.stack.waiting[enabled.previousBoundary]? =
        some (.initialized payload) := by
  have previousMembership :
      enabled.previousBoundary ∈ before.stack.sigma := by
    rw [enabled.sigma_two_levels]
    simp
  have previousBound :
      enabled.previousBoundary < before.stack.nextAge :=
    invariant.stack_wellShaped.sigma_partition.boundary_lt
      enabled.previousBoundary previousMembership
  have previousInactive :
      enabled.previousBoundary ∈ before.stack.sigma.dropLast := by
    rw [enabled.sigma_two_levels]
    simp
  exact
    (invariant.stack_operationalWaitingDomain
      |>.initialized_iff_inactive previousBound).mpr previousInactive

private theorem waiting_payload_subset_queued
    {certificate : Certificate} {before : ReservationState}
    (enabled : UnifyPayloadInput certificate before)
    {payload : List Vertex}
    (waitingLookup :
      before.stack.waiting[enabled.previousBoundary]? =
        some (.initialized payload)) :
    ∀ {vertex}, vertex ∈ payload →
      vertex ∈ before.stack.queuedVertices := by
  intro vertex membership
  unfold SequentialStackState.queuedVertices
    SequentialStackState.waitingVertices
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨.initialized payload, ?_, ?_⟩
  · exact List.mem_of_getElem? (by simpa using waitingLookup)
  · simpa [WaitingCell.vertices] using membership

private theorem waiting_payload_nodup
    {certificate : Certificate} {before : ReservationState}
    (enabled : UnifyPayloadInput certificate before)
    (invariant : SchedulerInvariant certificate before)
    {payload : List Vertex}
    (waitingLookup :
      before.stack.waiting[enabled.previousBoundary]? =
        some (.initialized payload)) :
    payload.Nodup := by
  have cellMembership :
      (.initialized payload : WaitingCell) ∈ before.stack.waiting.toList :=
    List.mem_of_getElem? (by simpa using waitingLookup)
  have mappedMembership :
      payload ∈
        before.stack.waiting.toList.map WaitingCell.vertices :=
    List.mem_map.mpr
      ⟨(.initialized payload : WaitingCell), cellMembership, rfl⟩
  have waitingSublist :
      List.Sublist payload before.stack.waitingVertices := by
    simpa [SequentialStackState.waitingVertices, List.flatMap] using
      List.sublist_flatten_of_mem mappedMembership
  have queuedSublist :
      List.Sublist payload before.stack.queuedVertices := by
    unfold SequentialStackState.queuedVertices
    exact waitingSublist.trans
      (List.sublist_append_right _ _)
  exact queuedSublist.nodup invariant.queued_vertices_nodup

private theorem waiting_payload_not_ready
    {certificate : Certificate} {before : ReservationState}
    (enabled : UnifyPayloadInput certificate before)
    (invariant : SchedulerInvariant certificate before)
    {payload : List Vertex}
    (waitingLookup :
      before.stack.waiting[enabled.previousBoundary]? =
        some (.initialized payload))
    {vertex : Vertex} (membership : vertex ∈ payload) :
    vertex ∉ before.stack.ready.flatten := by
  have waitingMembership : vertex ∈ before.stack.waitingVertices := by
    unfold SequentialStackState.waitingVertices
    apply List.mem_flatMap.mpr
    refine ⟨.initialized payload, ?_, ?_⟩
    · exact List.mem_of_getElem? (by simpa using waitingLookup)
    · simpa [WaitingCell.vertices] using membership
  have separated := List.nodup_append.mp invariant.queued_vertices_nodup
  intro readyMembership
  exact separated.2.2 vertex readyMembership vertex waitingMembership rfl

private theorem middle_invariant
    {certificate : Certificate} {before : ReservationState}
    (enabled : UnifyPayloadInput certificate before)
    (invariant : SchedulerInvariant certificate before) :
    SchedulerInvariant certificate (enabled.prepared invariant).after :=
  (enabled.prepared invariant).schedulerInvariant invariant

private theorem prepared_vertex_marked
    {certificate : Certificate} {before : ReservationState}
    (enabled : UnifyPayloadInput certificate before)
    (invariant : SchedulerInvariant certificate before) :
    (enabled.prepared invariant).coreMarked.marks[enabled.vertex]? =
      some (some enabled.activeBoundary) :=
  (UnificationState.markReadyRaw?_exact
    (enabled.prepared invariant).core_mark_eq).2.2.2.2.2.2

private theorem selected_token
    {certificate : Certificate} {before : ReservationState}
    (enabled : UnifyPayloadInput certificate before)
    (invariant : SchedulerInvariant certificate before) :
    (enabled.prepared invariant).coreMarked.tokenAt? enabled.vertex =
      some enabled.activeBoundary := by
  have middleInvariant := enabled.middle_invariant invariant
  have stackMarked :
      (enabled.prepared invariant).after.stack.marks[enabled.vertex]? =
        some (some enabled.activeBoundary) := by
    rw [← middleInvariant.realizesSigma.marks_eq]
    exact enabled.prepared_vertex_marked invariant
  have ageBound :
      enabled.activeBoundary <
        (enabled.prepared invariant).after.stack.nextAge :=
    middleInvariant.stack_wellShaped.assigned_age_bound
      enabled.vertex enabled.activeBoundary stackMarked
  have boundaryLookup :
      sigmaBoundary? (enabled.prepared invariant).after.stack.sigma
          enabled.activeBoundary =
        some enabled.activeBoundary := by
    apply middleInvariant.stack_wellShaped.sigma_partition.sigmaBoundary?_eq_top
    change before.stack.sigma.getLast? = some enabled.activeBoundary
    exact enabled.sigma_top
  have realized :
      sigmaBoundary? (enabled.prepared invariant).after.stack.sigma
          enabled.activeBoundary =
        some ((enabled.prepared invariant).coreMarked.representative
          enabled.activeBoundary) :=
    middleInvariant.realizesSigma.representative_eq_boundary ageBound
  have root :
      (enabled.prepared invariant).coreMarked.representative
          enabled.activeBoundary = enabled.activeBoundary :=
    Option.some.inj (realized.symm.trans boundaryLookup)
  unfold UnificationState.tokenAt?
  rw [enabled.prepared_vertex_marked invariant]
  simp [root]

private theorem mate_token
    {certificate : Certificate} {before : ReservationState}
    (enabled : UnifyPayloadInput certificate before)
    (invariant : SchedulerInvariant certificate before) :
    (enabled.prepared invariant).coreMarked.tokenAt?
        enabled.consumer.mate =
      some enabled.previousBoundary := by
  have middleInvariant := enabled.middle_invariant invariant
  have stackMarked :
      (enabled.prepared invariant).after.stack.marks[
          enabled.consumer.mate]? =
        some (some enabled.mateRawAge) := by
    rw [← middleInvariant.realizesSigma.marks_eq]
    exact enabled.prepared_mate_marked invariant
  have ageBound :
      enabled.mateRawAge <
        (enabled.prepared invariant).after.stack.nextAge :=
    middleInvariant.stack_wellShaped.assigned_age_bound
      enabled.consumer.mate enabled.mateRawAge stackMarked
  have boundaryLookup :
      sigmaBoundary? (enabled.prepared invariant).after.stack.sigma
          enabled.mateRawAge =
        some enabled.previousBoundary := by
    apply middleInvariant.stack_wellShaped.sigma_partition
      |>.sigmaBoundary?_eq_previous_of_between
    · change before.stack.sigma =
        enabled.sigmaPrefix ++
          [enabled.previousBoundary, enabled.activeBoundary]
      exact enabled.sigma_two_levels
    · exact enabled.lower
    · exact enabled.upper
  have realized :
      sigmaBoundary? (enabled.prepared invariant).after.stack.sigma
          enabled.mateRawAge =
        some ((enabled.prepared invariant).coreMarked.representative
          enabled.mateRawAge) :=
    middleInvariant.realizesSigma.representative_eq_boundary ageBound
  have root :
      (enabled.prepared invariant).coreMarked.representative
          enabled.mateRawAge = enabled.previousBoundary :=
    Option.some.inj (realized.symm.trans boundaryLookup)
  unfold UnificationState.tokenAt?
  rw [enabled.prepared_mate_marked invariant]
  simp [root]

private theorem submitted_tensor
    {certificate : Certificate} {before : ReservationState}
    (enabled : UnifyPayloadInput certificate before) :
    certificate.links[enabled.consumer.linkIndex]? =
      some (.tensor enabled.consumer.storedLeft
        enabled.consumer.storedRight enabled.consumer.conclusion) :=
  enabled.consumer_valid.2.1

private theorem tensor_wellFormed
    {certificate : Certificate} {before : ReservationState}
    (enabled : UnifyPayloadInput certificate before) :
    certificate.LinkWellFormed
      (.tensor enabled.consumer.storedLeft
        enabled.consumer.storedRight enabled.consumer.conclusion) :=
  enabled.consumer_valid.2.2.1

private theorem selected_eq_premise
    {certificate : Certificate} {before : ReservationState}
    (enabled : UnifyPayloadInput certificate before) :
    enabled.vertex = enabled.consumer.premise :=
  enabled.consumer_valid.2.2.2

private theorem premise_orientation
    {certificate : Certificate} {before : ReservationState}
    (enabled : UnifyPayloadInput certificate before) :
    (enabled.consumer.mate = enabled.consumer.storedLeft ∧
        enabled.vertex = enabled.consumer.storedRight) ∨
      (enabled.consumer.mate = enabled.consumer.storedRight ∧
        enabled.vertex = enabled.consumer.storedLeft) := by
  cases sideEquation : enabled.consumer.side with
  | storedLeft =>
      right
      constructor
      · simp [TensorBelow.mate, TensorPremiseSide.mate, sideEquation]
      · simpa [TensorBelow.premise, TensorPremiseSide.premise,
          sideEquation] using enabled.selected_eq_premise
  | storedRight =>
      left
      constructor
      · simp [TensorBelow.mate, TensorPremiseSide.mate, sideEquation]
      · simpa [TensorBelow.premise, TensorPremiseSide.premise,
          sideEquation] using enabled.selected_eq_premise

private theorem conclusion_ne_selected
    {certificate : Certificate} {before : ReservationState}
    (enabled : UnifyPayloadInput certificate before) :
    enabled.consumer.conclusion ≠ enabled.vertex := by
  rcases enabled.premise_orientation with orientation | orientation
  · exact fun same =>
      enabled.tensor_wellFormed.2.2.1
        (orientation.2.symm.trans same.symm)
  · exact fun same =>
      enabled.tensor_wellFormed.2.1
        (orientation.2.symm.trans same.symm)

private theorem conclusion_not_produced_before
    {certificate : Certificate} {before : ReservationState}
    (enabled : UnifyPayloadInput certificate before)
    (invariant : SchedulerInvariant certificate before) :
    ¬ Produced before enabled.consumer.conclusion := by
  intro produced
  have linkMembership :
      (.tensor enabled.consumer.storedLeft enabled.consumer.storedRight
        enabled.consumer.conclusion : Link) ∈ certificate.links :=
    List.mem_of_getElem? enabled.submitted_tensor
  rcases invariant.produced_premises_marked linkMembership produced with
    ⟨⟨leftAge, leftMarked⟩, rightAge, rightMarked⟩
  rcases enabled.premise_orientation with orientation | orientation
  · have rightUnmarked :
        before.core.marks[enabled.consumer.storedRight]? = some none := by
      rw [← orientation.2]
      exact enabled.core_vertex_unmarked invariant
    rw [rightUnmarked] at rightMarked
    simp at rightMarked
  · have leftUnmarked :
        before.core.marks[enabled.consumer.storedLeft]? = some none := by
      rw [← orientation.2]
      exact enabled.core_vertex_unmarked invariant
    rw [leftUnmarked] at leftMarked
    simp at leftMarked

private theorem conclusion_unmarked_before
    {certificate : Certificate} {before : ReservationState}
    (enabled : UnifyPayloadInput certificate before)
    (invariant : SchedulerInvariant certificate before) :
    before.core.marks[enabled.consumer.conclusion]? = some none := by
  have conclusionBound := enabled.tensor_wellFormed.2.2.2.2.2.1
  have coreMarksSize :
      before.core.marks.size = certificate.formulas.size :=
    invariant.core_abstractable.markArraySize
  have coreConclusionBound :
      enabled.consumer.conclusion < before.core.marks.size := by
    simpa [coreMarksSize] using conclusionBound
  cases conclusionLookup :
      before.core.marks[enabled.consumer.conclusion]? with
  | none =>
      rw [Array.getElem?_eq_getElem coreConclusionBound] at conclusionLookup
      simp at conclusionLookup
  | some mark =>
      cases mark with
      | none => rfl
      | some conclusionAge =>
          exact (enabled.conclusion_not_produced_before invariant
            (Or.inl ⟨conclusionAge, conclusionLookup⟩)).elim

private theorem conclusion_unmarked_middle
    {certificate : Certificate} {before : ReservationState}
    (enabled : UnifyPayloadInput certificate before)
    (invariant : SchedulerInvariant certificate before) :
    (enabled.prepared invariant).coreMarked.marks[
        enabled.consumer.conclusion]? = some none := by
  rcases UnificationState.markReadyRaw?_exact
      (enabled.prepared invariant).core_mark_eq with
    ⟨_, marksEq, _, _, _, _, _⟩
  have selectedNeConclusion :
      (enabled.prepared invariant).stackResult.vertex ≠
        enabled.consumer.conclusion := by
    simpa [prepared, stackResult] using
      enabled.conclusion_ne_selected.symm
  rw [marksEq]
  simpa [Array.getElem?_setIfInBounds,
    selectedNeConclusion] using
      enabled.conclusion_unmarked_before invariant

private theorem ready_mem_liveFrontier
    {certificate : Certificate} {state : ReservationState}
    (invariant : SchedulerInvariant certificate state)
    {vertex : Vertex}
    (membership : vertex ∈ state.stack.ready.flatten) :
    vertex ∈ state.core.liveFrontierVertices := by
  rcases List.mem_flatten.mp membership with
    ⟨bucket, bucketMembership, vertexMembership⟩
  rcases List.mem_iff_getElem.mp bucketMembership with
    ⟨position, positionBound, positionEquation⟩
  have readyLookup : state.stack.ready[position]? = some bucket := by
    rw [List.getElem?_eq_getElem positionBound, positionEquation]
  have sigmaPositionBound : position < state.stack.sigma.length := by
    rw [← invariant.stack_wellShaped.ready_aligned]
    exact positionBound
  let boundary := state.stack.sigma[position]
  have sigmaLookup : state.stack.sigma[position]? = some boundary :=
    List.getElem?_eq_getElem sigmaPositionBound
  rcases invariant.ready_bucket_frontier_exact sigmaLookup readyLookup with
    ⟨component, componentLookup, exactMembership⟩
  have frontierMembership : vertex ∈ component.frontier :=
    (exactMembership vertex).mp vertexMembership |>.1
  unfold UnificationState.liveFrontierVertices
  apply List.mem_flatMap.mpr
  refine ⟨some component, ?_, ?_⟩
  · exact List.mem_of_getElem? (by simpa using componentLookup)
  · simpa using frontierMembership

private theorem conclusion_not_produced_middle
    {certificate : Certificate} {before : ReservationState}
    (enabled : UnifyPayloadInput certificate before)
    (invariant : SchedulerInvariant certificate before) :
    ¬ Produced (enabled.prepared invariant).after
      enabled.consumer.conclusion := by
  intro produced
  apply enabled.conclusion_not_produced_before invariant
  rcases UnificationState.markReadyRaw?_exact
      (enabled.prepared invariant).core_mark_eq with
    ⟨_, marksEq, _, componentsEq, _, _, _⟩
  have selectedNeConclusion :
      (enabled.prepared invariant).stackResult.vertex ≠
        enabled.consumer.conclusion := by
    simpa [prepared, stackResult] using
      enabled.conclusion_ne_selected.symm
  rcases produced with ⟨age, marked⟩ | frontier
  · left
    refine ⟨age, ?_⟩
    change (enabled.prepared invariant).coreMarked.marks[
      enabled.consumer.conclusion]? = some (some age) at marked
    rw [marksEq] at marked
    simpa [Array.getElem?_setIfInBounds,
      selectedNeConclusion] using marked
  · right
    unfold UnificationState.liveFrontierVertices at frontier ⊢
    change enabled.consumer.conclusion ∈
      (enabled.prepared invariant).coreMarked.components.toList.flatMap _
      at frontier
    rw [componentsEq] at frontier
    exact frontier

private theorem conclusion_not_mem_waiting_before
    {certificate : Certificate} {before : ReservationState}
    (enabled : UnifyPayloadInput certificate before)
    (invariant : SchedulerInvariant certificate before) :
    enabled.consumer.conclusion ∉ before.stack.waitingVertices := by
  intro conclusionWaiting
  unfold SequentialStackState.waitingVertices at conclusionWaiting
  rcases List.mem_flatMap.mp conclusionWaiting with
    ⟨cell, cellMembership, conclusionInCell⟩
  cases cell with
  | undefined => simp [WaitingCell.vertices] at conclusionInCell
  | initialized payload =>
      simp only [WaitingCell.vertices] at conclusionInCell
      rcases List.mem_iff_getElem.mp cellMembership with
        ⟨boundary, boundaryBound, boundaryEquation⟩
      have waitingLookup : before.stack.waiting[boundary]? =
          some (.initialized payload) := by
        rw [← Array.getElem?_toList]
        rw [List.getElem?_eq_getElem boundaryBound, boundaryEquation]
      rcases invariant.waiting_span_exact
          waitingLookup conclusionInCell with
        ⟨oldLinkIndex, oldLeft, oldRight, olderPremise,
          youngerPremise, olderAge, youngerAge, youngerBoundary,
          oldLinkLookup, oldSourceLookup, conclusionUnmarked,
          oldOrientation, olderMarked, youngerMarked,
          olderBoundary, youngerBoundaryLookup, boundaryOrder⟩
      have oldLinkMembership :
          (.par oldLeft oldRight enabled.consumer.conclusion : Link) ∈
            certificate.links :=
        List.mem_of_getElem? oldLinkLookup
      have currentLinkMembership :
          (.tensor enabled.consumer.storedLeft enabled.consumer.storedRight
            enabled.consumer.conclusion : Link) ∈ certificate.links :=
        List.mem_of_getElem? enabled.submitted_tensor
      have impossible :=
        UnificationState.StructurallyWellFormed.producerLink_unique
          invariant.structural
          (conclusion := enabled.consumer.conclusion)
          oldLinkMembership (by simp [Link.produces])
          currentLinkMembership (by simp [Link.produces])
      cases impossible

private theorem conclusion_not_mem_waiting_middle
    {certificate : Certificate} {before : ReservationState}
    (enabled : UnifyPayloadInput certificate before)
    (invariant : SchedulerInvariant certificate before) :
    enabled.consumer.conclusion ∉
      (enabled.prepared invariant).after.stack.waitingVertices := by
  intro waiting
  apply enabled.conclusion_not_mem_waiting_before invariant
  exact waiting

private theorem conclusion_not_queued_middle
    {certificate : Certificate} {before : ReservationState}
    (enabled : UnifyPayloadInput certificate before)
    (invariant : SchedulerInvariant certificate before) :
    enabled.consumer.conclusion ∉
      (enabled.prepared invariant).after.stack.queuedVertices := by
  intro queued
  unfold SequentialStackState.queuedVertices at queued
  rcases List.mem_append.mp queued with ready | waiting
  · exact enabled.conclusion_not_produced_middle invariant
      (Or.inr (ready_mem_liveFrontier
        (enabled.middle_invariant invariant) ready))
  · exact enabled.conclusion_not_mem_waiting_middle invariant waiting

private theorem conclusion_not_ready_middle
    {certificate : Certificate} {before : ReservationState}
    (enabled : UnifyPayloadInput certificate before)
    (invariant : SchedulerInvariant certificate before) :
    enabled.consumer.conclusion ∉
      (enabled.prepared invariant).after.stack.ready.flatten := by
  intro ready
  exact enabled.conclusion_not_produced_middle invariant
    (Or.inr (ready_mem_liveFrontier
      (enabled.middle_invariant invariant) ready))

private theorem stored_premise_tokens
    {certificate : Certificate} {before : ReservationState}
    (enabled : UnifyPayloadInput certificate before)
    (invariant : SchedulerInvariant certificate before) :
    ((enabled.prepared invariant).coreMarked.tokenAt?
          enabled.consumer.storedLeft = some enabled.previousBoundary ∧
        (enabled.prepared invariant).coreMarked.tokenAt?
          enabled.consumer.storedRight = some enabled.activeBoundary) ∨
      ((enabled.prepared invariant).coreMarked.tokenAt?
          enabled.consumer.storedLeft = some enabled.activeBoundary ∧
        (enabled.prepared invariant).coreMarked.tokenAt?
          enabled.consumer.storedRight = some enabled.previousBoundary) := by
  rcases enabled.premise_orientation with orientation | orientation
  · left
    constructor
    · rw [← orientation.1]
      exact enabled.mate_token invariant
    · rw [← orientation.2]
      exact enabled.selected_token invariant
  · right
    constructor
    · rw [← orientation.2]
      exact enabled.selected_token invariant
    · rw [← orientation.1]
      exact enabled.mate_token invariant

private theorem tensor_premise_covered
    {certificate : Certificate} {before : ReservationState}
    (enabled : UnifyPayloadInput certificate before)
    (invariant : SchedulerInvariant certificate before)
    {premise token : Nat}
    (premiseMembership : premise ∈
      [enabled.consumer.storedLeft, enabled.consumer.storedRight])
    (tokenAt :
      (enabled.prepared invariant).coreMarked.tokenAt? premise = some token) :
    ∃ component,
      (enabled.prepared invariant).coreMarked.componentAt? token =
          some component ∧
        premise ∈ component.frontier := by
  have middleInvariant := enabled.middle_invariant invariant
  have linkMembership :
      (.tensor enabled.consumer.storedLeft enabled.consumer.storedRight
        enabled.consumer.conclusion : Link) ∈ certificate.links :=
    List.mem_of_getElem? enabled.submitted_tensor
  exact middleInvariant.pending_premises_covered_except_ready
    linkMembership (enabled.conclusion_unmarked_middle invariant)
    (enabled.conclusion_not_ready_middle invariant)
    premiseMembership tokenAt

private theorem tensor_queue_exists
    {certificate : Certificate} {before : ReservationState}
    (enabled : UnifyPayloadInput certificate before)
    (invariant : SchedulerInvariant certificate before) :
    ∃ coreTensor,
      ∃ step : Certificate.QueueTensorStep
          (enabled.prepared invariant).coreMarked coreTensor
          enabled.consumer.storedLeft enabled.consumer.storedRight
          enabled.consumer.conclusion,
        ((step.leftToken = enabled.previousBoundary ∧
            step.rightToken = enabled.activeBoundary) ∨
          (step.leftToken = enabled.activeBoundary ∧
            step.rightToken = enabled.previousBoundary)) ∧
        Certificate.queueTensor? (enabled.prepared invariant).coreMarked
            enabled.consumer.storedLeft enabled.consumer.storedRight
            enabled.consumer.conclusion = some coreTensor := by
  rcases enabled.stored_premise_tokens invariant with
    tokens | tokens
  · rcases enabled.tensor_premise_covered invariant (by simp)
        tokens.1 with ⟨leftComponent, leftLookup, leftMembership⟩
    rcases enabled.tensor_premise_covered invariant (by simp)
        tokens.2 with ⟨rightComponent, rightLookup, rightMembership⟩
    rcases Certificate.FirstOccurrencePick.exists_of_mem leftMembership with
      ⟨leftFocus, leftContext, leftPick⟩
    rcases Certificate.FirstOccurrencePick.exists_of_mem rightMembership with
      ⟨rightFocus, rightContext, rightPick⟩
    have tokenGuard :
        (enabled.prepared invariant).coreMarked.unifyTokens?
            enabled.consumer.storedLeft enabled.consumer.storedRight
            enabled.consumer.conclusion =
          some (enabled.previousBoundary, enabled.activeBoundary) := by
      simp [UnificationState.unifyTokens?,
        enabled.conclusion_unmarked_middle invariant,
        tokens.1, tokens.2,
        Nat.ne_of_lt enabled.previous_lt_active]
    let coreTensor : UnificationState := {
      (enabled.prepared invariant).coreMarked with
      parents :=
        (enabled.prepared invariant).coreMarked.parents.setIfInBounds
          enabled.activeBoundary enabled.previousBoundary
      components :=
        ((enabled.prepared invariant).coreMarked.components.setIfInBounds
          enabled.previousBoundary
          (some {
            tree := .tensor leftFocus rightFocus
              leftComponent.tree rightComponent.tree
            frontier :=
              enabled.consumer.conclusion ::
                (leftContext ++ rightContext) }))
          |>.setIfInBounds enabled.activeBoundary none
      firedConnectives :=
        (enabled.prepared invariant).coreMarked.firedConnectives + 1 }
    let step : Certificate.QueueTensorStep
        (enabled.prepared invariant).coreMarked coreTensor
        enabled.consumer.storedLeft enabled.consumer.storedRight
        enabled.consumer.conclusion := {
      leftToken := enabled.previousBoundary
      rightToken := enabled.activeBoundary
      leftComponent
      rightComponent
      leftFocus
      leftContext
      rightFocus
      rightContext
      token_guard := tokenGuard
      left_component := leftLookup
      right_component := rightLookup
      left_pick := leftPick
      right_pick := rightPick
      after_eq := by
        simp [coreTensor, Nat.min_eq_left
          (Nat.le_of_lt enabled.previous_lt_active),
          Nat.max_eq_right (Nat.le_of_lt enabled.previous_lt_active)] }
    have queueEquation :
        Certificate.queueTensor? (enabled.prepared invariant).coreMarked
            enabled.consumer.storedLeft enabled.consumer.storedRight
            enabled.consumer.conclusion = some coreTensor :=
      Certificate.queueTensor?_some_iff.mpr ⟨step⟩
    exact ⟨coreTensor, step, Or.inl ⟨rfl, rfl⟩, queueEquation⟩
  · rcases enabled.tensor_premise_covered invariant (by simp)
        tokens.1 with ⟨leftComponent, leftLookup, leftMembership⟩
    rcases enabled.tensor_premise_covered invariant (by simp)
        tokens.2 with ⟨rightComponent, rightLookup, rightMembership⟩
    rcases Certificate.FirstOccurrencePick.exists_of_mem leftMembership with
      ⟨leftFocus, leftContext, leftPick⟩
    rcases Certificate.FirstOccurrencePick.exists_of_mem rightMembership with
      ⟨rightFocus, rightContext, rightPick⟩
    have tokenGuard :
        (enabled.prepared invariant).coreMarked.unifyTokens?
            enabled.consumer.storedLeft enabled.consumer.storedRight
            enabled.consumer.conclusion =
          some (enabled.activeBoundary, enabled.previousBoundary) := by
      simp [UnificationState.unifyTokens?,
        enabled.conclusion_unmarked_middle invariant,
        tokens.1, tokens.2,
        Ne.symm (Nat.ne_of_lt enabled.previous_lt_active)]
    let coreTensor : UnificationState := {
      (enabled.prepared invariant).coreMarked with
      parents :=
        (enabled.prepared invariant).coreMarked.parents.setIfInBounds
          enabled.activeBoundary enabled.previousBoundary
      components :=
        ((enabled.prepared invariant).coreMarked.components.setIfInBounds
          enabled.previousBoundary
          (some {
            tree := .tensor leftFocus rightFocus
              leftComponent.tree rightComponent.tree
            frontier :=
              enabled.consumer.conclusion ::
                (leftContext ++ rightContext) }))
          |>.setIfInBounds enabled.activeBoundary none
      firedConnectives :=
        (enabled.prepared invariant).coreMarked.firedConnectives + 1 }
    let step : Certificate.QueueTensorStep
        (enabled.prepared invariant).coreMarked coreTensor
        enabled.consumer.storedLeft enabled.consumer.storedRight
        enabled.consumer.conclusion := {
      leftToken := enabled.activeBoundary
      rightToken := enabled.previousBoundary
      leftComponent
      rightComponent
      leftFocus
      leftContext
      rightFocus
      rightContext
      token_guard := tokenGuard
      left_component := leftLookup
      right_component := rightLookup
      left_pick := leftPick
      right_pick := rightPick
      after_eq := by
        simp [coreTensor, Nat.min_eq_right
          (Nat.le_of_lt enabled.previous_lt_active),
          Nat.max_eq_left (Nat.le_of_lt enabled.previous_lt_active)] }
    have queueEquation :
        Certificate.queueTensor? (enabled.prepared invariant).coreMarked
            enabled.consumer.storedLeft enabled.consumer.storedRight
            enabled.consumer.conclusion = some coreTensor :=
      Certificate.queueTensor?_some_iff.mpr ⟨step⟩
    exact ⟨coreTensor, step, Or.inr ⟨rfl, rfl⟩, queueEquation⟩

/-! The payload fold uses a deliberately smaller input-side induction
predicate.  It records one surviving root component and the exact waiting-par
premises which remain in that component. -/

private def PayloadReadyAtRoot (certificate : Certificate)
    (state : UnificationState) (root : Nat) (payload : List Vertex) : Prop :=
  ∃ component : UnificationComponent,
    state.representative root = root ∧
    state.components[root]? = some (some component) ∧
    payload.Nodup ∧
    ∀ conclusion ∈ payload,
      ∃ producer : WaitingParProducer certificate conclusion,
        state.marks[conclusion]? = some none ∧
        state.tokenAt? producer.storedLeft = some root ∧
        state.tokenAt? producer.storedRight = some root ∧
        producer.storedLeft ∈ component.frontier ∧
        producer.storedRight ∈ component.frontier

private theorem activateWaitingPayload?_exists_of_readyAtRoot
    {certificate : Certificate} {state : UnificationState}
    {root : Nat} {payload : List Vertex}
    (structural : certificate.StructurallyWellFormed)
    (ready : PayloadReadyAtRoot certificate state root payload) :
    ∃ after, activateWaitingPayload? certificate state payload = some after := by
  induction payload generalizing state with
  | nil =>
      exact ⟨state, rfl⟩
  | cons conclusion payload induction =>
      rcases ready with
        ⟨component, rootFixed, componentRaw, payloadNodup, allReady⟩
      rcases allReady conclusion (by simp) with
        ⟨producer, conclusionUnmarked, leftToken, rightToken,
          leftMembership, rightMembership⟩
      have rootBound : root < state.components.size :=
        (Array.getElem?_eq_some_iff.mp componentRaw).1
      have componentLookup : state.componentAt? root = some component := by
        unfold UnificationState.componentAt?
        rw [rootFixed, componentRaw]
        rfl
      have forwardReady :
          state.forwardToken? producer.storedLeft producer.storedRight
              conclusion = some root := by
        simp [UnificationState.forwardToken?, conclusionUnmarked,
          leftToken, rightToken]
      rcases Certificate.FirstOccurrencePick.two_of_mem
          producer.wellFormed.1 leftMembership rightMembership with
        ⟨leftFocus, afterLeft, rightFocus, context, leftPick, rightPick⟩
      let nextComponent : UnificationComponent := {
        tree := .par leftFocus rightFocus component.tree
        frontier := context ++ [conclusion] }
      let middle : UnificationState := {
        state with
        components := state.components.setIfInBounds root (some nextComponent)
        firedConnectives := state.firedConnectives + 1 }
      let queueStep : Certificate.QueueParStep state middle
          producer.storedLeft producer.storedRight conclusion := {
        outputToken := root
        component
        leftFocus
        afterLeft
        rightFocus
        context
        token_guard := forwardReady
        component_lookup := componentLookup
        left_pick := leftPick
        right_pick := rightPick
        after_eq := rfl }
      have queueEquation :
          Certificate.queuePar? state producer.storedLeft
              producer.storedRight conclusion = some middle :=
        Certificate.queuePar?_some_iff.mpr ⟨queueStep⟩
      have headEquation :
          activateWaitingPar? certificate state conclusion = some middle := by
        simp [activateWaitingPar?, waitingParProducer?_eq_some producer,
          queueEquation]
      have tailNodup : payload.Nodup := payloadNodup.tail
      have tailReady : PayloadReadyAtRoot certificate middle root payload := by
        refine ⟨nextComponent, ?_, ?_, tailNodup, ?_⟩
        · exact rootFixed
        · change
            (state.components.setIfInBounds root (some nextComponent))[root]? =
              some (some nextComponent)
          simp [rootBound]
        · intro tailConclusion tailMembership
          rcases allReady tailConclusion (by simp [tailMembership]) with
            ⟨tailProducer, tailUnmarked, tailLeftToken, tailRightToken,
              tailLeftMembership, tailRightMembership⟩
          have conclusionDifferent : tailConclusion ≠ conclusion := by
            intro same
            subst tailConclusion
            exact (List.nodup_cons.mp payloadNodup).1 tailMembership
          have premiseNe
              {premise : Vertex}
              (premiseMembership : premise ∈
                [tailProducer.storedLeft, tailProducer.storedRight]) :
              premise ≠ producer.storedLeft ∧
                premise ≠ producer.storedRight := by
            constructor
            · intro same
              subst premise
              have sameLink :=
                UnificationState.StructurallyWellFormed.parentLink_unique
                  structural
                  (List.mem_of_getElem? tailProducer.link_eq)
                  (by simpa [Link.premises] using premiseMembership)
                  (List.mem_of_getElem? producer.link_eq)
                  (by simp [Link.premises])
              have conclusionEq : tailConclusion = conclusion := by
                have mapped := congrArg
                  (fun link => match link with
                    | .axiom _ _ => 0
                    | .par _ _ produced => produced
                    | .tensor _ _ produced => produced)
                  sameLink
                simpa using mapped
              exact conclusionDifferent conclusionEq
            · intro same
              subst premise
              have sameLink :=
                UnificationState.StructurallyWellFormed.parentLink_unique
                  structural
                  (List.mem_of_getElem? tailProducer.link_eq)
                  (by simpa [Link.premises] using premiseMembership)
                  (List.mem_of_getElem? producer.link_eq)
                  (by simp [Link.premises])
              have conclusionEq : tailConclusion = conclusion := by
                have mapped := congrArg
                  (fun link => match link with
                    | .axiom _ _ => 0
                    | .par _ _ produced => produced
                    | .tensor _ _ produced => produced)
                  sameLink
                simpa using mapped
              exact conclusionDifferent conclusionEq
          have tailLeftNe := premiseNe
            (premise := tailProducer.storedLeft) (by simp)
          have tailRightNe := premiseNe
            (premise := tailProducer.storedRight) (by simp)
          have tailLeftAfterFirst : tailProducer.storedLeft ∈ afterLeft :=
            Certificate.FirstOccurrencePick.mem_remaining_of_ne
              leftPick tailLeftNe.1 tailLeftMembership
          have tailLeftContext : tailProducer.storedLeft ∈ context :=
            Certificate.FirstOccurrencePick.mem_remaining_of_ne
              rightPick tailLeftNe.2 tailLeftAfterFirst
          have tailRightAfterFirst : tailProducer.storedRight ∈ afterLeft :=
            Certificate.FirstOccurrencePick.mem_remaining_of_ne
              leftPick tailRightNe.1 tailRightMembership
          have tailRightContext : tailProducer.storedRight ∈ context :=
            Certificate.FirstOccurrencePick.mem_remaining_of_ne
              rightPick tailRightNe.2 tailRightAfterFirst
          refine ⟨tailProducer, ?_, ?_, ?_, ?_, ?_⟩
          · exact tailUnmarked
          · exact tailLeftToken
          · exact tailRightToken
          · simp [nextComponent, tailLeftContext]
          · simp [nextComponent, tailRightContext]
      rcases induction tailReady with ⟨after, tailEquation⟩
      exact ⟨after, by
        rw [activateWaitingPayload?, headEquation]
        exact tailEquation⟩

private theorem tensor_previous_root
    {certificate : Certificate} {before : ReservationState}
    (enabled : UnifyPayloadInput certificate before)
    (invariant : SchedulerInvariant certificate before)
    {coreTensor : UnificationState}
    (step : Certificate.QueueTensorStep
      (enabled.prepared invariant).coreMarked coreTensor
      enabled.consumer.storedLeft enabled.consumer.storedRight
      enabled.consumer.conclusion)
    (orientation :
      (step.leftToken = enabled.previousBoundary ∧
          step.rightToken = enabled.activeBoundary) ∨
        (step.leftToken = enabled.activeBoundary ∧
          step.rightToken = enabled.previousBoundary)) :
    coreTensor.representative enabled.previousBoundary =
      enabled.previousBoundary := by
  have middleInvariant := enabled.middle_invariant invariant
  have guards := UnificationState.unifyTokens?_success step.token_guard
  have previousBound :
      enabled.previousBoundary <
        (enabled.prepared invariant).coreMarked.parents.size := by
    rcases orientation with left | right
    · rw [← left.1]
      exact middleInvariant.core_abstractable.tokenAt?_bound guards.2.1
    · rw [← right.2]
      exact middleInvariant.core_abstractable.tokenAt?_bound guards.2.2.1
  have activeBound :
      enabled.activeBoundary <
        (enabled.prepared invariant).coreMarked.parents.size := by
    rcases orientation with left | right
    · rw [← left.2]
      exact middleInvariant.core_abstractable.tokenAt?_bound guards.2.2.1
    · rw [← right.1]
      exact middleInvariant.core_abstractable.tokenAt?_bound guards.2.1
  have previousRoot :
      (enabled.prepared invariant).coreMarked.representative
          enabled.previousBoundary = enabled.previousBoundary := by
    rcases orientation with left | right
    · rw [← left.1]
      exact middleInvariant.core_abstractable.tokenAt?_root guards.2.1
    · rw [← right.2]
      exact middleInvariant.core_abstractable.tokenAt?_root guards.2.2.1
  have activeRoot :
      (enabled.prepared invariant).coreMarked.representative
          enabled.activeBoundary = enabled.activeBoundary := by
    rcases orientation with left | right
    · rw [← left.2]
      exact middleInvariant.core_abstractable.tokenAt?_root guards.2.2.1
    · rw [← right.1]
      exact middleInvariant.core_abstractable.tokenAt?_root guards.2.1
  have minEq : min step.leftToken step.rightToken =
      enabled.previousBoundary := by
    rcases orientation with left | right
    · rw [left.1, left.2]
      exact Nat.min_eq_left (Nat.le_of_lt enabled.previous_lt_active)
    · rw [right.1, right.2]
      exact Nat.min_eq_right (Nat.le_of_lt enabled.previous_lt_active)
  have maxEq : max step.leftToken step.rightToken =
      enabled.activeBoundary := by
    rcases orientation with left | right
    · rw [left.1, left.2]
      exact Nat.max_eq_right (Nat.le_of_lt enabled.previous_lt_active)
    · rw [right.1, right.2]
      exact Nat.max_eq_left (Nat.le_of_lt enabled.previous_lt_active)
  have middleOrdered :
      (enabled.prepared invariant).coreMarked.OrderedParents := by
    intro token parent lookup
    exact middleInvariant.core_orderedParents lookup
  have parentsEq : coreTensor.parents =
      (enabled.prepared invariant).coreMarked.parents.setIfInBounds
        enabled.activeBoundary enabled.previousBoundary := by
    rw [step.after_eq]
    simp [minEq, maxEq]
  calc
    coreTensor.representative enabled.previousBoundary =
        ((enabled.prepared invariant).coreMarked.setParent
          enabled.activeBoundary enabled.previousBoundary).representative
            enabled.previousBoundary := by
      unfold UnificationState.representative UnificationState.setParent
      rw [parentsEq]
    _ = if (enabled.prepared invariant).coreMarked.representative
          enabled.previousBoundary = enabled.activeBoundary then
          enabled.previousBoundary
        else (enabled.prepared invariant).coreMarked.representative
          enabled.previousBoundary :=
      UnificationState.OrderedParents.setParent_representative middleOrdered
        previousBound activeBound enabled.previous_lt_active
        previousRoot activeRoot previousBound
    _ = enabled.previousBoundary := by
      rw [previousRoot]
      simp [Nat.ne_of_lt enabled.previous_lt_active]

private def tensorComponent
    {certificate : Certificate} {before : ReservationState}
    (enabled : UnifyPayloadInput certificate before)
    (invariant : SchedulerInvariant certificate before)
    {coreTensor : UnificationState}
    (step : Certificate.QueueTensorStep
      (enabled.prepared invariant).coreMarked coreTensor
      enabled.consumer.storedLeft enabled.consumer.storedRight
      enabled.consumer.conclusion) : UnificationComponent := {
  tree := .tensor step.leftFocus step.rightFocus
    step.leftComponent.tree step.rightComponent.tree
  frontier := enabled.consumer.conclusion ::
    (step.leftContext ++ step.rightContext) }

private theorem tensor_component_previous
    {certificate : Certificate} {before : ReservationState}
    (enabled : UnifyPayloadInput certificate before)
    (invariant : SchedulerInvariant certificate before)
    {coreTensor : UnificationState}
    (step : Certificate.QueueTensorStep
      (enabled.prepared invariant).coreMarked coreTensor
      enabled.consumer.storedLeft enabled.consumer.storedRight
      enabled.consumer.conclusion)
    (orientation :
      (step.leftToken = enabled.previousBoundary ∧
          step.rightToken = enabled.activeBoundary) ∨
        (step.leftToken = enabled.activeBoundary ∧
          step.rightToken = enabled.previousBoundary)) :
    coreTensor.components[enabled.previousBoundary]? =
      some (some (enabled.tensorComponent invariant step)) := by
  have middleInvariant := enabled.middle_invariant invariant
  have guards := UnificationState.unifyTokens?_success step.token_guard
  have previousParentBound :
      enabled.previousBoundary <
        (enabled.prepared invariant).coreMarked.parents.size := by
    rcases orientation with left | right
    · rw [← left.1]
      exact middleInvariant.core_abstractable.tokenAt?_bound guards.2.1
    · rw [← right.2]
      exact middleInvariant.core_abstractable.tokenAt?_bound guards.2.2.1
  have previousComponentBound :
      enabled.previousBoundary <
        (enabled.prepared invariant).coreMarked.components.size := by
    have aligned :
        (enabled.prepared invariant).coreMarked.components.size =
          (enabled.prepared invariant).coreMarked.parents.size := by
      simpa [PreparedStep.after] using
        middleInvariant.core_carriers_aligned
    rw [aligned]
    exact previousParentBound
  have componentsEq : coreTensor.components =
      (((enabled.prepared invariant).coreMarked.components.setIfInBounds
          (min step.leftToken step.rightToken)
          (some (enabled.tensorComponent invariant step)))
        |>.setIfInBounds (max step.leftToken step.rightToken) none) := by
    exact congrArg (fun state : UnificationState => state.components)
      step.after_eq
  rcases orientation with left | right
  · rw [componentsEq, left.1, left.2,
      Nat.min_eq_left (Nat.le_of_lt enabled.previous_lt_active),
      Nat.max_eq_right (Nat.le_of_lt enabled.previous_lt_active),
      Array.getElem?_setIfInBounds_ne
        (Nat.ne_of_gt enabled.previous_lt_active)]
    simp [tensorComponent, previousComponentBound]
  · rw [componentsEq, right.1, right.2,
      Nat.min_eq_right (Nat.le_of_lt enabled.previous_lt_active),
      Nat.max_eq_left (Nat.le_of_lt enabled.previous_lt_active),
      Array.getElem?_setIfInBounds_ne
        (Nat.ne_of_gt enabled.previous_lt_active)]
    simp [tensorComponent, previousComponentBound]

private theorem tensor_tokenAt_previous
    {certificate : Certificate} {before : ReservationState}
    (enabled : UnifyPayloadInput certificate before)
    (invariant : SchedulerInvariant certificate before)
    {coreTensor : UnificationState}
    (step : Certificate.QueueTensorStep
      (enabled.prepared invariant).coreMarked coreTensor
      enabled.consumer.storedLeft enabled.consumer.storedRight
      enabled.consumer.conclusion)
    (orientation :
      (step.leftToken = enabled.previousBoundary ∧
          step.rightToken = enabled.activeBoundary) ∨
        (step.leftToken = enabled.activeBoundary ∧
          step.rightToken = enabled.previousBoundary))
    {vertex boundary : Nat}
    (tokenAt :
      (enabled.prepared invariant).coreMarked.tokenAt? vertex =
        some boundary)
    (boundaryCase :
      boundary = enabled.previousBoundary ∨
        boundary = enabled.activeBoundary) :
    coreTensor.tokenAt? vertex = some enabled.previousBoundary := by
  have middleInvariant := enabled.middle_invariant invariant
  have guards := UnificationState.unifyTokens?_success step.token_guard
  have previousBound :
      enabled.previousBoundary <
        (enabled.prepared invariant).coreMarked.parents.size := by
    rcases orientation with left | right
    · rw [← left.1]
      exact middleInvariant.core_abstractable.tokenAt?_bound guards.2.1
    · rw [← right.2]
      exact middleInvariant.core_abstractable.tokenAt?_bound guards.2.2.1
  have activeBound :
      enabled.activeBoundary <
        (enabled.prepared invariant).coreMarked.parents.size := by
    rcases orientation with left | right
    · rw [← left.2]
      exact middleInvariant.core_abstractable.tokenAt?_bound guards.2.2.1
    · rw [← right.1]
      exact middleInvariant.core_abstractable.tokenAt?_bound guards.2.1
  have previousRoot :
      (enabled.prepared invariant).coreMarked.representative
          enabled.previousBoundary = enabled.previousBoundary := by
    rcases orientation with left | right
    · rw [← left.1]
      exact middleInvariant.core_abstractable.tokenAt?_root guards.2.1
    · rw [← right.2]
      exact middleInvariant.core_abstractable.tokenAt?_root guards.2.2.1
  have activeRoot :
      (enabled.prepared invariant).coreMarked.representative
          enabled.activeBoundary = enabled.activeBoundary := by
    rcases orientation with left | right
    · rw [← left.2]
      exact middleInvariant.core_abstractable.tokenAt?_root guards.2.2.1
    · rw [← right.1]
      exact middleInvariant.core_abstractable.tokenAt?_root guards.2.1
  have minEq : min step.leftToken step.rightToken =
      enabled.previousBoundary := by
    rcases orientation with left | right
    · rw [left.1, left.2]
      exact Nat.min_eq_left (Nat.le_of_lt enabled.previous_lt_active)
    · rw [right.1, right.2]
      exact Nat.min_eq_right (Nat.le_of_lt enabled.previous_lt_active)
  have maxEq : max step.leftToken step.rightToken =
      enabled.activeBoundary := by
    rcases orientation with left | right
    · rw [left.1, left.2]
      exact Nat.max_eq_right (Nat.le_of_lt enabled.previous_lt_active)
    · rw [right.1, right.2]
      exact Nat.max_eq_left (Nat.le_of_lt enabled.previous_lt_active)
  have parentsEq : coreTensor.parents =
      (enabled.prepared invariant).coreMarked.parents.setIfInBounds
        enabled.activeBoundary enabled.previousBoundary := by
    rw [step.after_eq]
    simp [minEq, maxEq]
  have middleOrdered :
      (enabled.prepared invariant).coreMarked.OrderedParents := by
    intro token parent lookup
    exact middleInvariant.core_orderedParents lookup
  rcases (enabled.prepared invariant).coreMarked.tokenAt?_some_witness
      tokenAt with ⟨rawAge, assigned, representativeEq⟩
  have rawBound :
      rawAge < (enabled.prepared invariant).coreMarked.parents.size :=
    middleInvariant.core_abstractable.markedTokenBound assigned
  have representativeAfter :
      coreTensor.representative rawAge =
        if (enabled.prepared invariant).coreMarked.representative rawAge =
            enabled.activeBoundary then
          enabled.previousBoundary
        else (enabled.prepared invariant).coreMarked.representative rawAge := by
    calc
      coreTensor.representative rawAge =
          ((enabled.prepared invariant).coreMarked.setParent
            enabled.activeBoundary enabled.previousBoundary).representative
              rawAge := by
        unfold UnificationState.representative UnificationState.setParent
        rw [parentsEq]
      _ = _ :=
        UnificationState.OrderedParents.setParent_representative
          middleOrdered previousBound activeBound
          enabled.previous_lt_active previousRoot activeRoot rawBound
  have marksEq : coreTensor.marks =
      (enabled.prepared invariant).coreMarked.marks := by
    simpa using congrArg (fun state : UnificationState => state.marks)
      step.after_eq
  have marked :=
    UnificationState.assignedToken?_some_raw assigned
  unfold UnificationState.tokenAt?
  rw [marksEq, marked]
  change some (coreTensor.representative rawAge) =
    some enabled.previousBoundary
  rw [representativeAfter, representativeEq]
  rcases boundaryCase with rfl | rfl
  · simp [Nat.ne_of_lt enabled.previous_lt_active]
  · simp

private theorem waiting_premise_ready_after_tensor
    {certificate : Certificate} {before : ReservationState}
    (enabled : UnifyPayloadInput certificate before)
    (invariant : SchedulerInvariant certificate before)
    {coreTensor : UnificationState}
    (step : Certificate.QueueTensorStep
      (enabled.prepared invariant).coreMarked coreTensor
      enabled.consumer.storedLeft enabled.consumer.storedRight
      enabled.consumer.conclusion)
    (orientation :
      (step.leftToken = enabled.previousBoundary ∧
          step.rightToken = enabled.activeBoundary) ∨
        (step.leftToken = enabled.activeBoundary ∧
          step.rightToken = enabled.previousBoundary))
    {left right conclusion premise boundary : Nat}
    (linkMembership : (.par left right conclusion : Link) ∈
      certificate.links)
    (conclusionUnmarked :
      (enabled.prepared invariant).coreMarked.marks[conclusion]? = some none)
    (conclusionNotReady : conclusion ∉
      (enabled.prepared invariant).after.stack.ready.flatten)
    (premiseMembership : premise ∈ [left, right])
    (tokenAt :
      (enabled.prepared invariant).coreMarked.tokenAt? premise =
        some boundary)
    (boundaryCase :
      boundary = enabled.previousBoundary ∨
        boundary = enabled.activeBoundary) :
    coreTensor.tokenAt? premise = some enabled.previousBoundary ∧
      premise ∈ (enabled.tensorComponent invariant step).frontier := by
  have middleInvariant := enabled.middle_invariant invariant
  rcases middleInvariant.pending_premises_covered_except_ready
      linkMembership conclusionUnmarked conclusionNotReady
      premiseMembership tokenAt with
    ⟨component, componentLookup, premiseFrontier⟩
  have tensorMembership :
      (.tensor enabled.consumer.storedLeft enabled.consumer.storedRight
        enabled.consumer.conclusion : Link) ∈ certificate.links :=
    List.mem_of_getElem? enabled.submitted_tensor
  have premiseNeLeft : premise ≠ enabled.consumer.storedLeft := by
    intro same
    subst premise
    have sameLink :=
      UnificationState.StructurallyWellFormed.parentLink_unique
        invariant.structural linkMembership
        (by simpa [Link.premises] using premiseMembership)
        tensorMembership (by simp [Link.premises])
    cases sameLink
  have premiseNeRight : premise ≠ enabled.consumer.storedRight := by
    intro same
    subst premise
    have sameLink :=
      UnificationState.StructurallyWellFormed.parentLink_unique
        invariant.structural linkMembership
        (by simpa [Link.premises] using premiseMembership)
        tensorMembership (by simp [Link.premises])
    cases sameLink
  refine ⟨enabled.tensor_tokenAt_previous invariant step orientation
    tokenAt boundaryCase, ?_⟩
  rcases orientation with leftOrientation | rightOrientation
  · rcases boundaryCase with previous | active
    · have lookup :
          (enabled.prepared invariant).coreMarked.componentAt? boundary =
            some step.leftComponent := by
        rw [previous, ← leftOrientation.1]
        exact step.left_component
      have componentEq : component = step.leftComponent :=
        Option.some.inj (componentLookup.symm.trans lookup)
      subst component
      have contextMembership :=
        Certificate.FirstOccurrencePick.mem_remaining_of_ne
          step.left_pick premiseNeLeft premiseFrontier
      simp [tensorComponent, contextMembership]
    · have lookup :
          (enabled.prepared invariant).coreMarked.componentAt? boundary =
            some step.rightComponent := by
        rw [active, ← leftOrientation.2]
        exact step.right_component
      have componentEq : component = step.rightComponent :=
        Option.some.inj (componentLookup.symm.trans lookup)
      subst component
      have contextMembership :=
        Certificate.FirstOccurrencePick.mem_remaining_of_ne
          step.right_pick premiseNeRight premiseFrontier
      simp [tensorComponent, contextMembership]
  · rcases boundaryCase with previous | active
    · have lookup :
          (enabled.prepared invariant).coreMarked.componentAt? boundary =
            some step.rightComponent := by
        rw [previous, ← rightOrientation.2]
        exact step.right_component
      have componentEq : component = step.rightComponent :=
        Option.some.inj (componentLookup.symm.trans lookup)
      subst component
      have contextMembership :=
        Certificate.FirstOccurrencePick.mem_remaining_of_ne
          step.right_pick premiseNeRight premiseFrontier
      simp [tensorComponent, contextMembership]
    · have lookup :
          (enabled.prepared invariant).coreMarked.componentAt? boundary =
            some step.leftComponent := by
        rw [active, ← rightOrientation.1]
        exact step.left_component
      have componentEq : component = step.leftComponent :=
        Option.some.inj (componentLookup.symm.trans lookup)
      subst component
      have contextMembership :=
        Certificate.FirstOccurrencePick.mem_remaining_of_ne
          step.left_pick premiseNeLeft premiseFrontier
      simp [tensorComponent, contextMembership]

private theorem later_boundary_eq_active
    {certificate : Certificate} {before : ReservationState}
    (enabled : UnifyPayloadInput certificate before)
    (invariant : SchedulerInvariant certificate before)
    {boundary : RawTokenAge}
    (membership : boundary ∈
      (enabled.prepared invariant).after.stack.sigma)
    (later : enabled.previousBoundary < boundary) :
    boundary = enabled.activeBoundary := by
  have middleInvariant := enabled.middle_invariant invariant
  have increasing :
      (enabled.sigmaPrefix ++
        [enabled.previousBoundary, enabled.activeBoundary]).Pairwise
          (· < ·) := by
    have source := middleInvariant.stack_wellShaped
      |>.sigma_partition.strictIncreasing
    change before.stack.sigma.Pairwise (· < ·) at source
    simpa [enabled.sigma_two_levels] using source
  change boundary ∈ before.stack.sigma at membership
  rw [enabled.sigma_two_levels] at membership
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    at membership
  rcases membership with inPrefix | atPrevious | atActive
  · have boundaryLtPrevious : boundary < enabled.previousBoundary :=
      (List.pairwise_append.mp increasing).2.2
        boundary inPrefix enabled.previousBoundary (by simp)
    exact False.elim ((Nat.lt_asymm later) boundaryLtPrevious)
  · subst boundary
    exact False.elim (Nat.lt_irrefl _ later)
  · exact atActive

private theorem middle_token_of_boundary
    {certificate : Certificate} {before : ReservationState}
    (enabled : UnifyPayloadInput certificate before)
    (invariant : SchedulerInvariant certificate before)
    {vertex rawAge boundary : Nat}
    (marked :
      (enabled.prepared invariant).coreMarked.marks[vertex]? =
        some (some rawAge))
    (boundaryLookup :
      sigmaBoundary? (enabled.prepared invariant).after.stack.sigma rawAge =
        some boundary) :
    (enabled.prepared invariant).coreMarked.tokenAt? vertex =
      some boundary := by
  have middleInvariant := enabled.middle_invariant invariant
  have stackMarked :
      (enabled.prepared invariant).after.stack.marks[vertex]? =
        some (some rawAge) := by
    rw [← middleInvariant.realizesSigma.marks_eq]
    exact marked
  have ageBound : rawAge <
      (enabled.prepared invariant).after.stack.nextAge :=
    middleInvariant.stack_wellShaped.assigned_age_bound
      vertex rawAge stackMarked
  have realized :
      sigmaBoundary? (enabled.prepared invariant).after.stack.sigma rawAge =
        some ((enabled.prepared invariant).coreMarked.representative
          rawAge) :=
    middleInvariant.realizesSigma.representative_eq_boundary ageBound
  have representativeEq :
      (enabled.prepared invariant).coreMarked.representative rawAge =
        boundary :=
    Option.some.inj (realized.symm.trans boundaryLookup)
  unfold UnificationState.tokenAt?
  rw [marked]
  simp [representativeEq]

private theorem payload_ready_after_tensor
    {certificate : Certificate} {before : ReservationState}
    (enabled : UnifyPayloadInput certificate before)
    (invariant : SchedulerInvariant certificate before)
    {payload : List Vertex}
    (waitingLookup :
      before.stack.waiting[enabled.previousBoundary]? =
        some (.initialized payload))
    {coreTensor : UnificationState}
    (step : Certificate.QueueTensorStep
      (enabled.prepared invariant).coreMarked coreTensor
      enabled.consumer.storedLeft enabled.consumer.storedRight
      enabled.consumer.conclusion)
    (orientation :
      (step.leftToken = enabled.previousBoundary ∧
          step.rightToken = enabled.activeBoundary) ∨
        (step.leftToken = enabled.activeBoundary ∧
          step.rightToken = enabled.previousBoundary)) :
    PayloadReadyAtRoot certificate coreTensor
      enabled.previousBoundary payload := by
  have middleInvariant := enabled.middle_invariant invariant
  refine ⟨enabled.tensorComponent invariant step,
    enabled.tensor_previous_root invariant step orientation,
    enabled.tensor_component_previous invariant step orientation,
    enabled.waiting_payload_nodup invariant waitingLookup, ?_⟩
  intro conclusion conclusionMembership
  have middleWaitingLookup :
      (enabled.prepared invariant).after.stack.waiting[
          enabled.previousBoundary]? = some (.initialized payload) := by
    exact waitingLookup
  rcases middleInvariant.waiting_span_exact
      middleWaitingLookup conclusionMembership with
    ⟨linkIndex, left, right, olderPremise, youngerPremise,
      olderAge, youngerAge, youngerBoundary, linkLookup,
      sourceLookup, conclusionUnmarked, spanOrientation,
      olderMarked, youngerMarked, olderBoundary,
      youngerBoundaryLookup, boundaryOrder⟩
  have linkMembership : (.par left right conclusion : Link) ∈
      certificate.links :=
    List.mem_of_getElem? linkLookup
  have producerWellFormed :
      certificate.LinkWellFormed (.par left right conclusion) :=
    invariant.structural.2.2.2.2.1 _ linkMembership
  let producer : WaitingParProducer certificate conclusion := {
    linkIndex
    storedLeft := left
    storedRight := right
    source_eq := sourceLookup
    link_eq := linkLookup
    wellFormed := producerWellFormed }
  have conclusionWaiting : conclusion ∈
      (enabled.prepared invariant).after.stack.waitingVertices := by
    unfold SequentialStackState.waitingVertices
    apply List.mem_flatMap.mpr
    refine ⟨.initialized payload, ?_, ?_⟩
    · exact List.mem_of_getElem? (by simpa using middleWaitingLookup)
    · simpa [WaitingCell.vertices] using conclusionMembership
  have conclusionNotReady : conclusion ∉
      (enabled.prepared invariant).after.stack.ready.flatten := by
    have separated :=
      List.nodup_append.mp middleInvariant.queued_vertices_nodup
    intro readyMembership
    exact separated.2.2 conclusion readyMembership
      conclusion conclusionWaiting rfl
  have olderToken :
      (enabled.prepared invariant).coreMarked.tokenAt? olderPremise =
        some enabled.previousBoundary :=
    enabled.middle_token_of_boundary invariant olderMarked olderBoundary
  have youngerBoundaryActive :
      youngerBoundary = enabled.activeBoundary := by
    apply enabled.later_boundary_eq_active invariant
    · exact sigmaBoundary?_mem youngerBoundaryLookup
    · exact boundaryOrder
  have youngerToken :
      (enabled.prepared invariant).coreMarked.tokenAt? youngerPremise =
        some enabled.activeBoundary := by
    have token := enabled.middle_token_of_boundary invariant
      youngerMarked youngerBoundaryLookup
    simpa [youngerBoundaryActive] using token
  have olderReady := enabled.waiting_premise_ready_after_tensor
    invariant step orientation linkMembership conclusionUnmarked
    conclusionNotReady
    (premise := olderPremise) (boundary := enabled.previousBoundary)
    (by rcases spanOrientation with value | value <;>
      simp [value.1]) olderToken (Or.inl rfl)
  have youngerReady := enabled.waiting_premise_ready_after_tensor
    invariant step orientation linkMembership conclusionUnmarked
    conclusionNotReady
    (premise := youngerPremise) (boundary := enabled.activeBoundary)
    (by rcases spanOrientation with value | value <;>
      simp [value.2]) youngerToken (Or.inr rfl)
  have marksEq : coreTensor.marks =
      (enabled.prepared invariant).coreMarked.marks := by
    simpa using congrArg (fun state : UnificationState => state.marks)
      step.after_eq
  have conclusionUnmarkedAfter :
      coreTensor.marks[conclusion]? = some none := by
    rw [marksEq]
    exact conclusionUnmarked
  rcases spanOrientation with orientationLR | orientationRL
  · have leftEq : olderPremise = producer.storedLeft := by
      simpa [producer] using orientationLR.1
    have rightEq : youngerPremise = producer.storedRight := by
      simpa [producer] using orientationLR.2
    refine ⟨producer, conclusionUnmarkedAfter, ?_, ?_, ?_, ?_⟩
    · rw [← leftEq]
      exact olderReady.1
    · rw [← rightEq]
      exact youngerReady.1
    · rw [← leftEq]
      exact olderReady.2
    · rw [← rightEq]
      exact youngerReady.2
  · have leftEq : youngerPremise = producer.storedLeft := by
      simpa [producer] using orientationRL.2
    have rightEq : olderPremise = producer.storedRight := by
      simpa [producer] using orientationRL.1
    refine ⟨producer, conclusionUnmarkedAfter, ?_, ?_, ?_, ?_⟩
    · rw [← leftEq]
      exact youngerReady.1
    · rw [← rightEq]
      exact olderReady.1
    · rw [← leftEq]
      exact youngerReady.2
    · rw [← rightEq]
      exact olderReady.2

private theorem prepared_ready_two_levels
    {certificate : Certificate} {before : ReservationState}
    (enabled : UnifyPayloadInput certificate before)
    (invariant : SchedulerInvariant certificate before) :
    ∃ readyPrefix previousReady,
      (enabled.prepared invariant).after.stack.ready =
        readyPrefix ++ [previousReady, enabled.readyTail] := by
  rcases enabled.ready_two_levels invariant with
    ⟨readyPrefix, previousReady, readyEquation⟩
  refine ⟨readyPrefix, previousReady, ?_⟩
  change before.stack.ready.dropLast ++ [enabled.readyTail] =
    readyPrefix ++ [previousReady, enabled.readyTail]
  rw [readyEquation]
  simp [List.append_assoc]

private theorem tensor_tokens_eq_adjacent
    {certificate : Certificate} {before : ReservationState}
    (enabled : UnifyPayloadInput certificate before)
    (invariant : SchedulerInvariant certificate before)
    {coreTensor : UnificationState}
    (step : Certificate.QueueTensorStep
      (enabled.prepared invariant).coreMarked coreTensor
      enabled.consumer.storedLeft enabled.consumer.storedRight
      enabled.consumer.conclusion) :
    (enabled.consumer.side = .storedLeft ∧
        step.leftToken = (enabled.prepared invariant).stackResult.rawAge ∧
        step.rightToken = enabled.previousBoundary) ∨
      (enabled.consumer.side = .storedRight ∧
        step.leftToken = enabled.previousBoundary ∧
        step.rightToken =
          (enabled.prepared invariant).stackResult.rawAge) := by
  have guards := UnificationState.unifyTokens?_success step.token_guard
  cases sideEquation : enabled.consumer.side with
  | storedLeft =>
      left
      refine ⟨rfl, ?_, ?_⟩
      · have selectedEquation :
            enabled.vertex = enabled.consumer.storedLeft := by
          simpa [TensorBelow.premise, TensorPremiseSide.premise,
            sideEquation] using enabled.selected_eq_premise
        have selectedToken :
            (enabled.prepared invariant).coreMarked.tokenAt?
                enabled.consumer.storedLeft =
              some enabled.activeBoundary := by
          rw [← selectedEquation]
          exact enabled.selected_token invariant
        have tokenEquation : step.leftToken = enabled.activeBoundary :=
          Option.some.inj (guards.2.1.symm.trans selectedToken)
        simpa [prepared, stackResult] using tokenEquation
      · have mateEquation :
            enabled.consumer.mate = enabled.consumer.storedRight := by
          simp [TensorBelow.mate, TensorPremiseSide.mate, sideEquation]
        have mateToken :
            (enabled.prepared invariant).coreMarked.tokenAt?
                enabled.consumer.storedRight =
              some enabled.previousBoundary := by
          rw [← mateEquation]
          exact enabled.mate_token invariant
        exact Option.some.inj (guards.2.2.1.symm.trans mateToken)
  | storedRight =>
      right
      refine ⟨rfl, ?_, ?_⟩
      · have mateEquation :
            enabled.consumer.mate = enabled.consumer.storedLeft := by
          simp [TensorBelow.mate, TensorPremiseSide.mate, sideEquation]
        have mateToken :
            (enabled.prepared invariant).coreMarked.tokenAt?
                enabled.consumer.storedLeft =
              some enabled.previousBoundary := by
          rw [← mateEquation]
          exact enabled.mate_token invariant
        exact Option.some.inj (guards.2.1.symm.trans mateToken)
      · have selectedEquation :
            enabled.vertex = enabled.consumer.storedRight := by
          simpa [TensorBelow.premise, TensorPremiseSide.premise,
            sideEquation] using enabled.selected_eq_premise
        have selectedToken :
            (enabled.prepared invariant).coreMarked.tokenAt?
                enabled.consumer.storedRight =
              some enabled.activeBoundary := by
          rw [← selectedEquation]
          exact enabled.selected_token invariant
        have tokenEquation : step.rightToken = enabled.activeBoundary :=
          Option.some.inj (guards.2.2.1.symm.trans selectedToken)
        simpa [prepared, stackResult] using tokenEquation

private theorem unifyPayload?_exists_of_input
    {certificate : Certificate} {before : ReservationState}
    (invariant : SchedulerInvariant certificate before)
    (enabled : UnifyPayloadInput certificate before) :
    ∃ after,
      unifyPayload? certificate before invariant.toReservationInvariant =
        some after := by
  rcases enabled.waiting_payload_exists invariant with
    ⟨payload, waitingLookup⟩
  rcases enabled.tensor_queue_exists invariant with
    ⟨coreTensor, tensorStep, tokenOrientation, tensorEquation⟩
  have payloadReady := enabled.payload_ready_after_tensor invariant
    waitingLookup tensorStep tokenOrientation
  rcases activateWaitingPayload?_exists_of_readyAtRoot
      invariant.structural payloadReady with
    ⟨coreAfter, activationEquation⟩
  rcases activateWaitingPayload?_some_iff.mp activationEquation with
    ⟨activationFold⟩
  rcases enabled.prepared_ready_two_levels invariant with
    ⟨readyPrefix, previousReady, readyEquation⟩
  let stackAfter : SequentialStackState := {
    (enabled.prepared invariant).stackResult.after with
    sigma := enabled.sigmaPrefix ++ [enabled.previousBoundary]
    ready := readyPrefix ++
      [enabled.consumer.conclusion ::
        (payload ++ previousReady ++ enabled.readyTail)]
    waiting :=
      (enabled.prepared invariant).stackResult.after.waiting
        |>.setIfInBounds enabled.previousBoundary .undefined }
  let mergeStep : MergeTopReadyWaitingStep
      (enabled.prepared invariant).stackResult.after stackAfter
      enabled.previousBoundary enabled.consumer.conclusion := {
    sigmaPrefix := enabled.sigmaPrefix
    activeBoundary := enabled.activeBoundary
    readyPrefix
    previousReady
    activeReady := enabled.readyTail
    payload
    sigma_eq := by
      change before.stack.sigma =
        enabled.sigmaPrefix ++
          [enabled.previousBoundary, enabled.activeBoundary]
      exact enabled.sigma_two_levels
    ready_eq := by
      simpa [PreparedStep.after] using readyEquation
    waiting_initialized := by
      change before.stack.waiting[enabled.previousBoundary]? =
        some (.initialized payload)
      exact waitingLookup
    after_eq := rfl }
  have mergeEquation :
      (enabled.prepared invariant).stackResult.after.mergeTopReadyWaiting?
          enabled.previousBoundary enabled.consumer.conclusion =
        some stackAfter :=
    SequentialStackState.mergeTopReadyWaiting?_some_iff.mpr ⟨mergeStep⟩
  let merged : List Vertex :=
    enabled.consumer.conclusion ::
      (payload ++ previousReady ++ enabled.readyTail)
  have mergedEquation : stackAfter.ready.getLast? = some merged := by
    simp [stackAfter, merged]
  have targetQueueNodup :
      (enabled.consumer.conclusion ::
        (enabled.prepared invariant).stackResult.after.queuedVertices).Nodup := by
    apply List.nodup_cons.mpr
    constructor
    · simpa [PreparedStep.after] using
        enabled.conclusion_not_queued_middle invariant
    · change QueuedVerticesNodup (enabled.prepared invariant).after
      exact (enabled.middle_invariant invariant).queued_vertices_nodup
  have outputQueueNodup : stackAfter.queuedVertices.Nodup :=
    mergeStep.queuedVertices_perm.symm.nodup targetQueueNodup
  have outputReadyNodup : stackAfter.ready.flatten.Nodup := by
    unfold SequentialStackState.queuedVertices at outputQueueNodup
    exact (List.nodup_append.mp outputQueueNodup).1
  have readyShapeNodup :
      (readyPrefix.flatten ++ merged).Nodup := by
    simpa [stackAfter, merged] using outputReadyNodup
  have mergedNodup : merged.Nodup :=
    (List.nodup_append.mp readyShapeNodup).2.1
  have tokensAdjacent :=
    enabled.tensor_tokens_eq_adjacent invariant tensorStep
  let after : ReservationState := {
    stack := stackAfter
    core := coreAfter
    tags := before.tags }
  let witness : UnifyPayloadStep certificate before after := {
    before_invariant := invariant.toReservationInvariant
    prepared := enabled.prepared invariant
    consumer := enabled.consumer
    mateRawAge := enabled.mateRawAge
    previousBoundary := enabled.previousBoundary
    payload
    coreTensor
    coreAfter
    stackAfter
    merged
    tensorStep
    activationFold
    mergeStep
    prepare_eq := enabled.prepare_eq invariant
    consumer_eq := by
      simpa [prepared, stackResult] using enabled.consumer_eq
    mate_marked := enabled.prepared_mate_marked invariant
    lower := enabled.lower
    upper := by
      simpa [prepared, stackResult] using enabled.upper
    waiting_payload := by
      change before.stack.waiting[enabled.previousBoundary]? =
        some (.initialized payload)
      exact waitingLookup
    tensor_queue_eq := tensorEquation
    activation_fold_eq := activationEquation
    stack_merge_eq := mergeEquation
    merged_eq := mergedEquation
    ready_nodup := mergedNodup
    tokens_eq_adjacent := tokensAdjacent
    output_eq := rfl }
  refine ⟨after, (unifyPayload?_some_iff
    invariant.toReservationInvariant).mpr ?_⟩
  exact ⟨witness⟩

end UnifyPayloadInput

/-- The complete scheduler invariant discharges every hidden mutation guard
once the arbitrary-payload rule's read-only input conditions are enabled.

This is conditional applicability, not a progress theorem: it does not assert
that an arbitrary invariant state satisfies `UnifyPayloadEnabled`. -/
theorem unifyPayload?_exists_of_enabled
    {certificate : Certificate} {before : ReservationState}
    (invariant : SchedulerInvariant certificate before)
    (enabled : UnifyPayloadEnabled certificate before) :
    ∃ after,
      unifyPayload? certificate before invariant.toReservationInvariant =
        some after := by
  rcases enabled with ⟨input⟩
  exact input.unifyPayload?_exists_of_input invariant

/-- Enabled arbitrary-payload execution also returns a state satisfying the
complete occurrence-exact scheduler invariant. -/
theorem unifyPayload?_exists_schedulerInvariant_of_enabled
    {certificate : Certificate} {before : ReservationState}
    (invariant : SchedulerInvariant certificate before)
    (enabled : UnifyPayloadEnabled certificate before) :
    ∃ after,
      unifyPayload? certificate before invariant.toReservationInvariant =
          some after ∧
        SchedulerInvariant certificate after := by
  rcases unifyPayload?_exists_of_enabled invariant enabled with
    ⟨after, equation⟩
  exact ⟨after, equation,
    unifyPayload?_schedulerInvariant invariant equation⟩

end SequentialFigure7

end ProofNetIR
