import ProofNetIR.SequentialSchedulerInvariant
import ProofNetIR.SequentialFigure7UnifyPayload

namespace ProofNetIR

/-!
# Transient scheduler invariant for arbitrary-payload unification

The physical tensor and payload-fold intermediates of Figure 7 do not use the
post-drain scheduler stack.  Consequently they need not satisfy
`ComponentDomainExact`, `RealizesSigma`, or `ReadyBucketFrontierExact` against
their physical stacks.  This module instead reasons about the non-circular
shadow state consisting of the final post-drain stack, the current production
core, and the unchanged input tags.

At the shadow's surviving boundary, the ready bucket contains both the
raw-unmarked frontier already represented by the current core and the suffix of
the waiting payload that has not yet been activated.  The latter is the exact
transient gap.  Every activation consumes its head; an empty gap recovers the
ordinary `ReadyBucketFrontierExact` field and therefore the complete
`SchedulerInvariant`.
-/

namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge
open SequentialUnification

/-- All fields of `SchedulerInvariant` except the one intentionally broken by
the transient ready/payload gap.  In particular, this is substantially stronger
than `ReservationInvariant`: it retains occurrence-exact component provenance,
payload uniqueness/unmarkedness, causal production, waiting-span semantics,
pending-premise coverage, and the exact firing counter. -/
structure SchedulerInvariantExceptReady (certificate : Certificate)
    (state : ReservationState) : Prop
    extends ReservationInvariant certificate state where
  structural : certificate.StructurallyWellFormed
  component_domain_exact : ComponentDomainExact state
  component_forest_provenance :
    certificate.ComponentForestProvenance state.core
  live_frontiers_nodup : LiveFrontiersNodup state
  queued_vertices_nodup : QueuedVerticesNodup state
  queued_vertices_unmarked : QueuedVerticesUnmarked state
  produced_premises_marked : ProducedPremisesMarked certificate state
  waiting_span_exact : WaitingSpanExact certificate state
  pending_premises_covered_except_ready :
    PendingPremisesCoveredExceptReady certificate state
  fired_counter_exact : FiredCounterExact state

/-- Forget only the ordinary ready/frontier equality. -/
theorem SchedulerInvariant.withoutReady
    {certificate : Certificate} {state : ReservationState}
    (invariant : SchedulerInvariant certificate state) :
    SchedulerInvariantExceptReady certificate state := {
  toReservationInvariant := invariant.toReservationInvariant
  structural := invariant.structural
  component_domain_exact := invariant.component_domain_exact
  component_forest_provenance := invariant.component_forest_provenance
  live_frontiers_nodup := invariant.live_frontiers_nodup
  queued_vertices_nodup := invariant.queued_vertices_nodup
  queued_vertices_unmarked := invariant.queued_vertices_unmarked
  produced_premises_marked := invariant.produced_premises_marked
  waiting_span_exact := invariant.waiting_span_exact
  pending_premises_covered_except_ready :=
    invariant.pending_premises_covered_except_ready
  fired_counter_exact := invariant.fired_counter_exact }

/-- Extensional ready/frontier equality with one distinguished payload gap.

Every bucket other than `gapBoundary` is exactly its component's raw-unmarked
frontier.  At `gapBoundary`, the bucket additionally contains precisely the
remaining, not-yet-activated payload occurrences.  This is a set-level
statement, just like `ReadyBucketFrontierExact`; deterministic list order is a
separate executable refinement. -/
def ReadyBucketFrontierExactWithGap (state : ReservationState)
    (gapBoundary : RawTokenAge) (gap : List Vertex) : Prop :=
  ∀ {position boundary : Nat} {bucket : List Vertex},
    state.stack.sigma[position]? = some boundary →
    state.stack.ready[position]? = some bucket →
    ∃ component : UnificationComponent,
      state.core.components[boundary]? = some (some component) ∧
      ∀ vertex,
        vertex ∈ bucket ↔
          (vertex ∈ component.frontier ∧
            state.core.marks[vertex]? = some none) ∨
          (boundary = gapBoundary ∧ vertex ∈ gap)

/-- Non-circular shadow invariant for one suffix of an arbitrary waiting
payload.  Besides the sole ready/frontier gap, every ordinary scheduler field
already holds on the shadow state.  Remaining payload occurrences are pairwise
distinct, raw-unmarked, and absent from both raw marks and every live frontier;
the latter condition is what supplies exact occurrence freshness to the next
`queuePar` step. -/
structure UnifyPayloadGapInvariant (certificate : Certificate)
    (state : ReservationState) (gapBoundary : RawTokenAge)
    (gap : List Vertex) : Prop
    extends SchedulerInvariantExceptReady certificate state where
  gap_boundary_top : state.stack.sigma.getLast? = some gapBoundary
  ready_bucket_frontier_exact_with_gap :
    ReadyBucketFrontierExactWithGap state gapBoundary gap
  gap_nodup : gap.Nodup
  gap_unmarked :
    ∀ vertex ∈ gap, state.core.marks[vertex]? = some none
  gap_not_produced :
    ∀ vertex ∈ gap, ¬ Produced state vertex
  gap_premises_at_boundary :
    ∀ conclusion ∈ gap,
      ∃ linkIndex left right,
        certificate.links[linkIndex]? =
            some (.par left right conclusion) ∧
          (SequentialUnification.sourceIndex certificate)[conclusion]? =
            some [{
              linkIndex := linkIndex
              link := .par left right conclusion }] ∧
          state.core.tokenAt? left = some gapBoundary ∧
          state.core.tokenAt? right = some gapBoundary

namespace UnifyPayloadGapInvariant

/-- Once the transient payload suffix is empty, the gap relation reduces
definitionally to ordinary ready/frontier exactness and all retained fields
reassemble into `SchedulerInvariant`. -/
theorem close
    {certificate : Certificate} {state : ReservationState}
    {gapBoundary : RawTokenAge}
    (invariant :
      UnifyPayloadGapInvariant certificate state gapBoundary []) :
    SchedulerInvariant certificate state := by
  have readyExact : ReadyBucketFrontierExact state := by
    intro position boundary bucket sigmaLookup readyLookup
    rcases invariant.ready_bucket_frontier_exact_with_gap
        sigmaLookup readyLookup with
      ⟨component, componentLookup, exactMembership⟩
    refine ⟨component, componentLookup, ?_⟩
    intro vertex
    simpa using exactMembership vertex
  exact {
    toReservationInvariant := invariant.toReservationInvariant
    structural := invariant.structural
    component_domain_exact := invariant.component_domain_exact
    component_forest_provenance := invariant.component_forest_provenance
    live_frontiers_nodup := invariant.live_frontiers_nodup
    ready_bucket_frontier_exact := readyExact
    queued_vertices_nodup := invariant.queued_vertices_nodup
    queued_vertices_unmarked := invariant.queued_vertices_unmarked
    produced_premises_marked := invariant.produced_premises_marked
    waiting_span_exact := invariant.waiting_span_exact
    pending_premises_covered_except_ready :=
      invariant.pending_premises_covered_except_ready
    fired_counter_exact := invariant.fired_counter_exact }

private theorem readyMemLiveFrontier
    {certificate : Certificate} {state : ReservationState}
    (invariant : SchedulerInvariant certificate state)
    {vertex : Vertex} (membership : vertex ∈ state.stack.ready.flatten) :
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

/-- A remaining gap occurrence is fresh for every exact live-component owner.
This is the point at which full scheduler provenance, rather than only the
reservation layer, enters arbitrary-payload unification. -/
private theorem occurrenceFresh
    {certificate : Certificate} {state : ReservationState}
    {gapBoundary : RawTokenAge} {gap : List Vertex}
    (invariant :
      UnifyPayloadGapInvariant certificate state gapBoundary gap)
    {vertex : Vertex} (vertexGap : vertex ∈ gap) :
    ∀ {index component owned},
      state.core.components[index]? = some (some component) →
      Certificate.OwnedOccurrenceAccounted
        state.core index component owned →
      vertex ∉ owned := by
  intro index component owned componentLookup accounted vertexOwned
  apply invariant.gap_not_produced vertex vertexGap
  rcases accounted vertex vertexOwned with
    ⟨rawAge, marked, _representative⟩ | ⟨_unmarked, frontier⟩
  · exact Or.inl ⟨rawAge, marked⟩
  · apply Or.inr
    unfold UnificationState.liveFrontierVertices
    apply List.mem_flatMap.mpr
    refine ⟨some component, ?_, ?_⟩
    · exact List.mem_of_getElem? (by
        rw [Array.getElem?_toList]
        exact componentLookup)
    · simpa using frontier

/-- The distinguished gap boundary is an actual live sigma boundary. -/
private theorem gapBoundary_mem
    {certificate : Certificate} {state : ReservationState}
    {gapBoundary : RawTokenAge} {gap : List Vertex}
    (invariant :
      UnifyPayloadGapInvariant certificate state gapBoundary gap) :
    gapBoundary ∈ state.stack.sigma :=
  List.mem_of_getLast? invariant.gap_boundary_top

/-- Every remaining gap occurrence is physically present in the unique ready
bucket aligned with the distinguished top boundary. -/
private theorem gap_mem_ready
    {certificate : Certificate} {state : ReservationState}
    {gapBoundary : RawTokenAge} {gap : List Vertex}
    (invariant : UnifyPayloadGapInvariant certificate state gapBoundary gap)
    {vertex : Vertex} (vertexGap : vertex ∈ gap) :
    vertex ∈ state.stack.ready.flatten := by
  rcases List.mem_iff_getElem.mp invariant.gapBoundary_mem with
    ⟨position, positionBound, positionEquation⟩
  have sigmaLookup : state.stack.sigma[position]? = some gapBoundary := by
    rw [List.getElem?_eq_getElem positionBound, positionEquation]
  have readyBound : position < state.stack.ready.length := by
    rw [invariant.stack_wellShaped.ready_aligned]
    exact positionBound
  let bucket := state.stack.ready[position]
  have readyLookup : state.stack.ready[position]? = some bucket :=
    List.getElem?_eq_getElem readyBound
  rcases invariant.ready_bucket_frontier_exact_with_gap
      sigmaLookup readyLookup with
    ⟨component, componentLookup, exactMembership⟩
  apply List.mem_flatten.mpr
  refine ⟨bucket, List.mem_of_getElem? readyLookup, ?_⟩
  exact (exactMembership vertex).mpr (Or.inr ⟨rfl, vertexGap⟩)

/-- The executable activation of the gap head is forced to use the surviving
top boundary.  Exact singleton source provenance identifies the executable
producer with the producer retained by the gap, while the two token queries
identify the runtime output token. -/
private theorem headOutput_eq_gapBoundary
    {certificate : Certificate} {state : ReservationState}
    {gapBoundary : RawTokenAge} {conclusion : Vertex}
    {payload : List Vertex} {afterCore : UnificationState}
    (invariant : UnifyPayloadGapInvariant certificate state gapBoundary
      (conclusion :: payload))
    (step : WaitingParActivationStep certificate state.core afterCore conclusion) :
    step.queueStep.outputToken = gapBoundary := by
  rcases invariant.gap_premises_at_boundary conclusion (by simp) with
    ⟨linkIndex, left, right, linkLookup, sourceLookup,
      leftToken, rightToken⟩
  have incidenceEq := Option.some.inj
    (sourceLookup.symm.trans step.producer.source_eq)
  have singletonEq := List.singleton_inj.mp incidenceEq
  have linkEq := congrArg SequentialUnification.SourceIncidence.link singletonEq
  injection linkEq with leftEq rightEq
  subst left
  subst right
  have guards := UnificationState.forwardToken?_success
    step.queueStep.token_guard
  exact Option.some.inj (guards.2.1.symm.trans leftToken)

/-- The forced output boundary is a production root before activation. -/
private theorem headOutput_root
    {certificate : Certificate} {state : ReservationState}
    {gapBoundary : RawTokenAge} {conclusion : Vertex}
    {payload : List Vertex} {afterCore : UnificationState}
    (invariant : UnifyPayloadGapInvariant certificate state gapBoundary
      (conclusion :: payload))
    (step : WaitingParActivationStep certificate state.core afterCore conclusion) :
    state.core.representative step.queueStep.outputToken =
      step.queueStep.outputToken :=
  invariant.core_abstractable.tokenAt?_root
    (UnificationState.forwardToken?_success step.queueStep.token_guard).2.1

/-- Occurrence-exact provenance preservation for the next activation at a
known root.  The conclusion freshness obligation is discharged from the real
transient gap, rather than postulated independently. -/
private theorem queueParComponentForest
    {certificate : Certificate} {state : ReservationState}
    {gapBoundary : RawTokenAge} {conclusion : Vertex}
    {payload : List Vertex} {afterCore : UnificationState}
    (invariant : UnifyPayloadGapInvariant certificate state gapBoundary
      (conclusion :: payload))
    (step : WaitingParActivationStep certificate state.core afterCore conclusion) :
    certificate.ComponentForestProvenance afterCore := by
  exact invariant.component_forest_provenance.queueParStep_of_root_fresh
    step.queueStep (invariant.headOutput_root step)
    step.producer.linkIndex step.submitted_par
    (invariant.occurrenceFresh (by simp))

/-- A waiting-par activation changes neither raw marks nor representatives, so
all token queries are definitionally transported through the step. -/
private theorem queueParTokenAt_eq
    {certificate : Certificate} {state : ReservationState}
    {conclusion vertex : Vertex} {afterCore : UnificationState}
    (step : WaitingParActivationStep certificate state.core afterCore conclusion) :
    afterCore.tokenAt? vertex = state.core.tokenAt? vertex := by
  unfold UnificationState.tokenAt?
  rw [step.exact.2.1]
  cases state.core.marks[vertex]? with
  | none => rfl
  | some assigned =>
      cases assigned with
      | none => rfl
      | some rawAge =>
          change some (afterCore.representative rawAge) =
            some (state.core.representative rawAge)
          unfold UnificationState.representative
          rw [step.exact.2.2.1]

/-- A single activation can add observable production evidence only for its
exact submitted conclusion.  Every retained context occurrence comes from the
old active component, and every other raw component slot is unchanged. -/
private theorem queueParProduced_cases
    {certificate : Certificate} {state : ReservationState}
    {gapBoundary : RawTokenAge} {conclusion : Vertex}
    {payload : List Vertex} {afterCore : UnificationState}
    (invariant : UnifyPayloadGapInvariant certificate state gapBoundary
      (conclusion :: payload))
    (step : WaitingParActivationStep certificate state.core afterCore conclusion)
    {vertex : Vertex}
    (produced : Produced { state with core := afterCore } vertex) :
    vertex = conclusion ∨ Produced state vertex := by
  have marksEq : afterCore.marks = state.core.marks := step.exact.2.1
  have componentsEq : afterCore.components =
      state.core.components.setIfInBounds step.queueStep.outputToken
        (some {
          tree := .par step.queueStep.leftFocus step.queueStep.rightFocus
            step.queueStep.component.tree
          frontier := step.queueStep.context ++ [conclusion] }) :=
    step.exact.1
  have root := invariant.headOutput_root step
  have activeRaw :
      state.core.components[step.queueStep.outputToken]? =
        some (some step.queueStep.component) := by
    have raw := UnificationState.componentAt?_some_raw
      step.queueStep.component_lookup
    simpa [root] using raw
  have activeBound : step.queueStep.outputToken < state.core.components.size :=
    (Array.getElem?_eq_some_iff.mp activeRaw).1
  rcases produced with ⟨rawAge, marked⟩ | frontierMembership
  · apply Or.inr
    apply Or.inl
    refine ⟨rawAge, ?_⟩
    change afterCore.marks[vertex]? = some (some rawAge) at marked
    rw [marksEq] at marked
    exact marked
  · change vertex ∈ afterCore.liveFrontierVertices at frontierMembership
    unfold UnificationState.liveFrontierVertices at frontierMembership
    rcases List.mem_flatMap.mp frontierMembership with
      ⟨cell, cellMembership, vertexFrontier⟩
    cases cell with
    | none => simp at vertexFrontier
    | some component =>
        simp only [Option.map_some, Option.getD_some] at vertexFrontier
        rcases List.mem_iff_getElem.mp cellMembership with
          ⟨index, indexBound, indexEquation⟩
        have afterLookup :
            afterCore.components[index]? = some (some component) := by
          rw [← Array.getElem?_toList]
          rw [List.getElem?_eq_getElem indexBound, indexEquation]
        by_cases active : index = step.queueStep.outputToken
        · subst index
          rw [componentsEq] at afterLookup
          simp [activeBound] at afterLookup
          subst component
          rw [List.mem_append] at vertexFrontier
          rcases vertexFrontier with contextMembership | conclusionMembership
          · apply Or.inr
            apply Or.inr
            unfold UnificationState.liveFrontierVertices
            apply List.mem_flatMap.mpr
            refine ⟨some step.queueStep.component, ?_, ?_⟩
            · exact List.mem_of_getElem? (by
                rw [Array.getElem?_toList]
                exact activeRaw)
            · have inAfterLeft : vertex ∈ step.queueStep.afterLeft :=
                (CutFreeDerivation.pick?_perm
                  step.queueStep.right_pick.positional).mem_iff.mpr (by
                    simp [contextMembership])
              exact (CutFreeDerivation.pick?_perm
                step.queueStep.left_pick.positional).mem_iff.mpr (by
                  simp [inAfterLeft])
          · exact Or.inl (by simpa using conclusionMembership)
        · apply Or.inr
          apply Or.inr
          unfold UnificationState.liveFrontierVertices
          apply List.mem_flatMap.mpr
          refine ⟨some component, ?_, by simpa using vertexFrontier⟩
          have oldLookup :
              state.core.components[index]? = some (some component) := by
            rw [componentsEq] at afterLookup
            simpa [Array.getElem?_setIfInBounds, Ne.symm active] using
              afterLookup
          exact List.mem_of_getElem? (by
            rw [Array.getElem?_toList]
            exact oldLookup)

/-- Consuming the gap head preserves non-production of the exact tail.  The
`head ≠ tail` fact comes from the stored payload's global `Nodup`; raw
unmarkedness alone would not justify this theorem. -/
private theorem tailNotProduced
    {certificate : Certificate} {state : ReservationState}
    {gapBoundary : RawTokenAge} {conclusion : Vertex}
    {payload : List Vertex} {afterCore : UnificationState}
    (invariant : UnifyPayloadGapInvariant certificate state gapBoundary
      (conclusion :: payload))
    (step : WaitingParActivationStep certificate state.core afterCore conclusion) :
    ∀ vertex ∈ payload,
      ¬ Produced { state with core := afterCore } vertex := by
  intro vertex vertexPayload producedAfter
  rcases invariant.queueParProduced_cases step producedAfter with
    same | producedBefore
  · subst vertex
    exact (List.nodup_cons.mp invariant.gap_nodup).1 vertexPayload
  · exact invariant.gap_not_produced vertex (by simp [vertexPayload])
      producedBefore

/-- The exact token/span payload facts transport to the tail because a par
activation changes neither marks nor parents. -/
private theorem tailPremisesAtBoundary
    {certificate : Certificate} {state : ReservationState}
    {gapBoundary : RawTokenAge} {conclusion : Vertex}
    {payload : List Vertex} {afterCore : UnificationState}
    (invariant : UnifyPayloadGapInvariant certificate state gapBoundary
      (conclusion :: payload))
    (step : WaitingParActivationStep certificate state.core afterCore conclusion) :
    ∀ tailConclusion ∈ payload,
      ∃ linkIndex left right,
        certificate.links[linkIndex]? =
            some (.par left right tailConclusion) ∧
          (SequentialUnification.sourceIndex certificate)[tailConclusion]? =
            some [{
              linkIndex := linkIndex
              link := .par left right tailConclusion }] ∧
          afterCore.tokenAt? left = some gapBoundary ∧
          afterCore.tokenAt? right = some gapBoundary := by
  intro tailConclusion tailMembership
  rcases invariant.gap_premises_at_boundary tailConclusion
      (by simp [tailMembership]) with
    ⟨linkIndex, left, right, linkLookup, sourceLookup,
      leftToken, rightToken⟩
  exact ⟨linkIndex, left, right, linkLookup, sourceLookup,
    (queueParTokenAt_eq step).trans leftToken,
    (queueParTokenAt_eq step).trans rightToken⟩

/-- The fixed-stack shadow keeps the complete reservation layer through one
payload activation. -/
private theorem queueParReservationInvariant
    {certificate : Certificate} {state : ReservationState}
    {gapBoundary : RawTokenAge} {conclusion : Vertex}
    {payload : List Vertex} {afterCore : UnificationState}
    (invariant : UnifyPayloadGapInvariant certificate state gapBoundary
      (conclusion :: payload))
    (step : WaitingParActivationStep certificate state.core afterCore conclusion) :
    ReservationInvariant certificate { state with core := afterCore } := by
  have alignment := Certificate.queuePar?_reservationAlignment
    invariant.core_carriers_aligned invariant.core_counter_aligned step.queue_eq
  exact {
    stack_wellShaped := invariant.stack_wellShaped
    stack_operationalWaitingDomain := invariant.stack_operationalWaitingDomain
    realizesSigma := {
      marks_eq := step.exact.2.1.trans invariant.realizesSigma.marks_eq
      horizon_eq := by
        rw [step.exact.2.2.1]
        exact invariant.realizesSigma.horizon_eq
      representative_eq_boundary := by
        intro age ageBound
        have oldBound : age < state.stack.nextAge := by simpa using ageBound
        calc
          sigmaBoundary? state.stack.sigma age =
              some (state.core.representative age) :=
            invariant.realizesSigma.representative_eq_boundary oldBound
          _ = some (afterCore.representative age) := by
            unfold UnificationState.representative
            rw [step.exact.2.2.1] }
    core_orderedParents :=
      Certificate.queuePar?_orderedParents invariant.core_orderedParents
        step.queue_eq
    core_abstractable :=
      Certificate.queuePar?_abstractable invariant.core_abstractable
        step.queue_eq
    core_componentsFormulaConsistent :=
      Certificate.queuePar?_componentsFormulaConsistent
        invariant.core_componentsFormulaConsistent step.producer.wellFormed
        step.queue_eq
    core_carriers_aligned := alignment.1
    core_counter_aligned := alignment.2
    tags_size := invariant.tags_size }

/-- Updating the surviving component in place preserves the exact equivalence
between live raw slots and final sigma boundaries. -/
private theorem queueParComponentDomainExact
    {certificate : Certificate} {state : ReservationState}
    {gapBoundary : RawTokenAge} {conclusion : Vertex}
    {payload : List Vertex} {afterCore : UnificationState}
    (invariant : UnifyPayloadGapInvariant certificate state gapBoundary
      (conclusion :: payload))
    (step : WaitingParActivationStep certificate state.core afterCore conclusion) :
    ComponentDomainExact { state with core := afterCore } := by
  have outputEq := invariant.headOutput_eq_gapBoundary step
  have root := invariant.headOutput_root step
  have rawLookup :
      state.core.components[step.queueStep.outputToken]? =
        some (some step.queueStep.component) := by
    have lookup := UnificationState.componentAt?_some_raw
      step.queueStep.component_lookup
    simpa [root] using lookup
  have outputBound : step.queueStep.outputToken < state.core.components.size :=
    (Array.getElem?_eq_some_iff.mp rawLookup).1
  let nextComponent : UnificationComponent := {
    tree := .par step.queueStep.leftFocus step.queueStep.rightFocus
      step.queueStep.component.tree
    frontier := step.queueStep.context ++ [conclusion] }
  intro token
  change (∃ component,
      afterCore.components[token]? = some (some component)) ↔
    token ∈ state.stack.sigma
  rw [step.exact.1]
  by_cases active : token = step.queueStep.outputToken
  · subst token
    constructor
    · intro _
      rw [outputEq]
      exact invariant.gapBoundary_mem
    · intro _
      exact ⟨nextComponent, by
        simp [nextComponent, outputBound]⟩
  · rw [Array.getElem?_setIfInBounds_ne (Ne.symm active)]
    exact invariant.component_domain_exact token

/-- Occurrence-exact forest preservation immediately supplies global
duplicate-freedom of all live frontiers in the next shadow. -/
private theorem queueParLiveFrontiersNodup
    {certificate : Certificate} {state : ReservationState}
    {gapBoundary : RawTokenAge} {conclusion : Vertex}
    {payload : List Vertex} {afterCore : UnificationState}
    (invariant : UnifyPayloadGapInvariant certificate state gapBoundary
      (conclusion :: payload))
    (step : WaitingParActivationStep certificate state.core afterCore conclusion) :
    LiveFrontiersNodup { state with core := afterCore } := by
  unfold LiveFrontiersNodup
  simpa [UnificationState.liveFrontierVertices] using
    (invariant.queueParComponentForest step).liveFrontiers_nodup

/-- The shadow stack is fixed, so queued-occurrence uniqueness is unchanged. -/
private theorem queueParQueuedVerticesNodup
    {certificate : Certificate} {state : ReservationState}
    {gapBoundary : RawTokenAge} {conclusion : Vertex}
    {payload : List Vertex} {afterCore : UnificationState}
    (invariant : UnifyPayloadGapInvariant certificate state gapBoundary
      (conclusion :: payload))
    (_step : WaitingParActivationStep certificate state.core afterCore conclusion) :
    QueuedVerticesNodup { state with core := afterCore } :=
  invariant.queued_vertices_nodup

/-- The shadow stack is fixed and activation preserves marks, so every queued
occurrence remains raw-unmarked. -/
private theorem queueParQueuedVerticesUnmarked
    {certificate : Certificate} {state : ReservationState}
    {gapBoundary : RawTokenAge} {conclusion : Vertex}
    {payload : List Vertex} {afterCore : UnificationState}
    (invariant : UnifyPayloadGapInvariant certificate state gapBoundary
      (conclusion :: payload))
    (step : WaitingParActivationStep certificate state.core afterCore conclusion) :
    QueuedVerticesUnmarked { state with core := afterCore } := by
  intro vertex membership
  change afterCore.marks[vertex]? = some none
  rw [step.exact.2.1]
  exact invariant.queued_vertices_unmarked vertex membership

/-- Waiting cells and sigma are fixed in the shadow, and activation preserves
marks, hence every still-stored waiting span remains exact. -/
private theorem queueParWaitingSpanExact
    {certificate : Certificate} {state : ReservationState}
    {gapBoundary : RawTokenAge} {conclusion : Vertex}
    {payload : List Vertex} {afterCore : UnificationState}
    (invariant : UnifyPayloadGapInvariant certificate state gapBoundary
      (conclusion :: payload))
    (step : WaitingParActivationStep certificate state.core afterCore conclusion) :
    WaitingSpanExact certificate { state with core := afterCore } := by
  intro boundary waitingPayload waitingConclusion waitingLookup
    waitingMembership
  rcases invariant.waiting_span_exact waitingLookup waitingMembership with
    ⟨linkIndex, left, right, olderPremise, youngerPremise,
      olderAge, youngerAge, youngerBoundary, linkLookup,
      sourceLookup, conclusionUnmarked, orientation,
      olderMarked, youngerMarked, olderBoundary,
      youngerBoundaryLookup, boundaryOrder⟩
  refine ⟨linkIndex, left, right, olderPremise, youngerPremise,
    olderAge, youngerAge, youngerBoundary, linkLookup,
    sourceLookup, ?_, orientation, ?_, ?_, olderBoundary,
    youngerBoundaryLookup, boundaryOrder⟩
  · change afterCore.marks[waitingConclusion]? = some none
    rw [step.exact.2.1]
    exact conclusionUnmarked
  · change afterCore.marks[olderPremise]? = some (some olderAge)
    rw [step.exact.2.1]
    exact olderMarked
  · change afterCore.marks[youngerPremise]? = some (some youngerAge)
    rw [step.exact.2.1]
    exact youngerMarked

/-- The activated par's exact premises have concrete raw marks in the next
shadow, as witnessed by its successful token queries. -/
private theorem queueParPremisesMarked
    {certificate : Certificate} {state : ReservationState}
    {conclusion : Vertex} {afterCore : UnificationState}
    (step : WaitingParActivationStep certificate state.core afterCore conclusion) :
    (∃ leftAge,
      afterCore.marks[step.producer.storedLeft]? = some (some leftAge)) ∧
      ∃ rightAge,
        afterCore.marks[step.producer.storedRight]? = some (some rightAge) := by
  have guards := UnificationState.forwardToken?_success
    step.queueStep.token_guard
  rcases state.core.tokenAt?_some_witness guards.2.1 with
    ⟨leftAge, leftAssigned, _leftRepresentative⟩
  rcases state.core.tokenAt?_some_witness guards.2.2 with
    ⟨rightAge, rightAssigned, _rightRepresentative⟩
  constructor
  · refine ⟨leftAge, ?_⟩
    rw [step.exact.2.1]
    exact UnificationState.assignedToken?_some_raw leftAssigned
  · refine ⟨rightAge, ?_⟩
    rw [step.exact.2.1]
    exact UnificationState.assignedToken?_some_raw rightAssigned

/-- Causal production is preserved: newly observable production can only be
the exact activated par, whose two premises are marked; all older cases use the
old causal field and unchanged marks. -/
private theorem queueParProducedPremisesMarked
    {certificate : Certificate} {state : ReservationState}
    {gapBoundary : RawTokenAge} {conclusion : Vertex}
    {payload : List Vertex} {afterCore : UnificationState}
    (invariant : UnifyPayloadGapInvariant certificate state gapBoundary
      (conclusion :: payload))
    (step : WaitingParActivationStep certificate state.core afterCore conclusion) :
    ProducedPremisesMarked certificate { state with core := afterCore } := by
  intro link linkMembership
  cases link with
  | «axiom» left right => trivial
  | «par» left right producedConclusion
  | tensor left right producedConclusion =>
      intro producedAfter
      rcases invariant.queueParProduced_cases step producedAfter with
        conclusionEq | producedBefore
      · subst producedConclusion
        have currentMembership :
            (.par step.producer.storedLeft step.producer.storedRight
              conclusion : Link) ∈ certificate.links :=
          List.mem_of_getElem? step.submitted_par
        have producerEq :=
          UnificationState.StructurallyWellFormed.producerLink_unique
            invariant.structural (conclusion := conclusion)
            linkMembership (by simp [Link.produces])
            currentMembership (by simp [Link.produces])
        cases producerEq <;> exact queueParPremisesMarked step
      · rcases invariant.produced_premises_marked
            linkMembership producedBefore with
          ⟨⟨leftAge, leftMarked⟩, rightAge, rightMarked⟩
        refine ⟨⟨leftAge, ?_⟩, rightAge, ?_⟩
        · change afterCore.marks[left]? = some (some leftAge)
          rw [step.exact.2.1]
          exact leftMarked
        · change afterCore.marks[right]? = some (some rightAge)
          rw [step.exact.2.1]
          exact rightMarked

/-- Pending-premise coverage survives one gap activation.  If an old covered
premise lies outside the updated root, its live component is unchanged.  At the
updated root, every premise other than the two consumed occurrences survives
the exact positional picks into the new context.  If the pending premise is one
of those consumed occurrences, structural parent-link uniqueness identifies
its connective with the activated par, whose conclusion is already in the gap
ready bucket, contradicting the pending hypothesis. -/
private theorem queueParPendingPremisesCoveredExceptReady
    {certificate : Certificate} {state : ReservationState}
    {gapBoundary : RawTokenAge} {activatedConclusion : Vertex}
    {payload : List Vertex} {afterCore : UnificationState}
    (invariant : UnifyPayloadGapInvariant certificate state gapBoundary
      (activatedConclusion :: payload))
    (step : WaitingParActivationStep certificate state.core afterCore
      activatedConclusion) :
    PendingPremisesCoveredExceptReady certificate
      { state with core := afterCore } := by
  have marksEq : afterCore.marks = state.core.marks := step.exact.2.1
  have parentsEq : afterCore.parents = state.core.parents := step.exact.2.2.1
  have outputEq := invariant.headOutput_eq_gapBoundary step
  have outputRoot := invariant.headOutput_root step
  have activeRaw :
      state.core.components[step.queueStep.outputToken]? =
        some (some step.queueStep.component) := by
    have raw := UnificationState.componentAt?_some_raw
      step.queueStep.component_lookup
    simpa [outputRoot] using raw
  have outputBound : step.queueStep.outputToken < state.core.components.size :=
    (Array.getElem?_eq_some_iff.mp activeRaw).1
  let nextComponent : UnificationComponent := {
    tree := .par step.queueStep.leftFocus step.queueStep.rightFocus
      step.queueStep.component.tree
    frontier := step.queueStep.context ++ [activatedConclusion] }
  have componentsEq : afterCore.components =
      state.core.components.setIfInBounds step.queueStep.outputToken
        (some nextComponent) := by
    simpa [nextComponent] using step.exact.1
  intro link linkMembership
  cases link with
  | «axiom» left right => trivial
  | «par» left right pendingConclusion
  | tensor left right pendingConclusion =>
      intro conclusionUnmarked conclusionNotReady premise token
        premiseMembership tokenAfter
      have conclusionUnmarkedBefore :
          state.core.marks[pendingConclusion]? = some none := by
        change afterCore.marks[pendingConclusion]? = some none
          at conclusionUnmarked
        rw [marksEq] at conclusionUnmarked
        exact conclusionUnmarked
      have tokenBefore : state.core.tokenAt? premise = some token := by
        have transported := queueParTokenAt_eq step (vertex := premise)
        exact transported.symm.trans tokenAfter
      have oldRoot : state.core.representative token = token :=
        invariant.core_abstractable.tokenAt?_root tokenBefore
      have premiseNeLeft : premise ≠ step.producer.storedLeft := by
        intro same
        subst premise
        have sameLink :=
          UnificationState.StructurallyWellFormed.parentLink_unique
            invariant.structural
            (premise := step.producer.storedLeft)
            (first := .par step.producer.storedLeft
              step.producer.storedRight activatedConclusion)
            (List.mem_of_getElem? step.submitted_par)
            (by simp [Link.premises]) linkMembership
            (by simpa [Link.premises] using premiseMembership)
        have activatedReady :
            activatedConclusion ∈ state.stack.ready.flatten :=
          invariant.gap_mem_ready (by simp)
        cases sameLink <;> exact conclusionNotReady activatedReady
      have premiseNeRight : premise ≠ step.producer.storedRight := by
        intro same
        subst premise
        have sameLink :=
          UnificationState.StructurallyWellFormed.parentLink_unique
            invariant.structural
            (premise := step.producer.storedRight)
            (first := .par step.producer.storedLeft
              step.producer.storedRight activatedConclusion)
            (List.mem_of_getElem? step.submitted_par)
            (by simp [Link.premises]) linkMembership
            (by simpa [Link.premises] using premiseMembership)
        have activatedReady :
            activatedConclusion ∈ state.stack.ready.flatten :=
          invariant.gap_mem_ready (by simp)
        cases sameLink <;> exact conclusionNotReady activatedReady
      rcases invariant.pending_premises_covered_except_ready
          linkMembership conclusionUnmarkedBefore conclusionNotReady
          premiseMembership tokenBefore with
        ⟨oldComponent, oldComponentLookup, oldFrontier⟩
      have oldRaw : state.core.components[token]? =
          some (some oldComponent) := by
        have raw := UnificationState.componentAt?_some_raw oldComponentLookup
        simpa [oldRoot] using raw
      by_cases active : token = step.queueStep.outputToken
      · subst token
        have componentEq : oldComponent = step.queueStep.component :=
          Option.some.inj (Option.some.inj (oldRaw.symm.trans activeRaw))
        subst oldComponent
        have afterLeft : premise ∈ step.queueStep.afterLeft :=
          Certificate.FirstOccurrencePick.mem_remaining_of_ne
            step.queueStep.left_pick premiseNeLeft oldFrontier
        have inContext : premise ∈ step.queueStep.context :=
          Certificate.FirstOccurrencePick.mem_remaining_of_ne
            step.queueStep.right_pick premiseNeRight afterLeft
        refine ⟨nextComponent, ?_, by simp [nextComponent, inContext]⟩
        have afterOutputRoot :
            afterCore.representative step.queueStep.outputToken =
              step.queueStep.outputToken := by
          unfold UnificationState.representative
          rw [parentsEq]
          exact outputRoot
        unfold UnificationState.componentAt?
        rw [afterOutputRoot, componentsEq]
        simp [outputBound]
      · refine ⟨oldComponent, ?_, oldFrontier⟩
        have afterRoot : afterCore.representative token = token := by
          unfold UnificationState.representative
          rw [parentsEq]
          exact oldRoot
        unfold UnificationState.componentAt?
        rw [afterRoot, componentsEq,
          Array.getElem?_setIfInBounds_ne (Ne.symm active)]
        simp [oldRaw]

/-- One activation closes exactly the head of the ready/frontier gap.  The
ready stack is unchanged.  At the distinguished top bucket, the activated head
moves from the exceptional payload disjunct into the new component frontier;
all other buckets retain ordinary exactness. -/
private theorem queueParReadyBucketFrontierExactWithGap
    {certificate : Certificate} {state : ReservationState}
    {gapBoundary : RawTokenAge} {conclusion : Vertex}
    {payload : List Vertex} {afterCore : UnificationState}
    (invariant : UnifyPayloadGapInvariant certificate state gapBoundary
      (conclusion :: payload))
    (step : WaitingParActivationStep certificate state.core afterCore conclusion) :
    ReadyBucketFrontierExactWithGap { state with core := afterCore }
      gapBoundary payload := by
  have outputEq := invariant.headOutput_eq_gapBoundary step
  have root := invariant.headOutput_root step
  have oldRaw :
      state.core.components[gapBoundary]? =
        some (some step.queueStep.component) := by
    have raw := UnificationState.componentAt?_some_raw
      step.queueStep.component_lookup
    rw [root, outputEq] at raw
    exact raw
  have outputBound : gapBoundary < state.core.components.size :=
    (Array.getElem?_eq_some_iff.mp oldRaw).1
  let nextComponent : UnificationComponent := {
    tree := .par step.queueStep.leftFocus step.queueStep.rightFocus
      step.queueStep.component.tree
    frontier := step.queueStep.context ++ [conclusion] }
  have componentsEq : afterCore.components =
      state.core.components.setIfInBounds gapBoundary
        (some nextComponent) := by
    simpa [outputEq, nextComponent] using step.exact.1
  have marksEq : afterCore.marks = state.core.marks := step.exact.2.1
  have guards := UnificationState.forwardToken?_success
    step.queueStep.token_guard
  have context_of_frontier_unmarked :
      ∀ {vertex}, vertex ∈ step.queueStep.component.frontier →
        state.core.marks[vertex]? = some none →
        vertex ∈ step.queueStep.context := by
    intro vertex frontier unmarked
    have vertexNeLeft : vertex ≠ step.producer.storedLeft := by
      intro same
      subst vertex
      unfold UnificationState.tokenAt? at guards
      rw [unmarked] at guards
      simp at guards
    have vertexNeRight : vertex ≠ step.producer.storedRight := by
      intro same
      subst vertex
      unfold UnificationState.tokenAt? at guards
      rw [unmarked] at guards
      simp at guards
    have afterLeft := Certificate.FirstOccurrencePick.mem_remaining_of_ne
      step.queueStep.left_pick vertexNeLeft frontier
    exact Certificate.FirstOccurrencePick.mem_remaining_of_ne
      step.queueStep.right_pick vertexNeRight afterLeft
  have frontier_of_context :
      ∀ {vertex}, vertex ∈ step.queueStep.context →
        vertex ∈ step.queueStep.component.frontier := by
    intro vertex contextMembership
    have afterLeft : vertex ∈ step.queueStep.afterLeft :=
      (CutFreeDerivation.pick?_perm
        step.queueStep.right_pick.positional).mem_iff.mpr
          (by simp [contextMembership])
    exact (CutFreeDerivation.pick?_perm
      step.queueStep.left_pick.positional).mem_iff.mpr
        (by simp [afterLeft])
  intro position boundary bucket sigmaLookup readyLookup
  rcases invariant.ready_bucket_frontier_exact_with_gap
      sigmaLookup readyLookup with
    ⟨oldComponent, oldComponentLookup, oldExact⟩
  by_cases focus : boundary = gapBoundary
  · subst boundary
    have oldComponentEq : oldComponent = step.queueStep.component :=
      Option.some.inj (Option.some.inj
        (oldComponentLookup.symm.trans oldRaw))
    subst oldComponent
    refine ⟨nextComponent, ?_, ?_⟩
    · change afterCore.components[gapBoundary]? = some (some nextComponent)
      rw [componentsEq]
      simp [outputBound]
    · intro vertex
      change vertex ∈ bucket ↔
        (vertex ∈ nextComponent.frontier ∧
          afterCore.marks[vertex]? = some none) ∨
        (gapBoundary = gapBoundary ∧ vertex ∈ payload)
      rw [marksEq]
      constructor
      · intro bucketMembership
        rcases (oldExact vertex).mp bucketMembership with
          ⟨oldFrontier, unmarked⟩ | ⟨_sameBoundary, oldGap⟩
        · left
          exact ⟨by
            simp [nextComponent,
              context_of_frontier_unmarked oldFrontier unmarked], unmarked⟩
        · simp only [List.mem_cons] at oldGap
          rcases oldGap with rfl | tailMembership
          · left
            exact ⟨by simp [nextComponent], guards.1⟩
          · right
            exact ⟨rfl, tailMembership⟩
      · intro targetMembership
        apply (oldExact vertex).mpr
        rcases targetMembership with
          ⟨newFrontier, unmarked⟩ | ⟨_sameBoundary, tailMembership⟩
        · change vertex ∈ step.queueStep.context ++ [conclusion]
            at newFrontier
          rw [List.mem_append] at newFrontier
          rcases newFrontier with contextMembership | headMembership
          · left
            exact ⟨frontier_of_context contextMembership, unmarked⟩
          · right
            have same : vertex = conclusion := by simpa using headMembership
            exact ⟨rfl, by simp [same]⟩
        · right
          exact ⟨rfl, by simp [tailMembership]⟩
  · refine ⟨oldComponent, ?_, ?_⟩
    · change afterCore.components[boundary]? = some (some oldComponent)
      rw [componentsEq,
        Array.getElem?_setIfInBounds_ne (Ne.symm focus)]
      exact oldComponentLookup
    · intro vertex
      rw [marksEq]
      have old := oldExact vertex
      simpa [focus] using old

private theorem gap_foldl_add_weight
    {alpha : Type} (weight : alpha → Nat) (values : List alpha)
    (initial : Nat) :
    values.foldl (fun total value => total + weight value) initial =
      initial + (values.map weight).sum := by
  induction values generalizing initial with
  | nil => simp
  | cons head tail induction =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [induction]
      omega

private theorem gap_map_sum_set_balance
    {alpha : Type} {values : List alpha} {index : Nat}
    {oldValue newValue : alpha}
    (weight : alpha → Nat)
    (lookup : values[index]? = some oldValue) :
    ((values.set index newValue).map weight).sum + weight oldValue =
      (values.map weight).sum + weight newValue := by
  induction values generalizing index with
  | nil => simp at lookup
  | cons head tail induction =>
      cases index with
      | zero =>
          have headEq : head = oldValue := by simpa using lookup
          subst head
          simp
          omega
      | succ prior =>
          simp only [List.getElem?_cons_succ] at lookup
          simp only [List.set, List.map_cons, List.sum_cons]
          have inner := induction lookup
          omega

private theorem gap_map_sum_set_add_one
    {alpha : Type} {values : List alpha} {index : Nat}
    {oldValue newValue : alpha} (weight : alpha → Nat)
    (lookup : values[index]? = some oldValue)
    (weightEq : weight newValue = weight oldValue + 1) :
    ((values.set index newValue).map weight).sum =
      (values.map weight).sum + 1 := by
  have balance := gap_map_sum_set_balance weight lookup
    (newValue := newValue)
  rw [weightEq] at balance
  omega

/-- One stored par constructor increments the runtime firing counter and the
live derivation-tree connective count by exactly the same amount. -/
private theorem queueParFiredCounterExact
    {certificate : Certificate} {state : ReservationState}
    {gapBoundary : RawTokenAge} {conclusion : Vertex}
    {payload : List Vertex} {afterCore : UnificationState}
    (invariant : UnifyPayloadGapInvariant certificate state gapBoundary
      (conclusion :: payload))
    (step : WaitingParActivationStep certificate state.core afterCore conclusion) :
    FiredCounterExact { state with core := afterCore } := by
  let weight : Option UnificationComponent → Nat := fun cell =>
    (cell.map UnificationComponent.connectiveCount).getD 0
  let values := state.core.components.toList
  let nextComponent : UnificationComponent := {
    tree := .par step.queueStep.leftFocus step.queueStep.rightFocus
      step.queueStep.component.tree
    frontier := step.queueStep.context ++ [conclusion] }
  have root := invariant.headOutput_root step
  have rawLookup :
      state.core.components[step.queueStep.outputToken]? =
        some (some step.queueStep.component) := by
    have raw := UnificationState.componentAt?_some_raw
      step.queueStep.component_lookup
    simpa [root] using raw
  have listLookup : values[step.queueStep.outputToken]? =
      some (some step.queueStep.component) := by
    simpa [values] using rawLookup
  have weightIncrease :
      weight (some nextComponent) =
        weight (some step.queueStep.component) + 1 := by
    simp [weight, nextComponent, UnificationComponent.connectiveCount,
      CutFreeDerivation.connectiveCount]
  have sumIncrease :
      (((values.set step.queueStep.outputToken
          (some nextComponent)).map weight).sum) =
        (values.map weight).sum + 1 :=
    gap_map_sum_set_add_one weight listLookup weightIncrease
  have totalIncrease :
      (values.set step.queueStep.outputToken (some nextComponent)).foldl
          (fun total cell => total + weight cell) 0 =
        values.foldl (fun total cell => total + weight cell) 0 + 1 := by
    rw [gap_foldl_add_weight, gap_foldl_add_weight]
    simpa using sumIncrease
  have oldCounter := invariant.fired_counter_exact
  unfold FiredCounterExact UnificationState.liveConnectiveCount at oldCounter
  change state.core.firedConnectives =
      values.foldl (fun total cell => total + weight cell) 0 at oldCounter
  have firedAfter :
      afterCore.firedConnectives = state.core.firedConnectives + 1 :=
    step.exact.2.2.2.2
  unfold FiredCounterExact UnificationState.liveConnectiveCount
  rw [firedAfter, step.exact.1, Array.toList_setIfInBounds]
  change state.core.firedConnectives + 1 =
    (values.set step.queueStep.outputToken (some nextComponent)).foldl
      (fun total cell => total + weight cell) 0
  rw [totalIncrease]
  exact congrArg (fun count => count + 1) oldCounter

/-- The fundamental transient induction step: one successful stored-order par
activation consumes exactly the gap head while preserving every non-ready
scheduler field on the fixed final-stack shadow. -/
theorem activateHead
    {certificate : Certificate} {state : ReservationState}
    {gapBoundary : RawTokenAge} {conclusion : Vertex}
    {payload : List Vertex} {afterCore : UnificationState}
    (invariant : UnifyPayloadGapInvariant certificate state gapBoundary
      (conclusion :: payload))
    (step : WaitingParActivationStep certificate state.core afterCore conclusion) :
    UnifyPayloadGapInvariant certificate { state with core := afterCore }
      gapBoundary payload := by
  exact {
    toReservationInvariant := invariant.queueParReservationInvariant step
    structural := invariant.structural
    component_domain_exact := invariant.queueParComponentDomainExact step
    component_forest_provenance := invariant.queueParComponentForest step
    live_frontiers_nodup := invariant.queueParLiveFrontiersNodup step
    queued_vertices_nodup := invariant.queueParQueuedVerticesNodup step
    queued_vertices_unmarked := invariant.queueParQueuedVerticesUnmarked step
    produced_premises_marked :=
      invariant.queueParProducedPremisesMarked step
    waiting_span_exact := invariant.queueParWaitingSpanExact step
    pending_premises_covered_except_ready :=
      invariant.queueParPendingPremisesCoveredExceptReady step
    fired_counter_exact := invariant.queueParFiredCounterExact step
    gap_boundary_top := invariant.gap_boundary_top
    ready_bucket_frontier_exact_with_gap :=
      invariant.queueParReadyBucketFrontierExactWithGap step
    gap_nodup := (List.nodup_cons.mp invariant.gap_nodup).2
    gap_unmarked := by
      intro vertex membership
      change afterCore.marks[vertex]? = some none
      rw [step.exact.2.1]
      exact invariant.gap_unmarked vertex (by simp [membership])
    gap_not_produced := invariant.tailNotProduced step
    gap_premises_at_boundary := invariant.tailPremisesAtBoundary step }

/-- A proof-relevant stored-order activation fold closes a real transient gap.
No physical intermediate is assigned `SchedulerInvariant`; each induction state
uses the caller-supplied fixed final scheduler stack and only replaces its
current production core. -/
theorem WaitingParActivationFoldStep.closeGap
    {certificate : Certificate} {shadow : ReservationState}
    {beforeCore afterCore : UnificationState} {payload : List Vertex}
    {gapBoundary : RawTokenAge}
    (fold : WaitingParActivationFoldStep certificate beforeCore payload afterCore)
    (invariant : UnifyPayloadGapInvariant certificate
      { shadow with core := beforeCore } gapBoundary payload) :
    SchedulerInvariant certificate { shadow with core := afterCore } := by
  induction fold generalizing shadow with
  | nil state =>
      simpa using invariant.close
  | @cons beforeCore middleCore afterCore conclusion payload head tail induction =>
      have next := invariant.activateHead head
      apply induction (shadow := shadow)
      simpa using next

end UnifyPayloadGapInvariant

namespace UnifyPayloadStep

private theorem readyMemLiveFrontierLocal
    {certificate : Certificate} {state : ReservationState}
    (invariant : SchedulerInvariant certificate state)
    {vertex : Vertex} (membership : vertex ∈ state.stack.ready.flatten) :
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

private theorem liveFrontierUnmarkedMemReadyLocal
    {certificate : Certificate} {state : ReservationState}
    (invariant : SchedulerInvariant certificate state)
    {vertex : Vertex}
    (frontier : vertex ∈ state.core.liveFrontierVertices)
    (unmarked : state.core.marks[vertex]? = some none) :
    vertex ∈ state.stack.ready.flatten := by
  unfold UnificationState.liveFrontierVertices at frontier
  rcases List.mem_flatMap.mp frontier with
    ⟨cell, cellMembership, vertexMembership⟩
  cases cell with
  | none => simp at vertexMembership
  | some component =>
      simp only [Option.map_some, Option.getD_some] at vertexMembership
      rcases List.mem_iff_getElem.mp cellMembership with
        ⟨index, indexBound, indexEquation⟩
      have componentLookup : state.core.components[index]? =
          some (some component) := by
        rw [← Array.getElem?_toList]
        rw [List.getElem?_eq_getElem indexBound, indexEquation]
      have boundaryMembership : index ∈ state.stack.sigma :=
        (invariant.component_domain_exact index).mp
          ⟨component, componentLookup⟩
      rcases List.mem_iff_getElem.mp boundaryMembership with
        ⟨position, positionBound, positionEquation⟩
      have sigmaLookup : state.stack.sigma[position]? = some index := by
        rw [List.getElem?_eq_getElem positionBound, positionEquation]
      have readyBound : position < state.stack.ready.length := by
        rw [invariant.stack_wellShaped.ready_aligned]
        exact positionBound
      let bucket := state.stack.ready[position]
      have readyLookup : state.stack.ready[position]? = some bucket :=
        List.getElem?_eq_getElem readyBound
      rcases invariant.ready_bucket_frontier_exact sigmaLookup readyLookup with
        ⟨actual, actualLookup, exactMembership⟩
      have actualEq : actual = component :=
        Option.some.inj
          (Option.some.inj (actualLookup.symm.trans componentLookup))
      subst actual
      apply List.mem_flatten.mpr
      exact ⟨bucket, List.mem_of_getElem? readyLookup,
        (exactMembership vertex).mpr ⟨vertexMembership, unmarked⟩⟩

/-- The non-circular initial shadow: final post-drain scheduler stack, tensor
core before any waiting-par activation, and the unchanged input tags. -/
private def tensorShadow
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after) : ReservationState := {
  stack := step.stackAfter
  core := step.coreTensor
  tags := before.tags }

private theorem activeBoundary_eq
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after) :
    step.mergeStep.activeBoundary = step.prepared.stackResult.rawAge := by
  have mergeTop :
      step.prepared.stackResult.after.sigma.getLast? =
        some step.mergeStep.activeBoundary := by
    rw [step.mergeStep.sigma_eq]
    simp
  have preparedTop :
      step.prepared.stackResult.after.sigma.getLast? =
        some step.prepared.stackResult.rawAge := by
    rcases SequentialStackState.popReadyMark?_exact step.prepared.stack_eq with
      ⟨_, sigmaTop, _, _, _, sigmaAfter, _, _, _⟩
    rw [sigmaAfter]
    exact sigmaTop
  exact Option.some.inj (mergeTop.symm.trans preparedTop)

private theorem middle_sigma_eq
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after) :
    step.prepared.stackResult.after.sigma =
      step.mergeStep.sigmaPrefix ++
        [step.previousBoundary, step.prepared.stackResult.rawAge] := by
  simpa [step.activeBoundary_eq] using step.mergeStep.sigma_eq

private theorem previous_lt_active
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after) :
    step.previousBoundary < step.prepared.stackResult.rawAge :=
  Nat.lt_of_le_of_lt step.lower step.upper

private theorem min_token_eq
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after) :
    min step.tensorStep.leftToken step.tensorStep.rightToken =
      step.previousBoundary := by
  rcases step.tokens_eq_adjacent with orientation | orientation
  · rw [orientation.2.1, orientation.2.2]
    exact Nat.min_eq_right (Nat.le_of_lt step.previous_lt_active)
  · rw [orientation.2.1, orientation.2.2]
    exact Nat.min_eq_left (Nat.le_of_lt step.previous_lt_active)

private theorem max_token_eq
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after) :
    max step.tensorStep.leftToken step.tensorStep.rightToken =
      step.prepared.stackResult.rawAge := by
  rcases step.tokens_eq_adjacent with orientation | orientation
  · rw [orientation.2.1, orientation.2.2]
    exact Nat.max_eq_left (Nat.le_of_lt step.previous_lt_active)
  · rw [orientation.2.1, orientation.2.2]
    exact Nat.max_eq_right (Nat.le_of_lt step.previous_lt_active)

private def tensorComponent
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after) :
    UnificationComponent := {
  tree := .tensor step.tensorStep.leftFocus step.tensorStep.rightFocus
    step.tensorStep.leftComponent.tree step.tensorStep.rightComponent.tree
  frontier := step.consumer.conclusion ::
    (step.tensorStep.leftContext ++ step.tensorStep.rightContext) }

private theorem tensor_components_eq
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after) :
    step.coreTensor.components =
      ((step.prepared.coreMarked.components.setIfInBounds
          step.previousBoundary (some step.tensorComponent))
        |>.setIfInBounds step.prepared.stackResult.rawAge none) := by
  rw [step.tensorStep.after_eq, step.min_token_eq, step.max_token_eq]
  rfl

private theorem stack_sigma_eq
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after) :
    step.stackAfter.sigma =
      step.mergeStep.sigmaPrefix ++ [step.previousBoundary] := by
  simpa using congrArg (fun state : SequentialStackState => state.sigma)
    step.mergeStep.after_eq

private theorem stack_waiting_eq
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after) :
    step.stackAfter.waiting =
      step.prepared.stackResult.after.waiting.setIfInBounds
        step.previousBoundary .undefined := by
  simpa using congrArg (fun state : SequentialStackState => state.waiting)
    step.mergeStep.after_eq

private theorem stack_ready_eq
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after) :
    step.stackAfter.ready =
      step.mergeStep.readyPrefix ++
        [step.consumer.conclusion ::
          (step.payload ++
            (step.mergeStep.previousReady ++ step.mergeStep.activeReady))] := by
  have payloadEquation : step.mergeStep.payload = step.payload :=
    WaitingCell.initialized.inj
      (Option.some.inj
        (step.mergeStep.waiting_initialized.symm.trans step.waiting_payload))
  simpa [payloadEquation] using congrArg
    (fun state : SequentialStackState => state.ready)
    step.mergeStep.after_eq

private theorem tensor_core_marks_eq
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after) :
    step.coreTensor.marks = step.prepared.coreMarked.marks := by
  rw [step.tensorStep.after_eq]

private theorem left_root
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    step.prepared.coreMarked.representative step.tensorStep.leftToken =
      step.tensorStep.leftToken := by
  have middleInvariant := step.prepared.schedulerInvariant invariant
  exact middleInvariant.core_abstractable.tokenAt?_root
    (UnificationState.unifyTokens?_success
      step.tensorStep.token_guard).2.1

private theorem right_root
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    step.prepared.coreMarked.representative step.tensorStep.rightToken =
      step.tensorStep.rightToken := by
  have middleInvariant := step.prepared.schedulerInvariant invariant
  exact middleInvariant.core_abstractable.tokenAt?_root
    (UnificationState.unifyTokens?_success
      step.tensorStep.token_guard).2.2.1

private theorem left_component_raw
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    step.prepared.coreMarked.components[step.tensorStep.leftToken]? =
      some (some step.tensorStep.leftComponent) := by
  have raw := UnificationState.componentAt?_some_raw
    step.tensorStep.left_component
  simpa [step.left_root invariant] using raw

private theorem right_component_raw
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    step.prepared.coreMarked.components[step.tensorStep.rightToken]? =
      some (some step.tensorStep.rightComponent) := by
  have raw := UnificationState.componentAt?_some_raw
    step.tensorStep.right_component
  simpa [step.right_root invariant] using raw

private theorem previous_bound
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    step.previousBoundary < step.prepared.coreMarked.components.size := by
  rcases step.tokens_eq_adjacent with orientation | orientation
  · rw [← orientation.2.2]
    exact (Array.getElem?_eq_some_iff.mp
      (step.right_component_raw invariant)).1
  · rw [← orientation.2.1]
    exact (Array.getElem?_eq_some_iff.mp
      (step.left_component_raw invariant)).1

private theorem active_bound
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    step.prepared.stackResult.rawAge <
      step.prepared.coreMarked.components.size := by
  rcases step.tokens_eq_adjacent with orientation | orientation
  · rw [← orientation.2.1]
    exact (Array.getElem?_eq_some_iff.mp
      (step.left_component_raw invariant)).1
  · rw [← orientation.2.2]
    exact (Array.getElem?_eq_some_iff.mp
      (step.right_component_raw invariant)).1

private theorem tensor_wellFormed
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after) :
    certificate.LinkWellFormed
      (.tensor step.consumer.storedLeft step.consumer.storedRight
        step.consumer.conclusion) :=
  Certificate.tensorBelow?_wellFormed step.consumer_eq

private theorem selected_eq_premise
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after) :
    step.prepared.stackResult.vertex =
      step.consumer.side.premise step.consumer.storedLeft
        step.consumer.storedRight := by
  change step.prepared.stackResult.vertex = step.consumer.premise
  exact Certificate.tensorBelow?_premise step.consumer_eq

private theorem premise_orientation
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after) :
    ((step.consumer.mate = step.consumer.storedLeft ∧
        step.prepared.stackResult.vertex = step.consumer.storedRight) ∨
      (step.consumer.mate = step.consumer.storedRight ∧
        step.prepared.stackResult.vertex = step.consumer.storedLeft)) := by
  cases sideEquation : step.consumer.side with
  | storedLeft =>
      right
      constructor
      · simp [TensorBelow.mate, TensorPremiseSide.mate, sideEquation]
      · simpa [TensorPremiseSide.premise, sideEquation] using
          step.selected_eq_premise
  | storedRight =>
      left
      constructor
      · simp [TensorBelow.mate, TensorPremiseSide.mate, sideEquation]
      · simpa [TensorPremiseSide.premise, sideEquation] using
          step.selected_eq_premise

private theorem conclusion_ne_selected
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after) :
    step.consumer.conclusion ≠ step.prepared.stackResult.vertex := by
  have tensorWellFormed := step.tensor_wellFormed
  cases sideEquation : step.consumer.side with
  | storedLeft =>
      have selectedEq : step.prepared.stackResult.vertex =
          step.consumer.storedLeft := by
        simpa [TensorPremiseSide.premise, sideEquation] using
          step.selected_eq_premise
      intro same
      exact tensorWellFormed.2.1 (selectedEq.symm.trans same.symm)
  | storedRight =>
      have selectedEq : step.prepared.stackResult.vertex =
          step.consumer.storedRight := by
        simpa [TensorPremiseSide.premise, sideEquation] using
          step.selected_eq_premise
      intro same
      exact tensorWellFormed.2.2.1 (selectedEq.symm.trans same.symm)

private theorem conclusion_not_produced_before
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    ¬ Produced before step.consumer.conclusion := by
  intro produced
  have linkMembership :
      (.tensor step.consumer.storedLeft step.consumer.storedRight
        step.consumer.conclusion : Link) ∈ certificate.links :=
    List.mem_of_getElem? step.submitted_tensor
  rcases invariant.produced_premises_marked linkMembership produced with
    ⟨⟨leftAge, leftMarked⟩, rightAge, rightMarked⟩
  rcases UnificationState.markReadyRaw?_exact
      step.prepared.core_mark_eq with
    ⟨selectedUnmarked, _, _, _, _, _, _⟩
  cases sideEquation : step.consumer.side with
  | storedLeft =>
      have selectedEq : step.prepared.stackResult.vertex =
          step.consumer.storedLeft := by
        simpa [TensorPremiseSide.premise, sideEquation] using
          step.selected_eq_premise
      have leftUnmarked :
          before.core.marks[step.consumer.storedLeft]? = some none :=
        (congrArg (fun vertex => before.core.marks[vertex]?)
          selectedEq).symm.trans selectedUnmarked
      rw [leftUnmarked] at leftMarked
      simp at leftMarked
  | storedRight =>
      have selectedEq : step.prepared.stackResult.vertex =
          step.consumer.storedRight := by
        simpa [TensorPremiseSide.premise, sideEquation] using
          step.selected_eq_premise
      have rightUnmarked :
          before.core.marks[step.consumer.storedRight]? = some none :=
        (congrArg (fun vertex => before.core.marks[vertex]?)
          selectedEq).symm.trans selectedUnmarked
      rw [rightUnmarked] at rightMarked
      simp at rightMarked

private theorem conclusion_not_produced_middle
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    ¬ Produced step.prepared.after step.consumer.conclusion := by
  intro produced
  apply step.conclusion_not_produced_before invariant
  rcases UnificationState.markReadyRaw?_exact
      step.prepared.core_mark_eq with
    ⟨_, marksEq, _, componentsEq, _, _, _⟩
  rcases produced with ⟨age, marked⟩ | frontier
  · left
    refine ⟨age, ?_⟩
    change step.prepared.coreMarked.marks[
        step.consumer.conclusion]? = some (some age) at marked
    rw [marksEq] at marked
    simpa [Array.getElem?_setIfInBounds,
      Ne.symm step.conclusion_ne_selected] using marked
  · right
    unfold UnificationState.liveFrontierVertices at frontier ⊢
    change step.consumer.conclusion ∈
      step.prepared.coreMarked.components.toList.flatMap _ at frontier
    rw [componentsEq] at frontier
    exact frontier

private theorem conclusion_not_mem_waiting_before
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    step.consumer.conclusion ∉ before.stack.waitingVertices := by
  intro conclusionWaiting
  unfold SequentialStackState.waitingVertices at conclusionWaiting
  rcases List.mem_flatMap.mp conclusionWaiting with
    ⟨cell, cellMembership, conclusionInCell⟩
  cases cell with
  | undefined => simp [WaitingCell.vertices] at conclusionInCell
  | initialized oldPayload =>
      simp only [WaitingCell.vertices] at conclusionInCell
      rcases List.mem_iff_getElem.mp cellMembership with
        ⟨boundary, boundaryBound, boundaryEquation⟩
      have waitingLookup : before.stack.waiting[boundary]? =
          some (.initialized oldPayload) := by
        rw [← Array.getElem?_toList]
        rw [List.getElem?_eq_getElem boundaryBound, boundaryEquation]
      rcases invariant.waiting_span_exact waitingLookup conclusionInCell with
        ⟨oldLinkIndex, oldLeft, oldRight, olderPremise,
          youngerPremise, olderAge, youngerAge, youngerBoundary,
          oldLinkLookup, oldSourceLookup, conclusionUnmarked,
          oldOrientation, olderMarked, youngerMarked,
          olderBoundary, youngerBoundaryLookup, boundaryOrder⟩
      have oldLinkMembership :
          (.par oldLeft oldRight step.consumer.conclusion : Link) ∈
            certificate.links :=
        List.mem_of_getElem? oldLinkLookup
      have currentLinkMembership :
          (.tensor step.consumer.storedLeft step.consumer.storedRight
            step.consumer.conclusion : Link) ∈ certificate.links :=
        List.mem_of_getElem? step.submitted_tensor
      have impossible :=
        UnificationState.StructurallyWellFormed.producerLink_unique
          invariant.structural
          (conclusion := step.consumer.conclusion)
          oldLinkMembership (by simp [Link.produces])
          currentLinkMembership (by simp [Link.produces])
      cases impossible

private theorem conclusion_not_mem_waiting_middle
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    step.consumer.conclusion ∉
      step.prepared.after.stack.waitingVertices := by
  intro waiting
  rcases SequentialStackState.popReadyMark?_exact
      step.prepared.stack_eq with
    ⟨_, _, _, _, _, _, _, waitingEq, _⟩
  apply step.conclusion_not_mem_waiting_before invariant
  unfold SequentialStackState.waitingVertices at waiting ⊢
  change step.consumer.conclusion ∈
      step.prepared.stackResult.after.waiting.toList.flatMap _ at waiting
  rw [waitingEq] at waiting
  exact waiting

private theorem conclusion_not_queued_middle
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    step.consumer.conclusion ∉
      step.prepared.after.stack.queuedVertices := by
  intro queued
  unfold SequentialStackState.queuedVertices at queued
  rcases List.mem_append.mp queued with ready | waiting
  · exact step.conclusion_not_produced_middle invariant
      (Or.inr
        (readyMemLiveFrontierLocal
          (step.prepared.schedulerInvariant invariant) ready))
  · exact step.conclusion_not_mem_waiting_middle invariant waiting

/-- The tensor shadow satisfies the complete reservation layer against the
final scheduler stack. -/
private theorem tensorShadow_reservationInvariant
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    ReservationInvariant certificate step.tensorShadow := by
  have middleInvariant := step.prepared.schedulerInvariant invariant
  have finalInvariant := step.reservationInvariant
  rw [step.output_eq] at finalInvariant
  have finalRealizes := step.realizesSigma
  have tensorRealizes : RealizesSigma step.stackAfter step.coreTensor := {
    marks_eq := step.activationFold.marks_eq.symm.trans
      finalRealizes.marks_eq
    horizon_eq := by
      calc
        step.coreTensor.parents.size = step.coreAfter.parents.size :=
          (congrArg Array.size step.activationFold.parents_eq).symm
        _ = step.stackAfter.nextAge := finalRealizes.horizon_eq
    representative_eq_boundary := by
      intro age ageBound
      calc
        sigmaBoundary? step.stackAfter.sigma age =
            some (step.coreAfter.representative age) :=
          finalRealizes.representative_eq_boundary ageBound
        _ = some (step.coreTensor.representative age) := by
          unfold UnificationState.representative
          rw [step.activationFold.parents_eq] }
  have alignment := Certificate.queueTensor?_reservationAlignment
    middleInvariant.core_carriers_aligned middleInvariant.core_counter_aligned
      step.tensor_queue_eq
  exact {
    stack_wellShaped := finalInvariant.stack_wellShaped
    stack_operationalWaitingDomain :=
      finalInvariant.stack_operationalWaitingDomain
    realizesSigma := tensorRealizes
    core_orderedParents := Certificate.queueTensor?_orderedParents
      middleInvariant.core_orderedParents step.tensor_queue_eq
    core_abstractable := Certificate.queueTensor?_abstractable
      middleInvariant.core_abstractable middleInvariant.core_orderedParents
        step.tensor_queue_eq
    core_componentsFormulaConsistent :=
      Certificate.queueTensor?_componentsFormulaConsistent
        middleInvariant.core_componentsFormulaConsistent
        (Certificate.tensorBelow?_wellFormed step.consumer_eq)
        step.tensor_queue_eq
    core_carriers_aligned := alignment.1
    core_counter_aligned := alignment.2
    tags_size := invariant.tags_size }

private theorem tensorShadow_componentDomainExact
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    ComponentDomainExact step.tensorShadow := by
  have middleInvariant := step.prepared.schedulerInvariant invariant
  have activeNotReduced :
      step.prepared.stackResult.rawAge ∉
        step.mergeStep.sigmaPrefix ++ [step.previousBoundary] := by
    intro membership
    have increasing :
        step.prepared.stackResult.after.sigma.Pairwise (· < ·) := by
      simpa [PreparedStep.after] using
        middleInvariant.stack_wellShaped.sigma_partition.strictIncreasing
    rw [step.middle_sigma_eq] at increasing
    have normalized :
        step.mergeStep.sigmaPrefix ++
            [step.previousBoundary, step.prepared.stackResult.rawAge] =
          (step.mergeStep.sigmaPrefix ++ [step.previousBoundary]) ++
            [step.prepared.stackResult.rawAge] := by
      simp [List.append_assoc]
    rw [normalized] at increasing
    have cross := (List.pairwise_append.mp increasing).2.2
    exact Nat.lt_irrefl _
      (cross step.prepared.stackResult.rawAge membership
        step.prepared.stackResult.rawAge (by simp))
  intro token
  change (∃ component,
      step.coreTensor.components[token]? = some (some component)) ↔
    token ∈ step.stackAfter.sigma
  rw [step.tensor_components_eq, step.stack_sigma_eq]
  by_cases previous : token = step.previousBoundary
  · subst token
    constructor
    · intro _
      simp
    · intro _
      refine ⟨step.tensorComponent, ?_⟩
      rw [Array.getElem?_setIfInBounds_ne
        (Nat.ne_of_gt step.previous_lt_active)]
      simp [step.previous_bound invariant]
  · by_cases active : token = step.prepared.stackResult.rawAge
    · subst token
      simp [step.active_bound invariant, activeNotReduced]
    · have oldDomain :
        (∃ component,
          step.prepared.coreMarked.components[token]? =
            some (some component)) ↔
          token ∈ step.prepared.stackResult.after.sigma := by
        simpa [PreparedStep.after] using
          middleInvariant.component_domain_exact token
      rw [step.middle_sigma_eq] at oldDomain
      rw [Array.getElem?_setIfInBounds_ne (Ne.symm active),
        Array.getElem?_setIfInBounds_ne (Ne.symm previous)]
      simpa [active] using oldDomain

private theorem tensorProducedCases
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after)
    (invariant : SchedulerInvariant certificate before)
    {vertex : Vertex} (produced : Produced step.tensorShadow vertex) :
    vertex = step.consumer.conclusion ∨
      Produced step.prepared.after vertex := by
  rcases produced with ⟨rawAge, marked⟩ | frontierMembership
  · apply Or.inr
    apply Or.inl
    refine ⟨rawAge, ?_⟩
    change step.coreTensor.marks[vertex]? = some (some rawAge) at marked
    rw [step.tensorStep.after_eq] at marked
    exact marked
  · change vertex ∈ step.coreTensor.liveFrontierVertices at frontierMembership
    unfold UnificationState.liveFrontierVertices at frontierMembership
    rcases List.mem_flatMap.mp frontierMembership with
      ⟨cell, cellMembership, vertexFrontier⟩
    cases cell with
    | none => simp at vertexFrontier
    | some component =>
        simp only [Option.map_some, Option.getD_some] at vertexFrontier
        rcases List.mem_iff_getElem.mp cellMembership with
          ⟨index, indexBound, indexEquation⟩
        have tensorLookup :
            step.coreTensor.components[index]? = some (some component) := by
          rw [← Array.getElem?_toList]
          rw [List.getElem?_eq_getElem indexBound, indexEquation]
        by_cases previous : index = step.previousBoundary
        · subst index
          rw [step.tensor_components_eq] at tensorLookup
          simp [step.previous_bound invariant,
            Nat.ne_of_gt step.previous_lt_active] at tensorLookup
          subst component
          simp only [tensorComponent, List.mem_cons,
            List.mem_append] at vertexFrontier
          rcases vertexFrontier with rfl | inLeft | inRight
          · exact Or.inl rfl
          · apply Or.inr
            apply Or.inr
            unfold UnificationState.liveFrontierVertices
            apply List.mem_flatMap.mpr
            refine ⟨some step.tensorStep.leftComponent, ?_, ?_⟩
            · exact List.mem_of_getElem? (by
                simpa [PreparedStep.after] using
                  step.left_component_raw invariant)
            · exact (CutFreeDerivation.pick?_perm
                step.tensorStep.left_pick.positional).mem_iff.mpr (by
                  simp [inLeft])
          · apply Or.inr
            apply Or.inr
            unfold UnificationState.liveFrontierVertices
            apply List.mem_flatMap.mpr
            refine ⟨some step.tensorStep.rightComponent, ?_, ?_⟩
            · exact List.mem_of_getElem? (by
                simpa [PreparedStep.after] using
                  step.right_component_raw invariant)
            · exact (CutFreeDerivation.pick?_perm
                step.tensorStep.right_pick.positional).mem_iff.mpr (by
                  simp [inRight])
        · by_cases active : index = step.prepared.stackResult.rawAge
          · subst index
            rw [step.tensor_components_eq] at tensorLookup
            simp [step.active_bound invariant] at tensorLookup
          · apply Or.inr
            apply Or.inr
            unfold UnificationState.liveFrontierVertices
            apply List.mem_flatMap.mpr
            refine ⟨some component, ?_, by simpa using vertexFrontier⟩
            have oldLookup :
                step.prepared.coreMarked.components[index]? =
                  some (some component) := by
              rw [step.tensor_components_eq] at tensorLookup
              simpa [Array.getElem?_setIfInBounds, Ne.symm previous,
                Ne.symm active] using tensorLookup
            exact List.mem_of_getElem? (by
              simpa [PreparedStep.after] using oldLookup)

private theorem tensorShadow_componentForestProvenance
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    certificate.ComponentForestProvenance step.tensorShadow.core := by
  have middleInvariant := step.prepared.schedulerInvariant invariant
  have tensorConclusionFresh :
      ∀ {index component owned},
        step.prepared.coreMarked.components[index]? =
            some (some component) →
        Certificate.OwnedOccurrenceAccounted
            step.prepared.coreMarked index component owned →
        step.consumer.conclusion ∉ owned := by
    intro index component owned componentLookup accounted conclusionOwned
    apply step.conclusion_not_produced_middle invariant
    rcases accounted step.consumer.conclusion conclusionOwned with
      ⟨rawAge, marked, _⟩ | ⟨unmarked, frontier⟩
    · exact Or.inl ⟨rawAge, marked⟩
    · apply Or.inr
      unfold UnificationState.liveFrontierVertices
      apply List.mem_flatMap.mpr
      refine ⟨some component, ?_, ?_⟩
      · exact List.mem_of_getElem? (by
          simpa [PreparedStep.after] using componentLookup)
      · exact frontier
  exact middleInvariant.component_forest_provenance
    |>.queueTensorStep_of_roots_fresh
      middleInvariant.core_abstractable
      middleInvariant.core_orderedParents step.tensorStep
      step.consumer.linkIndex step.submitted_tensor tensorConclusionFresh

private theorem tensorShadow_liveFrontiersNodup
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    LiveFrontiersNodup step.tensorShadow := by
  unfold LiveFrontiersNodup
  simpa [tensorShadow, UnificationState.liveFrontierVertices] using
    (step.tensorShadow_componentForestProvenance invariant)
      |>.liveFrontiers_nodup

private theorem tensorShadow_queuedVerticesNodup
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    QueuedVerticesNodup step.tensorShadow := by
  have middleInvariant := step.prepared.schedulerInvariant invariant
  have targetNodup :
      (step.consumer.conclusion ::
        step.prepared.after.stack.queuedVertices).Nodup :=
    List.nodup_cons.mpr
      ⟨step.conclusion_not_queued_middle invariant,
        middleInvariant.queued_vertices_nodup⟩
  unfold QueuedVerticesNodup tensorShadow
  exact step.mergeStep.queuedVertices_perm.symm.nodup targetNodup

private theorem tensorShadow_queuedVerticesUnmarked
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    QueuedVerticesUnmarked step.tensorShadow := by
  have middleInvariant := step.prepared.schedulerInvariant invariant
  intro vertex membership
  have targetMembership :=
    step.mergeStep.queuedVertices_perm.mem_iff.mp (by
      simpa [tensorShadow] using membership)
  simp only [List.mem_cons] at targetMembership
  change step.coreTensor.marks[vertex]? = some none
  rw [step.tensorStep.after_eq]
  rcases targetMembership with rfl | oldMembership
  · exact (UnificationState.unifyTokens?_success
      step.tensorStep.token_guard).1
  · exact middleInvariant.queued_vertices_unmarked vertex oldMembership

private theorem merge_payload_eq
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after) :
    step.mergeStep.payload = step.payload :=
  WaitingCell.initialized.inj
    (Option.some.inj
      (step.mergeStep.waiting_initialized.symm.trans step.waiting_payload))

private theorem tensorShadow_gapNodup
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after) :
    step.payload.Nodup := by
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
      simpa using congrArg (fun state : SequentialStackState => state.ready)
        step.mergeStep.after_eq
    rw [readyEquation]
    simp
  have exactMerged :
      step.merged = step.consumer.conclusion ::
        (step.mergeStep.payload ++ step.mergeStep.previousReady ++
          step.mergeStep.activeReady) :=
    Option.some.inj (step.merged_eq.symm.trans mergedLookup)
  have readyNodup := step.ready_nodup
  rw [exactMerged] at readyNodup
  have tailNodup := (List.nodup_cons.mp readyNodup).2
  have payloadPreviousNodup := (List.nodup_append.mp tailNodup).1
  have payloadNodup := (List.nodup_append.mp payloadPreviousNodup).1
  simpa [step.merge_payload_eq] using payloadNodup

private theorem payloadUnmarkedMiddle
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after)
    (invariant : SchedulerInvariant certificate before)
    {vertex : Vertex} (membership : vertex ∈ step.payload) :
    step.prepared.coreMarked.marks[vertex]? = some none := by
  have middleInvariant := step.prepared.schedulerInvariant invariant
  rcases middleInvariant.waiting_span_exact
      step.waiting_payload membership with
    ⟨_, _, _, _, _, _, _, _, _, _, unmarked, _⟩
  exact unmarked

private theorem payloadMemWaitingMiddle
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after)
    {vertex : Vertex} (membership : vertex ∈ step.payload) :
    vertex ∈ step.prepared.after.stack.waitingVertices := by
  unfold SequentialStackState.waitingVertices
  apply List.mem_flatMap.mpr
  refine ⟨.initialized step.payload, ?_, ?_⟩
  · apply List.mem_of_getElem?
    change step.prepared.stackResult.after.waiting.toList[_]? =
      some (WaitingCell.initialized step.payload)
    rw [Array.getElem?_toList]
    exact step.waiting_payload
  · simpa [WaitingCell.vertices] using membership

private theorem payloadNotReadyMiddle
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after)
    (invariant : SchedulerInvariant certificate before)
    {vertex : Vertex} (membership : vertex ∈ step.payload) :
    vertex ∉ step.prepared.after.stack.ready.flatten := by
  have middleInvariant := step.prepared.schedulerInvariant invariant
  have parts := List.nodup_append.mp
    middleInvariant.queued_vertices_nodup
  intro readyMembership
  exact parts.2.2 vertex readyMembership vertex
    (step.payloadMemWaitingMiddle membership) rfl

private theorem payloadNotProducedMiddle
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after)
    (invariant : SchedulerInvariant certificate before)
    {vertex : Vertex} (membership : vertex ∈ step.payload) :
    ¬ Produced step.prepared.after vertex := by
  intro produced
  rcases produced with ⟨rawAge, marked⟩ | frontier
  · have unmarked := step.payloadUnmarkedMiddle invariant membership
    change step.prepared.coreMarked.marks[vertex]? = some (some rawAge)
      at marked
    rw [unmarked] at marked
    simp at marked
  · exact step.payloadNotReadyMiddle invariant membership
      (liveFrontierUnmarkedMemReadyLocal
        (step.prepared.schedulerInvariant invariant) frontier
        (step.payloadUnmarkedMiddle invariant membership))

private theorem payloadNeTensorConclusion
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after)
    (invariant : SchedulerInvariant certificate before)
    {vertex : Vertex} (membership : vertex ∈ step.payload) :
    vertex ≠ step.consumer.conclusion := by
  intro same
  have middleInvariant := step.prepared.schedulerInvariant invariant
  rcases middleInvariant.waiting_span_exact step.waiting_payload membership with
    ⟨linkIndex, left, right, olderPremise, youngerPremise, olderAge,
      youngerAge, youngerBoundary, parLookup, sourceLookup, unmarked,
      orientation, olderMarked, youngerMarked, olderBoundary,
      youngerBoundaryLookup, boundaryOrder⟩
  have parMembership : (.par left right vertex : Link) ∈ certificate.links :=
    List.mem_of_getElem? parLookup
  have tensorMembership :
      (.tensor step.consumer.storedLeft step.consumer.storedRight
        step.consumer.conclusion : Link) ∈ certificate.links :=
    List.mem_of_getElem? step.submitted_tensor
  have impossible :=
    UnificationState.StructurallyWellFormed.producerLink_unique
      invariant.structural (conclusion := vertex)
      parMembership (by simp [Link.produces])
      tensorMembership (by simp [same, Link.produces])
  cases impossible

private theorem tensorShadow_gapNotProduced
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    ∀ vertex ∈ step.payload, ¬ Produced step.tensorShadow vertex := by
  intro vertex membership produced
  rcases step.tensorProducedCases invariant produced with
    same | oldProduced
  · exact step.payloadNeTensorConclusion invariant membership same
  · exact step.payloadNotProducedMiddle invariant membership oldProduced

private theorem tensorShadow_gapUnmarked
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    ∀ vertex ∈ step.payload,
      step.tensorShadow.core.marks[vertex]? = some none := by
  intro vertex membership
  change step.coreTensor.marks[vertex]? = some none
  rw [step.tensorStep.after_eq]
  exact step.payloadUnmarkedMiddle invariant membership

private theorem tensorShadow_gapPremisesAtBoundary
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    ∀ conclusion ∈ step.payload,
      ∃ linkIndex left right,
        certificate.links[linkIndex]? =
            some (.par left right conclusion) ∧
          (SequentialUnification.sourceIndex certificate)[conclusion]? =
            some [{
              linkIndex := linkIndex
              link := .par left right conclusion }] ∧
          step.tensorShadow.core.tokenAt? left =
            some step.previousBoundary ∧
          step.tensorShadow.core.tokenAt? right =
            some step.previousBoundary := by
  intro conclusion conclusionMembership
  have middleInvariant := step.prepared.schedulerInvariant invariant
  rcases middleInvariant.waiting_span_exact
      step.waiting_payload conclusionMembership with
    ⟨linkIndex, left, right, olderPremise, youngerPremise,
      olderAge, youngerAge, youngerBoundary, linkLookup,
      sourceLookup, conclusionUnmarked, orientation,
      olderMarked, youngerMarked, olderBoundary,
      youngerBoundaryLookup, boundaryOrder⟩
  have shadowInvariant := step.tensorShadow_reservationInvariant invariant
  have topLookup : step.tensorShadow.stack.sigma.getLast? =
      some step.previousBoundary := by
    change step.stackAfter.sigma.getLast? = some step.previousBoundary
    rw [step.stack_sigma_eq]
    simp
  have tokenAtBoundary :
      ∀ {premise rawAge},
        step.prepared.coreMarked.marks[premise]? = some (some rawAge) →
        step.previousBoundary ≤ rawAge →
        step.tensorShadow.core.tokenAt? premise =
          some step.previousBoundary := by
    intro premise rawAge marked lower
    have shadowMarked :
        step.tensorShadow.core.marks[premise]? = some (some rawAge) := by
      change step.coreTensor.marks[premise]? = some (some rawAge)
      rw [step.tensorStep.after_eq]
      exact marked
    have stackMarked :
        step.tensorShadow.stack.marks[premise]? = some (some rawAge) := by
      rw [← shadowInvariant.realizesSigma.marks_eq]
      exact shadowMarked
    have ageBound : rawAge < step.tensorShadow.stack.nextAge :=
      shadowInvariant.stack_wellShaped.assigned_age_bound
        premise rawAge stackMarked
    have topBoundary :
        sigmaBoundary? step.tensorShadow.stack.sigma rawAge =
          some step.previousBoundary :=
      shadowInvariant.stack_wellShaped.sigma_partition
        |>.sigmaBoundary?_eq_top_of_le topLookup lower ageBound
    have realized :
        sigmaBoundary? step.tensorShadow.stack.sigma rawAge =
          some (step.tensorShadow.core.representative rawAge) :=
      shadowInvariant.realizesSigma.representative_eq_boundary ageBound
    have representativeEq :
        step.tensorShadow.core.representative rawAge =
          step.previousBoundary :=
      Option.some.inj (realized.symm.trans topBoundary)
    unfold UnificationState.tokenAt?
    rw [shadowMarked]
    simp [representativeEq]
  have olderLower : step.previousBoundary ≤ olderAge :=
    sigmaBoundary?_le (by
      simpa [PreparedStep.after] using olderBoundary)
  have youngerLower : step.previousBoundary ≤ youngerAge := by
    have boundaryLe : youngerBoundary ≤ youngerAge :=
      sigmaBoundary?_le (by
        simpa [PreparedStep.after] using youngerBoundaryLookup)
    exact Nat.le_trans (Nat.le_of_lt boundaryOrder) boundaryLe
  have olderToken := tokenAtBoundary olderMarked olderLower
  have youngerToken := tokenAtBoundary youngerMarked youngerLower
  have tokens :
      step.tensorShadow.core.tokenAt? left =
          some step.previousBoundary ∧
        step.tensorShadow.core.tokenAt? right =
          some step.previousBoundary := by
    rcases orientation with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨olderToken, youngerToken⟩
    · exact ⟨youngerToken, olderToken⟩
  exact ⟨linkIndex, left, right, linkLookup, sourceLookup,
    tokens.1, tokens.2⟩

private theorem tensorShadow_submittedPremisesMarked
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after) :
    (∃ leftAge,
      step.tensorShadow.core.marks[step.consumer.storedLeft]? =
        some (some leftAge)) ∧
      ∃ rightAge,
        step.tensorShadow.core.marks[step.consumer.storedRight]? =
          some (some rightAge) := by
  have selectedMarked :
      step.prepared.coreMarked.marks[
          step.prepared.stackResult.vertex]? =
        some (some step.prepared.stackResult.rawAge) :=
    (UnificationState.markReadyRaw?_exact
      step.prepared.core_mark_eq).2.2.2.2.2.2
  have coreMarksEq :
      step.coreTensor.marks = step.prepared.coreMarked.marks := by
    rw [step.tensorStep.after_eq]
  rcases step.premise_orientation with
    ⟨mateEq, selectedEq⟩ | ⟨mateEq, selectedEq⟩
  · constructor
    · exact ⟨step.mateRawAge, by
        change step.coreTensor.marks[step.consumer.storedLeft]? = _
        rw [coreMarksEq, ← mateEq]
        exact step.mate_marked⟩
    · exact ⟨step.prepared.stackResult.rawAge, by
        change step.coreTensor.marks[step.consumer.storedRight]? = _
        rw [coreMarksEq, ← selectedEq]
        exact selectedMarked⟩
  · constructor
    · exact ⟨step.prepared.stackResult.rawAge, by
        change step.coreTensor.marks[step.consumer.storedLeft]? = _
        rw [coreMarksEq, ← selectedEq]
        exact selectedMarked⟩
    · exact ⟨step.mateRawAge, by
        change step.coreTensor.marks[step.consumer.storedRight]? = _
        rw [coreMarksEq, ← mateEq]
        exact step.mate_marked⟩

private theorem tensorShadow_producedPremisesMarked
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    ProducedPremisesMarked certificate step.tensorShadow := by
  have middleInvariant := step.prepared.schedulerInvariant invariant
  intro link linkMembership
  cases link with
  | «axiom» left right => trivial
  | «par» left right conclusion
  | tensor left right conclusion =>
      intro producedAfter
      rcases step.tensorProducedCases invariant producedAfter with
        conclusionEq | producedMiddle
      · subst conclusion
        have currentMembership :
            (.tensor step.consumer.storedLeft step.consumer.storedRight
              step.consumer.conclusion : Link) ∈ certificate.links :=
          List.mem_of_getElem? step.submitted_tensor
        have producerEq :=
          UnificationState.StructurallyWellFormed.producerLink_unique
            invariant.structural
            (conclusion := step.consumer.conclusion)
            linkMembership (by simp [Link.produces])
            currentMembership (by simp [Link.produces])
        cases producerEq <;>
          exact step.tensorShadow_submittedPremisesMarked
      · rcases middleInvariant.produced_premises_marked
            linkMembership producedMiddle with
          ⟨⟨leftAge, leftMarked⟩, rightAge, rightMarked⟩
        refine ⟨⟨leftAge, ?_⟩, rightAge, ?_⟩
        · change step.coreTensor.marks[left]? = some (some leftAge)
          rw [step.tensorStep.after_eq]
          exact leftMarked
        · change step.coreTensor.marks[right]? = some (some rightAge)
          rw [step.tensorStep.after_eq]
          exact rightMarked

private theorem tensorShadow_waitingSpanExact
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    WaitingSpanExact certificate step.tensorShadow := by
  have middleInvariant := step.prepared.schedulerInvariant invariant
  have middlePartition :=
    middleInvariant.stack_wellShaped.sigma_partition
  have activeTop :
      step.prepared.stackResult.after.sigma.getLast? =
        some step.prepared.stackResult.rawAge := by
    rw [step.middle_sigma_eq]
    simp
  intro boundary payload conclusion waitingLookup conclusionMembership
  have boundaryNePrevious : boundary ≠ step.previousBoundary := by
    intro same
    subst boundary
    have previousWaitingBound :
        step.previousBoundary <
          step.prepared.stackResult.after.waiting.size :=
      (Array.getElem?_eq_some_iff.mp step.waiting_payload).1
    change step.stackAfter.waiting[step.previousBoundary]? =
      some (.initialized payload) at waitingLookup
    rw [step.stack_waiting_eq] at waitingLookup
    simp [previousWaitingBound] at waitingLookup
  have middleWaitingLookup :
      step.prepared.stackResult.after.waiting[boundary]? =
        some (.initialized payload) := by
    change step.stackAfter.waiting[boundary]? =
      some (.initialized payload) at waitingLookup
    rw [step.stack_waiting_eq,
      Array.getElem?_setIfInBounds_ne (Ne.symm boundaryNePrevious)]
      at waitingLookup
    exact waitingLookup
  rcases middleInvariant.waiting_span_exact
      (by simpa [PreparedStep.after] using middleWaitingLookup)
      conclusionMembership with
    ⟨linkIndex, left, right, olderPremise, youngerPremise,
      olderAge, youngerAge, youngerBoundary, linkLookup,
      sourceLookup, conclusionUnmarked, orientation,
      olderMarked, youngerMarked, olderBoundary,
      youngerBoundaryLookup, boundaryOrder⟩
  have boundaryMembership :
      boundary ∈ step.prepared.stackResult.after.sigma :=
    sigmaBoundary?_mem (by
      simpa [PreparedStep.after] using olderBoundary)
  have boundaryBound :
      boundary < step.prepared.stackResult.after.nextAge :=
    middlePartition.boundary_lt boundary boundaryMembership
  have boundaryLtPrevious : boundary < step.previousBoundary :=
    middleInvariant.stack_operationalWaitingDomain
      |>.payload_boundary_lt_previous_of_ne middlePartition
        step.middle_sigma_eq boundaryBound middleWaitingLookup
        conclusionMembership boundaryNePrevious
  have stackOlderMarked :
      step.prepared.stackResult.after.marks[olderPremise]? =
        some (some olderAge) := by
    change step.prepared.after.stack.marks[olderPremise]? =
      some (some olderAge)
    rw [← middleInvariant.realizesSigma.marks_eq]
    exact olderMarked
  have olderAgeBound :
      olderAge < step.prepared.stackResult.after.nextAge :=
    middleInvariant.stack_wellShaped.assigned_age_bound
      olderPremise olderAge (by
        simpa [PreparedStep.after] using stackOlderMarked)
  have olderAgeLtActive :
      olderAge < step.prepared.stackResult.rawAge := by
    by_cases isLt : olderAge < step.prepared.stackResult.rawAge
    · exact isLt
    · have activeLe : step.prepared.stackResult.rawAge ≤ olderAge :=
        Nat.le_of_not_gt isLt
      have activeLookup :=
        middlePartition.sigmaBoundary?_eq_top_of_le
          activeTop activeLe olderAgeBound
      have activeLookup' :
          sigmaBoundary? step.prepared.stackResult.after.sigma olderAge =
            some step.prepared.stackResult.rawAge := by
        simpa [PreparedStep.after] using activeLookup
      have oldLookup :
          sigmaBoundary? step.prepared.stackResult.after.sigma olderAge =
            some boundary := by
        simpa [PreparedStep.after] using olderBoundary
      rw [oldLookup] at activeLookup'
      have same := Option.some.inj activeLookup'
      exact False.elim ((Nat.ne_of_gt
        (Nat.lt_trans boundaryLtPrevious step.previous_lt_active)) same.symm)
  have olderBoundaryAfter :
      sigmaBoundary? step.tensorShadow.stack.sigma olderAge =
        some boundary := by
    change sigmaBoundary? step.stackAfter.sigma olderAge = some boundary
    rw [step.stack_sigma_eq]
    calc
      sigmaBoundary?
          (step.mergeStep.sigmaPrefix ++ [step.previousBoundary])
          olderAge =
          sigmaBoundary? step.prepared.stackResult.after.sigma olderAge :=
        sigmaBoundary?_popActive_of_lt step.middle_sigma_eq olderAgeLtActive
      _ = some boundary := by
        simpa [PreparedStep.after] using olderBoundary
  have stackYoungerMarked :
      step.prepared.stackResult.after.marks[youngerPremise]? =
        some (some youngerAge) := by
    change step.prepared.after.stack.marks[youngerPremise]? =
      some (some youngerAge)
    rw [← middleInvariant.realizesSigma.marks_eq]
    exact youngerMarked
  have youngerAgeBound :
      youngerAge < step.prepared.stackResult.after.nextAge :=
    middleInvariant.stack_wellShaped.assigned_age_bound
      youngerPremise youngerAge (by
        simpa [PreparedStep.after] using stackYoungerMarked)
  by_cases activeLe :
      step.prepared.stackResult.rawAge ≤ youngerAge
  · refine ⟨linkIndex, left, right, olderPremise, youngerPremise,
      olderAge, youngerAge, step.previousBoundary, linkLookup,
      sourceLookup, ?_, orientation, ?_, ?_, olderBoundaryAfter, ?_,
      boundaryLtPrevious⟩
    · change step.coreTensor.marks[conclusion]? = some none
      rw [step.tensor_core_marks_eq]
      exact conclusionUnmarked
    · change step.coreTensor.marks[olderPremise]? = some (some olderAge)
      rw [step.tensor_core_marks_eq]
      exact olderMarked
    · change step.coreTensor.marks[youngerPremise]? = some (some youngerAge)
      rw [step.tensor_core_marks_eq]
      exact youngerMarked
    · change sigmaBoundary? step.stackAfter.sigma youngerAge =
        some step.previousBoundary
      rw [step.stack_sigma_eq]
      exact middlePartition
        |>.sigmaBoundary?_popActive_eq_previous_of_active_le
          step.middle_sigma_eq activeLe youngerAgeBound
  · have youngerAgeLtActive :
        youngerAge < step.prepared.stackResult.rawAge :=
      Nat.lt_of_not_ge activeLe
    refine ⟨linkIndex, left, right, olderPremise, youngerPremise,
      olderAge, youngerAge, youngerBoundary, linkLookup,
      sourceLookup, ?_, orientation, ?_, ?_, olderBoundaryAfter, ?_,
      boundaryOrder⟩
    · change step.coreTensor.marks[conclusion]? = some none
      rw [step.tensor_core_marks_eq]
      exact conclusionUnmarked
    · change step.coreTensor.marks[olderPremise]? = some (some olderAge)
      rw [step.tensor_core_marks_eq]
      exact olderMarked
    · change step.coreTensor.marks[youngerPremise]? = some (some youngerAge)
      rw [step.tensor_core_marks_eq]
      exact youngerMarked
    · change sigmaBoundary? step.stackAfter.sigma youngerAge =
        some youngerBoundary
      rw [step.stack_sigma_eq]
      calc
        sigmaBoundary?
            (step.mergeStep.sigmaPrefix ++ [step.previousBoundary])
            youngerAge =
            sigmaBoundary? step.prepared.stackResult.after.sigma
              youngerAge :=
          sigmaBoundary?_popActive_of_lt step.middle_sigma_eq
            youngerAgeLtActive
        _ = some youngerBoundary := by
          simpa [PreparedStep.after] using youngerBoundaryLookup

private theorem tensorShadow_readyBucketFrontierExactWithGap
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    ReadyBucketFrontierExactWithGap step.tensorShadow
      step.previousBoundary step.payload := by
  have middleInvariant := step.prepared.schedulerInvariant invariant
  have prefixLengths :
      step.mergeStep.readyPrefix.length =
        step.mergeStep.sigmaPrefix.length := by
    have aligned := middleInvariant.stack_wellShaped.ready_aligned
    change step.prepared.stackResult.after.ready.length =
      step.prepared.stackResult.after.sigma.length at aligned
    rw [step.mergeStep.ready_eq, step.middle_sigma_eq] at aligned
    simp at aligned
    omega
  have previousSigmaLookup :
      step.prepared.after.stack.sigma[
          step.mergeStep.readyPrefix.length]? =
        some step.previousBoundary := by
    change step.prepared.stackResult.after.sigma[
        step.mergeStep.readyPrefix.length]? = _
    rw [step.middle_sigma_eq, prefixLengths]
    simp
  have activeSigmaLookup :
      step.prepared.after.stack.sigma[
          step.mergeStep.readyPrefix.length + 1]? =
        some step.prepared.stackResult.rawAge := by
    change step.prepared.stackResult.after.sigma[
        step.mergeStep.readyPrefix.length + 1]? = _
    rw [step.middle_sigma_eq, prefixLengths]
    simp
  have previousReadyLookup :
      step.prepared.after.stack.ready[
          step.mergeStep.readyPrefix.length]? =
        some step.mergeStep.previousReady := by
    change step.prepared.stackResult.after.ready[
        step.mergeStep.readyPrefix.length]? = _
    rw [step.mergeStep.ready_eq]
    simp
  have activeReadyLookup :
      step.prepared.after.stack.ready[
          step.mergeStep.readyPrefix.length + 1]? =
        some step.mergeStep.activeReady := by
    change step.prepared.stackResult.after.ready[
        step.mergeStep.readyPrefix.length + 1]? = _
    rw [step.mergeStep.ready_eq]
    simp
  rcases middleInvariant.ready_bucket_frontier_exact
      previousSigmaLookup previousReadyLookup with
    ⟨previousComponent, previousComponentLookup, previousExact⟩
  rcases middleInvariant.ready_bucket_frontier_exact
      activeSigmaLookup activeReadyLookup with
    ⟨activeComponent, activeComponentLookup, activeExact⟩
  change step.prepared.coreMarked.components[step.previousBoundary]? =
    some (some previousComponent) at previousComponentLookup
  change step.prepared.coreMarked.components[
      step.prepared.stackResult.rawAge]? =
    some (some activeComponent) at activeComponentLookup
  change (∀ vertex,
      vertex ∈ step.mergeStep.previousReady ↔
        vertex ∈ previousComponent.frontier ∧
          step.prepared.coreMarked.marks[vertex]? = some none)
    at previousExact
  change (∀ vertex,
      vertex ∈ step.mergeStep.activeReady ↔
        vertex ∈ activeComponent.frontier ∧
          step.prepared.coreMarked.marks[vertex]? = some none)
    at activeExact
  have tokenGuards :=
    UnificationState.unifyTokens?_success step.tensorStep.token_guard
  have left_context_of_frontier_unmarked :
      ∀ {vertex},
        vertex ∈ step.tensorStep.leftComponent.frontier →
        step.prepared.coreMarked.marks[vertex]? = some none →
        vertex ∈ step.tensorStep.leftContext := by
    intro vertex frontier unmarked
    have vertexNeLeft : vertex ≠ step.consumer.storedLeft := by
      intro same
      subst vertex
      unfold UnificationState.tokenAt? at tokenGuards
      rw [unmarked] at tokenGuards
      simp at tokenGuards
    exact Certificate.FirstOccurrencePick.mem_remaining_of_ne
      step.tensorStep.left_pick vertexNeLeft frontier
  have right_context_of_frontier_unmarked :
      ∀ {vertex},
        vertex ∈ step.tensorStep.rightComponent.frontier →
        step.prepared.coreMarked.marks[vertex]? = some none →
        vertex ∈ step.tensorStep.rightContext := by
    intro vertex frontier unmarked
    have vertexNeRight : vertex ≠ step.consumer.storedRight := by
      intro same
      subst vertex
      unfold UnificationState.tokenAt? at tokenGuards
      rw [unmarked] at tokenGuards
      simp at tokenGuards
    exact Certificate.FirstOccurrencePick.mem_remaining_of_ne
      step.tensorStep.right_pick vertexNeRight frontier
  have left_frontier_of_context :
      ∀ {vertex}, vertex ∈ step.tensorStep.leftContext →
        vertex ∈ step.tensorStep.leftComponent.frontier := by
    intro vertex membership
    exact (CutFreeDerivation.pick?_perm
      step.tensorStep.left_pick.positional).mem_iff.mpr (by
        simp [membership])
  have right_frontier_of_context :
      ∀ {vertex}, vertex ∈ step.tensorStep.rightContext →
        vertex ∈ step.tensorStep.rightComponent.frontier := by
    intro vertex membership
    exact (CutFreeDerivation.pick?_perm
      step.tensorStep.right_pick.positional).mem_iff.mpr (by
        simp [membership])
  intro position boundary bucket sigmaLookup readyLookup
  change step.stackAfter.sigma[position]? = some boundary at sigmaLookup
  change step.stackAfter.ready[position]? = some bucket at readyLookup
  rw [step.stack_sigma_eq] at sigmaLookup
  rw [step.stack_ready_eq] at readyLookup
  have positionBound :
      position <
        (step.mergeStep.readyPrefix ++
          [step.consumer.conclusion ::
            (step.payload ++
              (step.mergeStep.previousReady ++
                step.mergeStep.activeReady))]).length :=
    (List.getElem?_eq_some_iff.mp readyLookup).1
  by_cases inPrefix : position < step.mergeStep.readyPrefix.length
  · have sigmaPrefixBound :
        position < step.mergeStep.sigmaPrefix.length := by
      simpa [prefixLengths] using inPrefix
    have oldSigmaLookup :
        step.prepared.after.stack.sigma[position]? = some boundary := by
      change step.prepared.stackResult.after.sigma[position]? = some boundary
      rw [step.middle_sigma_eq,
        List.getElem?_append_left sigmaPrefixBound]
      rw [List.getElem?_append_left sigmaPrefixBound] at sigmaLookup
      exact sigmaLookup
    have oldReadyLookup :
        step.prepared.after.stack.ready[position]? = some bucket := by
      change step.prepared.stackResult.after.ready[position]? = some bucket
      rw [step.mergeStep.ready_eq,
        List.getElem?_append_left inPrefix]
      rw [List.getElem?_append_left inPrefix] at readyLookup
      exact readyLookup
    rcases middleInvariant.ready_bucket_frontier_exact
        oldSigmaLookup oldReadyLookup with
      ⟨component, componentLookup, exactMembership⟩
    change step.prepared.coreMarked.components[boundary]? =
      some (some component) at componentLookup
    change (∀ vertex, vertex ∈ bucket ↔
      vertex ∈ component.frontier ∧
        step.prepared.coreMarked.marks[vertex]? = some none)
      at exactMembership
    have boundaryInPrefix : boundary ∈ step.mergeStep.sigmaPrefix :=
      List.mem_of_getElem? (by
        have lookup := oldSigmaLookup
        change step.prepared.stackResult.after.sigma[position]? =
          some boundary at lookup
        rw [step.middle_sigma_eq,
          List.getElem?_append_left sigmaPrefixBound] at lookup
        exact lookup)
    have increasing :
        (step.mergeStep.sigmaPrefix ++
          [step.previousBoundary,
            step.prepared.stackResult.rawAge]).Pairwise (· < ·) := by
      have oldIncreasing :=
        middleInvariant.stack_wellShaped.sigma_partition.strictIncreasing
      change step.prepared.stackResult.after.sigma.Pairwise (· < ·)
        at oldIncreasing
      rw [step.middle_sigma_eq] at oldIncreasing
      exact oldIncreasing
    have boundaryLtPrevious : boundary < step.previousBoundary :=
      (List.pairwise_append.mp increasing).2.2
        boundary boundaryInPrefix step.previousBoundary (by simp)
    have previousNeBoundary : step.previousBoundary ≠ boundary :=
      Nat.ne_of_gt boundaryLtPrevious
    have activeNeBoundary :
        step.prepared.stackResult.rawAge ≠ boundary :=
      Nat.ne_of_gt
        (Nat.lt_trans boundaryLtPrevious step.previous_lt_active)
    refine ⟨component, ?_, ?_⟩
    · change step.coreTensor.components[boundary]? = some (some component)
      rw [step.tensor_components_eq,
        Array.getElem?_setIfInBounds_ne activeNeBoundary,
        Array.getElem?_setIfInBounds_ne previousNeBoundary]
      exact componentLookup
    · intro vertex
      change vertex ∈ bucket ↔
        (vertex ∈ component.frontier ∧
          step.coreTensor.marks[vertex]? = some none) ∨
        (boundary = step.previousBoundary ∧ vertex ∈ step.payload)
      rw [step.tensor_core_marks_eq]
      simpa [Nat.ne_of_lt boundaryLtPrevious] using exactMembership vertex
  · have positionTop :
        position = step.mergeStep.readyPrefix.length := by
      simp at positionBound
      omega
    subst position
    have boundaryEq : boundary = step.previousBoundary := by
      rw [prefixLengths] at sigmaLookup
      simp at sigmaLookup
      exact sigmaLookup.symm
    have bucketEq :
        bucket = step.consumer.conclusion ::
          (step.payload ++
            (step.mergeStep.previousReady ++ step.mergeStep.activeReady)) := by
      simp at readyLookup
      exact readyLookup.symm
    subst boundary
    subst bucket
    refine ⟨step.tensorComponent, ?_, ?_⟩
    · change step.coreTensor.components[step.previousBoundary]? =
        some (some step.tensorComponent)
      rw [step.tensor_components_eq,
        Array.getElem?_setIfInBounds_ne
          (Nat.ne_of_gt step.previous_lt_active)]
      simp [step.previous_bound invariant]
    · intro vertex
      change vertex ∈ step.consumer.conclusion ::
            (step.payload ++
              (step.mergeStep.previousReady ++ step.mergeStep.activeReady)) ↔
        (vertex ∈ step.tensorComponent.frontier ∧
          step.coreTensor.marks[vertex]? = some none) ∨
        (step.previousBoundary = step.previousBoundary ∧
          vertex ∈ step.payload)
      rw [step.tensor_core_marks_eq]
      rcases step.tokens_eq_adjacent with orientation | orientation
      · have rightRaw := step.right_component_raw invariant
        have leftRaw := step.left_component_raw invariant
        rw [orientation.2.2] at rightRaw
        rw [orientation.2.1] at leftRaw
        have previousComponentEq :
            previousComponent = step.tensorStep.rightComponent :=
          Option.some.inj (Option.some.inj
            (previousComponentLookup.symm.trans rightRaw))
        have activeComponentEq :
            activeComponent = step.tensorStep.leftComponent :=
          Option.some.inj (Option.some.inj
            (activeComponentLookup.symm.trans leftRaw))
        subst previousComponent
        subst activeComponent
        simp only [tensorComponent, eq_self, true_and]
        change vertex ∈ step.consumer.conclusion ::
            (step.payload ++
              (step.mergeStep.previousReady ++ step.mergeStep.activeReady)) ↔
          (vertex ∈ step.consumer.conclusion ::
              (step.tensorStep.leftContext ++
                step.tensorStep.rightContext) ∧
            step.prepared.coreMarked.marks[vertex]? = some none) ∨
          vertex ∈ step.payload
        constructor
        · intro membership
          simp only [List.mem_cons, List.mem_append] at membership ⊢
          rcases membership with rfl | inPayload | inPrevious | inActive
          · exact Or.inl ⟨Or.inl rfl, tokenGuards.1⟩
          · exact Or.inr inPayload
          · have facts := (previousExact vertex).mp inPrevious
            exact Or.inl ⟨Or.inr (Or.inr
              (right_context_of_frontier_unmarked facts.1 facts.2)),
              facts.2⟩
          · have facts := (activeExact vertex).mp inActive
            exact Or.inl ⟨Or.inr (Or.inl
              (left_context_of_frontier_unmarked facts.1 facts.2)),
              facts.2⟩
        · intro target
          simp only [List.mem_cons, List.mem_append] at target ⊢
          rcases target with ⟨frontier, unmarked⟩ | inPayload
          · rcases frontier with rfl | inLeft | inRight
            · exact Or.inl rfl
            · exact Or.inr (Or.inr (Or.inr ((activeExact vertex).mpr
                ⟨left_frontier_of_context inLeft, unmarked⟩)))
            · exact Or.inr (Or.inr (Or.inl ((previousExact vertex).mpr
                ⟨right_frontier_of_context inRight, unmarked⟩)))
          · exact Or.inr (Or.inl inPayload)
      · have leftRaw := step.left_component_raw invariant
        have rightRaw := step.right_component_raw invariant
        rw [orientation.2.1] at leftRaw
        rw [orientation.2.2] at rightRaw
        have previousComponentEq :
            previousComponent = step.tensorStep.leftComponent :=
          Option.some.inj (Option.some.inj
            (previousComponentLookup.symm.trans leftRaw))
        have activeComponentEq :
            activeComponent = step.tensorStep.rightComponent :=
          Option.some.inj (Option.some.inj
            (activeComponentLookup.symm.trans rightRaw))
        subst previousComponent
        subst activeComponent
        simp only [tensorComponent, eq_self, true_and]
        change vertex ∈ step.consumer.conclusion ::
            (step.payload ++
              (step.mergeStep.previousReady ++ step.mergeStep.activeReady)) ↔
          (vertex ∈ step.consumer.conclusion ::
              (step.tensorStep.leftContext ++
                step.tensorStep.rightContext) ∧
            step.prepared.coreMarked.marks[vertex]? = some none) ∨
          vertex ∈ step.payload
        constructor
        · intro membership
          simp only [List.mem_cons, List.mem_append] at membership ⊢
          rcases membership with rfl | inPayload | inPrevious | inActive
          · exact Or.inl ⟨Or.inl rfl, tokenGuards.1⟩
          · exact Or.inr inPayload
          · have facts := (previousExact vertex).mp inPrevious
            exact Or.inl ⟨Or.inr (Or.inl
              (left_context_of_frontier_unmarked facts.1 facts.2)),
              facts.2⟩
          · have facts := (activeExact vertex).mp inActive
            exact Or.inl ⟨Or.inr (Or.inr
              (right_context_of_frontier_unmarked facts.1 facts.2)),
              facts.2⟩
        · intro target
          simp only [List.mem_cons, List.mem_append] at target ⊢
          rcases target with ⟨frontier, unmarked⟩ | inPayload
          · rcases frontier with rfl | inLeft | inRight
            · exact Or.inl rfl
            · exact Or.inr (Or.inr (Or.inl ((previousExact vertex).mpr
                ⟨left_frontier_of_context inLeft, unmarked⟩)))
            · exact Or.inr (Or.inr (Or.inr ((activeExact vertex).mpr
                ⟨right_frontier_of_context inRight, unmarked⟩)))
          · exact Or.inr (Or.inl inPayload)

private theorem tensor_foldl_add_weight
    {alpha : Type} (weight : alpha → Nat) (values : List alpha)
    (initial : Nat) :
    values.foldl (fun total value => total + weight value) initial =
      initial + (values.map weight).sum := by
  induction values generalizing initial with
  | nil => simp
  | cons head tail induction =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [induction]
      omega

private theorem tensor_map_sum_set_balance
    {alpha : Type} {values : List alpha} {index : Nat}
    {oldValue newValue : alpha}
    (weight : alpha → Nat)
    (lookup : values[index]? = some oldValue) :
    ((values.set index newValue).map weight).sum + weight oldValue =
      (values.map weight).sum + weight newValue := by
  induction values generalizing index with
  | nil => simp at lookup
  | cons head tail induction =>
      cases index with
      | zero =>
          have headEq : head = oldValue := by simpa using lookup
          subst head
          simp
          omega
      | succ prior =>
          simp only [List.getElem?_cons_succ] at lookup
          simp only [List.set, List.map_cons, List.sum_cons]
          have inner := induction lookup
          omega

private theorem tensor_map_sum_set_merge_clear
    {alpha : Type} {values : List alpha}
    {survivor retired : Nat}
    {survivorValue retiredValue mergedValue clearedValue : alpha}
    (weight : alpha → Nat)
    (different : survivor ≠ retired)
    (survivorLookup : values[survivor]? = some survivorValue)
    (retiredLookup : values[retired]? = some retiredValue)
    (clearedWeight : weight clearedValue = 0)
    (mergedWeight :
      weight mergedValue =
        weight survivorValue + weight retiredValue + 1) :
    ((((values.set survivor mergedValue).set retired clearedValue).map
        weight).sum) =
      (values.map weight).sum + 1 := by
  have retiredAfter :
      (values.set survivor mergedValue)[retired]? =
        some retiredValue := by
    rw [List.getElem?_set_ne different]
    exact retiredLookup
  have first := tensor_map_sum_set_balance weight survivorLookup
    (newValue := mergedValue)
  have second := tensor_map_sum_set_balance weight retiredAfter
    (newValue := clearedValue)
  rw [clearedWeight] at second
  omega

private theorem tensorShadow_firedCounterExact
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    FiredCounterExact step.tensorShadow := by
  let weight : Option UnificationComponent → Nat := fun cell =>
    (cell.map UnificationComponent.connectiveCount).getD 0
  let values := step.prepared.coreMarked.components.toList
  have middleInvariant := step.prepared.schedulerInvariant invariant
  have leftLookup :
      values[step.tensorStep.leftToken]? =
        some (some step.tensorStep.leftComponent) := by
    simpa [values] using step.left_component_raw invariant
  have rightLookup :
      values[step.tensorStep.rightToken]? =
        some (some step.tensorStep.rightComponent) := by
    simpa [values] using step.right_component_raw invariant
  have sumIncrease :
      (((values.set step.previousBoundary
          (some step.tensorComponent)).set
          step.prepared.stackResult.rawAge none).map weight).sum =
        (values.map weight).sum + 1 := by
    rcases step.tokens_eq_adjacent with orientation | orientation
    · rw [orientation.2.1] at leftLookup
      rw [orientation.2.2] at rightLookup
      apply tensor_map_sum_set_merge_clear weight
        (Nat.ne_of_lt step.previous_lt_active)
        rightLookup leftLookup
      · simp [weight]
      · simp [weight, tensorComponent,
          UnificationComponent.connectiveCount,
          CutFreeDerivation.connectiveCount]
        omega
    · rw [orientation.2.1] at leftLookup
      rw [orientation.2.2] at rightLookup
      apply tensor_map_sum_set_merge_clear weight
        (Nat.ne_of_lt step.previous_lt_active)
        leftLookup rightLookup
      · simp [weight]
      · simp [weight, tensorComponent,
          UnificationComponent.connectiveCount,
          CutFreeDerivation.connectiveCount]
  have totalIncrease :
      ((values.set step.previousBoundary
          (some step.tensorComponent)).set
          step.prepared.stackResult.rawAge none).foldl
          (fun total cell => total + weight cell) 0 =
        values.foldl
          (fun total cell => total + weight cell) 0 + 1 := by
    rw [tensor_foldl_add_weight, tensor_foldl_add_weight]
    simpa using sumIncrease
  have middleCounter := middleInvariant.fired_counter_exact
  unfold FiredCounterExact UnificationState.liveConnectiveCount at middleCounter
  change step.prepared.coreMarked.firedConnectives =
    step.prepared.coreMarked.components.toList.foldl
      (fun total cell => total +
        (cell.map UnificationComponent.connectiveCount).getD 0) 0
    at middleCounter
  unfold FiredCounterExact tensorShadow
  rw [step.tensorStep.after_eq, step.max_token_eq, step.min_token_eq]
  unfold UnificationState.liveConnectiveCount
  rw [Array.toList_setIfInBounds, Array.toList_setIfInBounds]
  change step.prepared.coreMarked.firedConnectives + 1 =
    ((values.set step.previousBoundary
      (some step.tensorComponent)).set
      step.prepared.stackResult.rawAge none).foldl
      (fun total cell => total + weight cell) 0
  rw [totalIncrease]
  exact congrArg (fun count => count + 1) middleCounter

private theorem tensorShadow_representative
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after)
    (invariant : SchedulerInvariant certificate before)
    {rawAge : RawTokenAge}
    (rawBound : rawAge < step.prepared.coreMarked.parents.size) :
    step.tensorShadow.core.representative rawAge =
      if step.prepared.coreMarked.representative rawAge =
          step.prepared.stackResult.rawAge then
        step.previousBoundary
      else
        step.prepared.coreMarked.representative rawAge := by
  have middleInvariant := step.prepared.schedulerInvariant invariant
  have previousParentBound :
      step.previousBoundary < step.prepared.coreMarked.parents.size := by
    have aligned : step.prepared.coreMarked.components.size =
        step.prepared.coreMarked.parents.size := by
      simpa [PreparedStep.after] using
        middleInvariant.core_carriers_aligned
    rw [← aligned]
    exact step.previous_bound invariant
  have activeParentBound :
      step.prepared.stackResult.rawAge <
        step.prepared.coreMarked.parents.size := by
    have aligned : step.prepared.coreMarked.components.size =
        step.prepared.coreMarked.parents.size := by
      simpa [PreparedStep.after] using
        middleInvariant.core_carriers_aligned
    rw [← aligned]
    exact step.active_bound invariant
  have previousRoot :
      step.prepared.coreMarked.representative step.previousBoundary =
        step.previousBoundary := by
    rcases step.tokens_eq_adjacent with orientation | orientation
    · rw [← orientation.2.2]
      exact step.right_root invariant
    · rw [← orientation.2.1]
      exact step.left_root invariant
  have activeRoot :
      step.prepared.coreMarked.representative
          step.prepared.stackResult.rawAge =
        step.prepared.stackResult.rawAge := by
    rcases step.tokens_eq_adjacent with orientation | orientation
    · rw [← orientation.2.1]
      exact step.left_root invariant
    · rw [← orientation.2.2]
      exact step.right_root invariant
  have middleOrdered : step.prepared.coreMarked.OrderedParents := by
    intro token parent lookup
    exact middleInvariant.core_orderedParents lookup
  change step.coreTensor.representative rawAge = _
  calc
    step.coreTensor.representative rawAge =
        (step.prepared.coreMarked.setParent
          step.prepared.stackResult.rawAge
          step.previousBoundary).representative rawAge := by
      unfold UnificationState.representative
      rw [step.tensorStep.after_eq,
        step.max_token_eq, step.min_token_eq]
      rfl
    _ = _ :=
      middleOrdered.setParent_representative
        previousParentBound activeParentBound
        step.previous_lt_active previousRoot activeRoot rawBound

private theorem tensorShadow_componentAtPrevious
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    step.tensorShadow.core.componentAt? step.previousBoundary =
      some step.tensorComponent := by
  have middleInvariant := step.prepared.schedulerInvariant invariant
  have previousParentBound :
      step.previousBoundary < step.prepared.coreMarked.parents.size := by
    have aligned : step.prepared.coreMarked.components.size =
        step.prepared.coreMarked.parents.size := by
      simpa [PreparedStep.after] using
        middleInvariant.core_carriers_aligned
    rw [← aligned]
    exact step.previous_bound invariant
  have previousRootMiddle :
      step.prepared.coreMarked.representative step.previousBoundary =
        step.previousBoundary := by
    rcases step.tokens_eq_adjacent with orientation | orientation
    · rw [← orientation.2.2]
      exact step.right_root invariant
    · rw [← orientation.2.1]
      exact step.left_root invariant
  have previousRootAfter :
      step.tensorShadow.core.representative step.previousBoundary =
        step.previousBoundary := by
    rw [step.tensorShadow_representative invariant previousParentBound,
      previousRootMiddle]
    simp [Nat.ne_of_lt step.previous_lt_active]
  unfold UnificationState.componentAt?
  rw [previousRootAfter]
  change (do
    let component ← step.coreTensor.components[step.previousBoundary]?
    component) = some step.tensorComponent
  rw [step.tensor_components_eq]
  rw [Array.getElem?_setIfInBounds_ne
    (Nat.ne_of_gt step.previous_lt_active)]
  simp [step.previous_bound invariant]

private theorem tensorConclusionMemReady
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after) :
    step.consumer.conclusion ∈ step.tensorShadow.stack.ready.flatten := by
  change step.consumer.conclusion ∈ step.stackAfter.ready.flatten
  rw [step.stack_ready_eq]
  apply List.mem_flatten.mpr
  exact ⟨step.consumer.conclusion ::
      (step.payload ++
        (step.mergeStep.previousReady ++ step.mergeStep.activeReady)),
    by simp, by simp⟩

private theorem oldReadySubsetTensorShadow
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after)
    {vertex : Vertex}
    (membership : vertex ∈ step.prepared.after.stack.ready.flatten) :
    vertex ∈ step.tensorShadow.stack.ready.flatten := by
  change vertex ∈
    step.prepared.stackResult.after.ready.flatten at membership
  rw [step.mergeStep.ready_eq] at membership
  change vertex ∈ step.stackAfter.ready.flatten
  rw [step.stack_ready_eq]
  simp only [List.flatten_append, List.flatten_cons,
    List.flatten_nil, List.append_nil, List.mem_append,
    List.mem_cons] at membership ⊢
  rcases membership with inPrefix | inPrevious | inActive
  · exact Or.inl inPrefix
  · exact Or.inr (Or.inr (Or.inr (Or.inl inPrevious)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr inActive)))

private theorem tensorShadow_pendingPremisesCoveredExceptReady
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    PendingPremisesCoveredExceptReady certificate step.tensorShadow := by
  have middleInvariant := step.prepared.schedulerInvariant invariant
  intro link linkMembership
  cases link with
  | «axiom» left right => trivial
  | tensor left right conclusion
  | «par» left right conclusion =>
      intro conclusionUnmarked conclusionNotReady premise token
        premiseMembership tokenAt
      have conclusionNeCurrent :
          conclusion ≠ step.consumer.conclusion := by
        intro same
        subst conclusion
        exact conclusionNotReady step.tensorConclusionMemReady
      have middleConclusionUnmarked :
          step.prepared.after.core.marks[conclusion]? = some none := by
        change step.prepared.coreMarked.marks[conclusion]? = some none
        change step.coreTensor.marks[conclusion]? = some none
          at conclusionUnmarked
        rw [step.tensor_core_marks_eq] at conclusionUnmarked
        exact conclusionUnmarked
      have middleConclusionNotReady :
          conclusion ∉ step.prepared.after.stack.ready.flatten := by
        intro membership
        exact conclusionNotReady (step.oldReadySubsetTensorShadow membership)
      rcases step.tensorShadow.core.tokenAt?_some_witness tokenAt with
        ⟨rawAge, assignedAfter, representativeAfter⟩
      have assignedMiddle :
          step.prepared.coreMarked.assignedToken? premise =
            some rawAge := by
        unfold UnificationState.assignedToken? at assignedAfter ⊢
        change step.coreTensor.marks[premise]?.join = some rawAge
          at assignedAfter
        rw [step.tensor_core_marks_eq] at assignedAfter
        exact assignedAfter
      let oldToken :=
        step.prepared.coreMarked.representative rawAge
      have middleTokenAt :
          step.prepared.after.core.tokenAt? premise =
            some oldToken := by
        change step.prepared.coreMarked.tokenAt? premise = some oldToken
        unfold UnificationState.tokenAt?
        rw [UnificationState.assignedToken?_some_raw assignedMiddle]
        rfl
      have rawBound :
          rawAge < step.prepared.coreMarked.parents.size :=
        middleInvariant.core_abstractable.markedTokenBound assignedMiddle
      have tokenTransport :
          token =
            if oldToken = step.prepared.stackResult.rawAge then
              step.previousBoundary
            else oldToken := by
        have transported := step.tensorShadow_representative invariant rawBound
        rw [representativeAfter] at transported
        exact transported
      rcases middleInvariant.pending_premises_covered_except_ready
          linkMembership middleConclusionUnmarked
          middleConclusionNotReady premiseMembership middleTokenAt with
        ⟨component, componentLookup, premiseFrontier⟩
      change step.prepared.coreMarked.componentAt? oldToken =
        some component at componentLookup
      have premiseNeLeft :
          premise ≠ step.consumer.storedLeft := by
        intro same
        subst premise
        have sameLink :=
          UnificationState.StructurallyWellFormed.parentLink_unique
            invariant.structural
            (premise := step.consumer.storedLeft)
            (first := .tensor step.consumer.storedLeft
              step.consumer.storedRight step.consumer.conclusion)
            (List.mem_of_getElem? step.submitted_tensor)
            (by simp [Link.premises]) linkMembership
            (by simpa [Link.premises] using premiseMembership)
        cases sameLink <;> exact conclusionNeCurrent rfl
      have premiseNeRight :
          premise ≠ step.consumer.storedRight := by
        intro same
        subst premise
        have sameLink :=
          UnificationState.StructurallyWellFormed.parentLink_unique
            invariant.structural
            (premise := step.consumer.storedRight)
            (first := .tensor step.consumer.storedLeft
              step.consumer.storedRight step.consumer.conclusion)
            (List.mem_of_getElem? step.submitted_tensor)
            (by simp [Link.premises]) linkMembership
            (by simpa [Link.premises] using premiseMembership)
        cases sameLink <;> exact conclusionNeCurrent rfl
      have oldRoot :
          step.prepared.coreMarked.representative oldToken = oldToken :=
        middleInvariant.core_abstractable.tokenAt?_root middleTokenAt
      by_cases oldIsLeft : oldToken = step.tensorStep.leftToken
      · have rawLookup :=
          UnificationState.componentAt?_some_raw componentLookup
        rw [oldRoot, oldIsLeft] at rawLookup
        have componentEq : component = step.tensorStep.leftComponent :=
          Option.some.inj (Option.some.inj
            (rawLookup.symm.trans (step.left_component_raw invariant)))
        subst component
        have inContext :=
          Certificate.FirstOccurrencePick.mem_remaining_of_ne
            step.tensorStep.left_pick premiseNeLeft premiseFrontier
        have tokenPrevious : token = step.previousBoundary := by
          rw [tokenTransport, oldIsLeft]
          rcases step.tokens_eq_adjacent with orientation | orientation
          · rw [orientation.2.1]
            simp
          · rw [orientation.2.1]
            simp [Nat.ne_of_lt step.previous_lt_active]
        refine ⟨step.tensorComponent, ?_,
          by simp [tensorComponent, inContext]⟩
        rw [tokenPrevious]
        exact step.tensorShadow_componentAtPrevious invariant
      · by_cases oldIsRight : oldToken = step.tensorStep.rightToken
        · have rawLookup :=
            UnificationState.componentAt?_some_raw componentLookup
          rw [oldRoot, oldIsRight] at rawLookup
          have componentEq : component = step.tensorStep.rightComponent :=
            Option.some.inj (Option.some.inj
              (rawLookup.symm.trans (step.right_component_raw invariant)))
          subst component
          have inContext :=
            Certificate.FirstOccurrencePick.mem_remaining_of_ne
              step.tensorStep.right_pick premiseNeRight premiseFrontier
          have tokenPrevious : token = step.previousBoundary := by
            rw [tokenTransport, oldIsRight]
            rcases step.tokens_eq_adjacent with orientation | orientation
            · rw [orientation.2.2]
              simp [Nat.ne_of_lt step.previous_lt_active]
            · rw [orientation.2.2]
              simp
          refine ⟨step.tensorComponent, ?_,
            by simp [tensorComponent, inContext]⟩
          rw [tokenPrevious]
          exact step.tensorShadow_componentAtPrevious invariant
        · have oldNeActive :
              oldToken ≠ step.prepared.stackResult.rawAge := by
            intro same
            rcases step.tokens_eq_adjacent with orientation | orientation
            · exact oldIsLeft (same.trans orientation.2.1.symm)
            · exact oldIsRight (same.trans orientation.2.2.symm)
          have oldNePrevious : oldToken ≠ step.previousBoundary := by
            intro same
            rcases step.tokens_eq_adjacent with orientation | orientation
            · exact oldIsRight (same.trans orientation.2.2.symm)
            · exact oldIsLeft (same.trans orientation.2.1.symm)
          have tokenOld : token = oldToken := by
            simpa [oldNeActive] using tokenTransport
          refine ⟨component, ?_, premiseFrontier⟩
          have oldParentBound :
              oldToken < step.prepared.coreMarked.parents.size :=
            middleInvariant.core_abstractable.tokenAt?_bound middleTokenAt
          have afterOldRoot :
              step.tensorShadow.core.representative oldToken = oldToken := by
            rw [step.tensorShadow_representative invariant oldParentBound,
              oldRoot]
            simp [oldNeActive]
          rw [tokenOld]
          unfold UnificationState.componentAt? at componentLookup ⊢
          rw [oldRoot] at componentLookup
          rw [afterOldRoot]
          change (do
            let cell ← step.coreTensor.components[oldToken]?
            cell) = some component
          rw [step.tensor_components_eq]
          rw [Array.getElem?_setIfInBounds_ne (Ne.symm oldNeActive),
            Array.getElem?_setIfInBounds_ne (Ne.symm oldNePrevious)]
          exact componentLookup

/-- The actual post-drain tensor shadow satisfies the transient invariant with
the complete stored waiting payload as its initial gap.  Every field is
derived from the full input scheduler invariant and the exact executable
tensor/merge witnesses; no reachability or history hypothesis is used. -/
private theorem tensorShadow_initialGap
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    UnifyPayloadGapInvariant certificate step.tensorShadow
      step.previousBoundary step.payload := {
  toReservationInvariant := step.tensorShadow_reservationInvariant invariant
  structural := invariant.structural
  component_domain_exact :=
    step.tensorShadow_componentDomainExact invariant
  component_forest_provenance :=
    step.tensorShadow_componentForestProvenance invariant
  live_frontiers_nodup := step.tensorShadow_liveFrontiersNodup invariant
  queued_vertices_nodup := step.tensorShadow_queuedVerticesNodup invariant
  queued_vertices_unmarked :=
    step.tensorShadow_queuedVerticesUnmarked invariant
  produced_premises_marked :=
    step.tensorShadow_producedPremisesMarked invariant
  waiting_span_exact := step.tensorShadow_waitingSpanExact invariant
  pending_premises_covered_except_ready :=
    step.tensorShadow_pendingPremisesCoveredExceptReady invariant
  fired_counter_exact := step.tensorShadow_firedCounterExact invariant
  gap_boundary_top := by
    change step.stackAfter.sigma.getLast? = some step.previousBoundary
    rw [step.stack_sigma_eq]
    simp
  ready_bucket_frontier_exact_with_gap :=
    step.tensorShadow_readyBucketFrontierExactWithGap invariant
  gap_nodup := step.tensorShadow_gapNodup
  gap_unmarked := step.tensorShadow_gapUnmarked invariant
  gap_not_produced := step.tensorShadow_gapNotProduced invariant
  gap_premises_at_boundary :=
    step.tensorShadow_gapPremisesAtBoundary invariant }

/-- A successful atomic arbitrary-payload tensor-plus-stored-par-fold
unification preserves the complete occurrence-exact state-only scheduler
invariant.

The proof uses a fixed-final-stack shadow whose gap is exactly the unactivated
payload suffix.  It does not assign `SchedulerInvariant` to the physically
misaligned tensor/fold intermediates, assume `InitNewHistory`, or claim rule
applicability, dispatcher progress, global reachability, completeness, or
complexity. -/
theorem schedulerInvariant
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyPayloadStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    SchedulerInvariant certificate after := by
  have initial := step.tensorShadow_initialGap invariant
  have closed :=
    UnifyPayloadGapInvariant.WaitingParActivationFoldStep.closeGap
      step.activationFold (shadow := step.tensorShadow) initial
  rw [step.output_eq]
  simpa [tensorShadow] using closed

end UnifyPayloadStep

/-- Executable arbitrary-payload `unifyPayload?` success preserves the
complete occurrence-exact scheduler invariant.  This is a preservation
corollary only; totality and dispatcher progress remain separate obligations.
-/
theorem unifyPayload?_schedulerInvariant
    {certificate : Certificate} {before after : ReservationState}
    (invariant : SchedulerInvariant certificate before)
    (equation :
      unifyPayload? certificate before invariant.toReservationInvariant =
        some after) :
    SchedulerInvariant certificate after := by
  rcases (unifyPayload?_some_iff invariant.toReservationInvariant).mp
      equation with ⟨step⟩
  exact step.schedulerInvariant invariant

end SequentialFigure7

end ProofNetIR
