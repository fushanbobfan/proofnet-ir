import ProofNetIR.SequentialFigure7Rules
import ProofNetIR.SequentialFigure7New
import ProofNetIR.SequentialFigure7UnifyOne
import ProofNetIR.SequentialComponentProvenance

namespace ProofNetIR

/-!
# State-based Figure-7 scheduler invariant

This module adds the first non-circular semantic invariant for the delayed
Figure-7 state.  Every field is a predicate of the current certificate and
current executable state; no reachability history or future dispatcher
success appears in its definition.

The invariant deliberately separates ready work from waiting promises.
Ready buckets are the raw-unmarked frontiers of the live production
components at the corresponding `sigma` boundaries.  A waiting payload is
not yet a fired production component: it records an exact submitted par whose
premises have already been marked in two ordered scheduler components.
Consequently the connective counter is counted from the actual live
derivation trees, not from ready/waiting list membership.

Guerrini's paper uses sets for ready and waiting buckets.  The executable
lists retain deterministic order, but the semantic fields below use
membership only.  The current preservation layer covers the common prepared
prefix, `concl`, `nop`, operational `new`, successful local `forward`, and
successful local `wait`.  It also covers bounded tensor unification when the
drained waiting payload is empty, and strict singleton tensor-plus-par
unification when that payload is exactly one conclusion.  It does not prove
arbitrary nonempty/full `unify`, dispatcher applicability or totality,
full-rule reachability, progress, or completeness.
-/

namespace CutFreeDerivation

/-- Number of multiplicative connective constructors in a derivation tree.
Exchange contributes no logical connective. -/
def connectiveCount : CutFreeDerivation → Nat
  | .axiom _ _ => 0
  | .tensor _ _ left right =>
      left.connectiveCount + right.connectiveCount + 1
  | .par _ _ premise => premise.connectiveCount + 1
  | .exchange _ premise => premise.connectiveCount

end CutFreeDerivation

namespace UnificationComponent

/-- Number of already constructed multiplicative connectives in one live
production component. -/
def connectiveCount (component : UnificationComponent) : Nat :=
  component.tree.connectiveCount

end UnificationComponent

namespace UnificationState

/-- Frontier occurrences of every live component slot, in raw component-array
order. Retired slots contribute no occurrences. -/
def liveFrontierVertices (state : UnificationState) : List Vertex :=
  state.components.toList.flatMap
    (fun cell =>
      (cell.map UnificationComponent.frontier).getD [])

/-- Total number of constructed multiplicative connectives across all live
component slots.  Retired slots contribute zero. -/
def liveConnectiveCount (state : UnificationState) : Nat :=
  state.components.toList.foldl
    (fun total cell =>
      total +
        (cell.map UnificationComponent.connectiveCount).getD 0)
    0

end UnificationState

namespace Certificate

/-- Reserving an axiom preserves the exact token lookup of every existing
occurrence. -/
theorem reserveAxiomAt?_tokenAt_eq
    {certificate : Certificate} {before after : UnificationState}
    {linkIndex : Nat}
    (ordered : before.OrderedParents)
    (equation : certificate.reserveAxiomAt? before linkIndex = some after)
    (vertex : Vertex) :
    after.tokenAt? vertex = before.tokenAt? vertex := by
  rcases certificate.reserveAxiomAt?_exact equation with
    ⟨left, right, component, linkLookup, ready, componentLookup,
      frontier, marksEq, parentsEq, componentsEq, counterEq, firedEq⟩
  unfold UnificationState.tokenAt?
  rw [marksEq]
  cases before.marks[vertex]? with
  | none => rfl
  | some assigned =>
      cases assigned with
      | none => rfl
      | some rawAge =>
          change some (after.representative rawAge) =
            some (before.representative rawAge)
          exact congrArg some
            (certificate.reserveAxiomAt?_old_representative ordered equation)

/-- A previously live component remains available through token lookup after
an axiom is appended. -/
theorem reserveAxiomAt?_componentAt?_of_some
    {certificate : Certificate} {before after : UnificationState}
    {linkIndex token : Nat} {component : UnificationComponent}
    (ordered : before.OrderedParents)
    (equation : certificate.reserveAxiomAt? before linkIndex = some after)
    (lookup : before.componentAt? token = some component) :
    after.componentAt? token = some component := by
  rcases certificate.reserveAxiomAt?_exact equation with
    ⟨left, right, newComponent, linkLookup, ready, componentLookup,
      frontier, marksEq, parentsEq, componentsEq, counterEq, firedEq⟩
  have rawLookup := UnificationState.componentAt?_some_raw lookup
  have rawBound := (Array.getElem?_eq_some_iff.mp rawLookup).1
  have afterRawLookup :
      after.components[after.representative token]? =
        some (some component) := by
    rw [certificate.reserveAxiomAt?_old_representative ordered equation,
      componentsEq]
    simpa [Array.getElem?_push, Nat.ne_of_lt rawBound] using rawLookup
  unfold UnificationState.componentAt?
  rw [afterRawLookup]
  rfl

end Certificate

namespace SequentialSchedulerBridge

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState

private theorem flatMap_replicate_waitingUndefined
    (count : Nat) :
    (List.replicate count WaitingCell.undefined).flatMap
        WaitingCell.vertices = [] := by
  induction count with
  | zero => rfl
  | succ count induction =>
      simp [List.replicate_succ, WaitingCell.vertices, induction]

private theorem empty_waitingVertices (carrierSize : Nat) :
    (SequentialStackState.empty carrierSize).waitingVertices = [] := by
  unfold SequentialStackState.waitingVertices
    SequentialStackState.empty
  exact flatMap_replicate_waitingUndefined carrierSize

private theorem empty_queuedVertices (carrierSize : Nat) :
    (SequentialStackState.empty carrierSize).queuedVertices = [] := by
  unfold SequentialStackState.queuedVertices
  rw [empty_waitingVertices]
  rfl

private theorem StructurallyWellFormed.axiomEndpointFormula_of_mem
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {left right vertex : Vertex}
    (membership : .axiom left right ∈ certificate.links)
    (endpoint : vertex = left ∨ vertex = right) :
    ∃ name positive,
      certificate.formula? vertex = some (.atom name positive) := by
  have wellFormed :
      certificate.LinkWellFormed (.axiom left right) :=
    structural.2.2.2.2.1 _ membership
  rcases wellFormed with ⟨_, _, _, typing⟩
  cases leftEquation : certificate.formula? left with
  | none =>
      simp [leftEquation] at typing
  | some leftFormula =>
      cases leftFormula with
      | tensor first second =>
          simp [leftEquation] at typing
      | «par» first second =>
          simp [leftEquation] at typing
      | atom name positive =>
          cases rightEquation : certificate.formula? right with
          | none =>
              simp [leftEquation, rightEquation] at typing
          | some rightFormula =>
              simp [leftEquation, rightEquation] at typing
              rcases endpoint with rfl | rfl
              · exact ⟨name, positive, by simpa using leftEquation⟩
              · subst rightFormula
                exact ⟨name, !positive, by
                  simpa [Formula.dual] using rightEquation⟩

/-- Live raw component slots are exactly the current `sigma` boundaries.

The statement uses raw component-array slots rather than `componentAt?`, whose
representative lookup would make the reverse direction tautological after a
union. -/
def ComponentDomainExact (state : ReservationState) : Prop :=
  ∀ token,
    (∃ component,
      state.core.components[token]? = some (some component)) ↔
      token ∈ state.stack.sigma

/-- No formula occurrence appears in two live production frontiers (or twice
inside one live frontier). -/
def LiveFrontiersNodup (state : ReservationState) : Prop :=
  state.core.liveFrontierVertices.Nodup

/-- Every aligned ready bucket is exactly the raw-unmarked frontier of the
live component stored at its matching `sigma` boundary.

This is an extensional membership statement.  It intentionally does not
identify the deterministic list order with the set order used in the paper.
-/
def ReadyBucketFrontierExact (state : ReservationState) : Prop :=
  ∀ {position boundary : Nat} {bucket : List Vertex},
    state.stack.sigma[position]? = some boundary →
    state.stack.ready[position]? = some bucket →
    ∃ component : UnificationComponent,
      state.core.components[boundary]? = some (some component) ∧
      ∀ vertex,
        vertex ∈ bucket ↔
          vertex ∈ component.frontier ∧
            state.core.marks[vertex]? = some none

/-- Every scheduler-queued occurrence appears exactly once across all ready
and initialized waiting payloads. -/
def QueuedVerticesNodup (state : ReservationState) : Prop :=
  state.stack.queuedVertices.Nodup

/-- Scheduler-queued occurrences have not yet received a raw mark. -/
def QueuedVerticesUnmarked (state : ReservationState) : Prop :=
  ∀ vertex ∈ state.stack.queuedVertices,
    state.core.marks[vertex]? = some none

/-- Observable production evidence in the current executable state: a raw
mark or membership in a live production-component frontier.  The second
disjunct covers constructed conclusions that remain deliberately unmarked
while queued.

This predicate does not, by itself, recover the certificate-link identity of
an internal derivation-tree node.  Exact internal occurrence provenance is a
separate obligation for the complete Figure-7 rules. -/
def Produced (state : ReservationState) (vertex : Vertex) : Prop :=
  (∃ age, state.core.marks[vertex]? = some (some age)) ∨
    vertex ∈ state.core.liveFrontierVertices

/-- Causal production discipline for submitted multiplicative links.

Whenever a submitted par or tensor conclusion has observable production
evidence, both of its submitted premises have concrete raw marks.  Combined
with the pre-prefix fact that a selected ready premise is raw-unmarked, this
supplies the contradiction needed to rule out an observably produced
conclusion before a future `forward`/`unify` firing.

This is a necessary state predicate, not a runtime scan and not yet a complete
occurrence-faithful account of internal derivation nodes.  Repeated formula
labels mean that `FormulaConsistent` alone cannot identify an internal tree
node with one exact certificate link; that provenance remains an explicit
pre-rule obligation.
-/
def ProducedPremisesMarked (certificate : Certificate)
    (state : ReservationState) : Prop :=
  ∀ {link : Link}, link ∈ certificate.links →
    match link with
    | .axiom _ _ => True
    | .par left right conclusion
    | .tensor left right conclusion =>
        Produced state conclusion →
          (∃ leftAge,
            state.core.marks[left]? = some (some leftAge)) ∧
          ∃ rightAge,
            state.core.marks[right]? = some (some rightAge)

/-- Exact semantic span carried by one delayed par conclusion.

Every waiting occurrence names its unique submitted par producer.  Its two
premises are already marked: the older raw age maps to the waiting cell's
boundary and the younger raw age maps to a strictly later boundary.  In the
combined scheduler invariant, `RealizesSigma` and premise coverage relate
those boundaries to live components; this predicate alone does not assert
frontier membership.  The disjunction retains which submitted premise is the
older one without imposing a list order on the waiting bucket.
-/
def WaitingSpanExact (certificate : Certificate)
    (state : ReservationState) : Prop :=
  ∀ {boundary payload conclusion},
    state.stack.waiting[boundary]? =
      some (.initialized payload) →
    conclusion ∈ payload →
    ∃ linkIndex left right olderPremise youngerPremise
        olderAge youngerAge youngerBoundary,
      certificate.links[linkIndex]? =
        some (.par left right conclusion) ∧
      (SequentialUnification.sourceIndex certificate)[conclusion]? =
        some [{
          linkIndex := linkIndex
          link := .par left right conclusion }] ∧
      state.core.marks[conclusion]? = some none ∧
      ((olderPremise = left ∧ youngerPremise = right) ∨
        (olderPremise = right ∧ youngerPremise = left)) ∧
      state.core.marks[olderPremise]? = some (some olderAge) ∧
      state.core.marks[youngerPremise]? = some (some youngerAge) ∧
      sigmaBoundary? state.stack.sigma olderAge = some boundary ∧
      sigmaBoundary? state.stack.sigma youngerAge =
        some youngerBoundary ∧
      boundary < youngerBoundary

/-- Pending-premise coverage adapted to delayed conclusion marking.

A connective whose conclusion is already in a ready bucket has been
constructed even though its raw mark is deliberately still undefined. Every
other raw-unmarked connective must expose each marked premise in its live
component. Waiting conclusions are not exempt: their pars have not yet been
constructed.
-/
def PendingPremisesCoveredExceptReady (certificate : Certificate)
    (state : ReservationState) : Prop :=
  ∀ {link : Link}, link ∈ certificate.links →
    match link with
    | .axiom _ _ => True
    | .par left right conclusion
    | .tensor left right conclusion =>
        state.core.marks[conclusion]? = some none →
        conclusion ∉ state.stack.ready.flatten →
        ∀ {premise token : Nat}, premise ∈ [left, right] →
          state.core.tokenAt? premise = some token →
          ∃ component,
            state.core.componentAt? token = some component ∧
              premise ∈ component.frontier

/-- The production firing counter equals the number of logical connective
constructors actually present in live production components. -/
def FiredCounterExact (state : ReservationState) : Prop :=
  state.core.firedConnectives = state.core.liveConnectiveCount

/-- Non-circular semantic invariant for the currently constructed scheduler
state.

This foundation says nothing about dispatcher progress, full-rule
reachability, token-age strategy, fallback removal, or whole-program
complexity. -/
structure SchedulerInvariant (certificate : Certificate)
    (state : ReservationState) : Prop
    extends ReservationInvariant certificate state where
  structural : certificate.StructurallyWellFormed
  component_domain_exact : ComponentDomainExact state
  component_forest_provenance :
    certificate.ComponentForestProvenance state.core
  live_frontiers_nodup : LiveFrontiersNodup state
  ready_bucket_frontier_exact : ReadyBucketFrontierExact state
  queued_vertices_nodup : QueuedVerticesNodup state
  queued_vertices_unmarked : QueuedVerticesUnmarked state
  produced_premises_marked :
    ProducedPremisesMarked certificate state
  waiting_span_exact : WaitingSpanExact certificate state
  pending_premises_covered_except_ready :
    PendingPremisesCoveredExceptReady certificate state
  fired_counter_exact : FiredCounterExact state

/-- Every unmarked frontier occurrence in a live component appears in the
current scheduler queue. -/
theorem SchedulerInvariant.frontier_unmarked_mem_queued
    {certificate : Certificate} {state : ReservationState}
    (invariant : SchedulerInvariant certificate state)
    {index : Nat} {component : UnificationComponent} {vertex : Vertex}
    (componentLookup : state.core.components[index]? = some (some component))
    (frontier : vertex ∈ component.frontier)
    (unmarked : state.core.marks[vertex]? = some none) :
    vertex ∈ state.stack.queuedVertices := by
  have boundaryMembership : index ∈ state.stack.sigma :=
    (invariant.component_domain_exact index).mp ⟨component, componentLookup⟩
  rcases List.mem_iff_getElem.mp boundaryMembership with
    ⟨position, positionBound, positionEquation⟩
  have sigmaLookup : state.stack.sigma[position]? = some index := by
    rw [List.getElem?_eq_getElem positionBound, positionEquation]
  have readyPositionBound : position < state.stack.ready.length := by
    rw [invariant.stack_wellShaped.ready_aligned]
    exact positionBound
  let bucket := state.stack.ready[position]
  have readyLookup : state.stack.ready[position]? = some bucket :=
    List.getElem?_eq_getElem readyPositionBound
  rcases invariant.ready_bucket_frontier_exact sigmaLookup readyLookup with
    ⟨actualComponent, actualLookup, exactMembership⟩
  have componentEquation : actualComponent = component := by
    exact Option.some.inj (Option.some.inj (actualLookup.symm.trans componentLookup))
  subst actualComponent
  have vertexInBucket : vertex ∈ bucket :=
    (exactMembership vertex).mpr ⟨frontier, unmarked⟩
  unfold SequentialStackState.queuedVertices
  apply List.mem_append_left
  apply List.mem_flatten.mpr
  exact ⟨bucket, List.mem_of_getElem? readyLookup, vertexInBucket⟩

/-- An unmarked occurrence in any live component frontier is queued. -/
theorem SchedulerInvariant.unmarked_liveFrontier_mem_queued
    {certificate : Certificate} {state : ReservationState}
    (invariant : SchedulerInvariant certificate state)
    {vertex : Vertex}
    (membership : vertex ∈ state.core.liveFrontierVertices)
    (unmarked : state.core.marks[vertex]? = some none) :
    vertex ∈ state.stack.queuedVertices := by
  unfold UnificationState.liveFrontierVertices at membership
  rcases List.mem_flatMap.mp membership with
    ⟨cell, cellMembership, vertexMembership⟩
  cases cell with
  | none => simp at vertexMembership
  | some component =>
      simp only [Option.map_some, Option.getD_some] at vertexMembership
      rcases List.mem_iff_getElem.mp cellMembership with
        ⟨index, indexBound, indexEquation⟩
      have componentLookup : state.core.components[index]? = some (some component) := by
        rw [← Array.getElem?_toList]
        rw [List.getElem?_eq_getElem indexBound, indexEquation]
      exact invariant.frontier_unmarked_mem_queued
        componentLookup vertexMembership unmarked

/-- Every unmarked occurrence owned by an exact live-component witness is
queued.  The marked-owner alternative is impossible for an unmarked vertex. -/
theorem SchedulerInvariant.owned_unmarked_mem_queued
    {certificate : Certificate} {state : ReservationState}
    (invariant : SchedulerInvariant certificate state)
    {index : Nat} {component : UnificationComponent}
    {owned : List Vertex} {vertex : Vertex}
    (componentLookup : state.core.components[index]? = some (some component))
    (accounted : Certificate.OwnedOccurrenceAccounted state.core index component owned)
    (vertexOwned : vertex ∈ owned)
    (vertexUnmarked : state.core.marks[vertex]? = some none) :
    vertex ∈ state.stack.queuedVertices := by
  have vertexFrontier : vertex ∈ component.frontier := by
    rcases accounted vertex vertexOwned with
      ⟨rawAge, marked, representative⟩ | ⟨unmarked, frontier⟩
    · rw [vertexUnmarked] at marked
      simp at marked
    · exact frontier
  exact invariant.frontier_unmarked_mem_queued
    componentLookup vertexFrontier vertexUnmarked

/-- On a structurally well-formed certificate, the exact empty state has no
produced occurrence, live component, ready work, waiting promise, or fired
connective. -/
theorem empty_schedulerInvariant {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed) :
    SchedulerInvariant certificate
      (ReservationState.empty certificate) := by
  refine {
    toReservationInvariant := empty_reservationInvariant certificate
    structural := structural
    component_domain_exact := ?_
    component_forest_provenance :=
      Certificate.initialUnificationState_componentForestProvenance
        certificate
    live_frontiers_nodup := ?_
    ready_bucket_frontier_exact := ?_
    queued_vertices_nodup := ?_
    queued_vertices_unmarked := ?_
    produced_premises_marked := ?_
    waiting_span_exact := ?_
    pending_premises_covered_except_ready := ?_
    fired_counter_exact := ?_ }
  · intro token
    simp [ReservationState.empty,
      Certificate.initialUnificationState,
      SequentialStackState.empty]
  · simp [LiveFrontiersNodup,
      UnificationState.liveFrontierVertices,
      ReservationState.empty,
      Certificate.initialUnificationState]
  · unfold ReadyBucketFrontierExact
    intro position boundary bucket sigmaLookup
    simp [ReservationState.empty, SequentialStackState.empty] at sigmaLookup
  · simp [QueuedVerticesNodup, ReservationState.empty,
      empty_queuedVertices]
  · intro vertex membership
    rw [show
      (ReservationState.empty certificate).stack.queuedVertices = [] by
        exact empty_queuedVertices certificate.formulas.size] at membership
    simp at membership
  · intro link membership
    cases link with
    | «axiom» left right => trivial
    | tensor left right conclusion
    | «par» left right conclusion =>
        intro produced
        rcases produced with ⟨age, marked⟩ | frontier
        · by_cases conclusionBound :
              conclusion < certificate.formulas.size <;>
            simp [ReservationState.empty,
              Certificate.initialUnificationState,
              conclusionBound] at marked
        · simp [ReservationState.empty,
            Certificate.initialUnificationState,
            UnificationState.liveFrontierVertices] at frontier
  · unfold WaitingSpanExact
    intro boundary payload conclusion waitingLookup
    simp [ReservationState.empty, SequentialStackState.empty,
      Array.getElem?_replicate] at waitingLookup
  · intro link membership
    cases link with
    | «axiom» left right => trivial
    | tensor left right conclusion
    | «par» left right conclusion =>
        intro conclusionUnmarked conclusionNotReady premise token
          premiseMembership tokenAt
        by_cases premiseBound :
            premise < certificate.formulas.size <;>
          simp [ReservationState.empty,
            Certificate.initialUnificationState,
            UnificationState.tokenAt?, premiseBound] at tokenAt
  · rfl

/-- A successful initial reservation establishes the exact live-component
domain. -/
theorem InitialReservationStep.componentDomainExact
    {certificate : Certificate} {after : ReservationState}
    {start : Vertex}
    (step : InitialReservationStep certificate after start) :
    ComponentDomainExact after := by
  rcases certificate.reserveAxiomAt?_exact step.core_eq with
    ⟨left, right, component, exactLink, ready, componentLookup,
      frontier, marksEq, parentsEq, componentsEq, counterEq, firedEq⟩
  have stackExact :=
    SequentialStackState.initEnqueue?_exact step.stack_eq
  rw [step.output_eq]
  intro token
  rw [componentsEq, stackExact.2.2.1]
  change
    (∃ component_1,
      #[some component][token]? = some (some component_1)) ↔
      token ∈ [0]
  constructor
  · rintro ⟨candidate, lookup⟩
    have tokenBound : token < #[some component].size :=
      (Array.getElem?_eq_some_iff.mp lookup).1
    have tokenZero : token = 0 := by
      simpa using tokenBound
    simp [tokenZero]
  · intro membership
    have tokenZero : token = 0 := by simpa using membership
    subst token
    exact ⟨component, by simp⟩

/-- The two search-oriented endpoints retained by a successful initial
reservation are distinct. -/
theorem InitialReservationStep.reached_ne_partner
    {certificate : Certificate} {after : ReservationState}
    {start : Vertex}
    (step : InitialReservationStep certificate after start) :
    step.reached ≠ step.partner := by
  have route := step.route
  rcases certificate.reserveAxiomAt?_exact step.core_eq with
    ⟨left, right, component, exactLink, ready, componentLookup,
      frontier, marksEq, parentsEq, componentsEq, counterEq, firedEq⟩
  have submitted :
      Link.axiom left right =
        .axiom step.result.left step.result.right :=
    Option.some.inj (exactLink.symm.trans step.result.exactLink)
  injection submitted with leftEq rightEq
  subst left
  subst right
  have storedDifferent :
      step.result.left ≠ step.result.right :=
    ((certificate.linkLocallyWellFormed_iff
      (.axiom step.result.left step.result.right)).mp ready.1).1
  rcases route.storedEndpoints with
    ⟨reachedEq, partnerEq⟩ | ⟨reachedEq, partnerEq⟩
  · simpa [reachedEq, partnerEq] using storedDifferent
  · simpa [reachedEq, partnerEq] using storedDifferent.symm

/-- The sole live initial axiom frontier contains each occurrence once. -/
theorem InitialReservationStep.liveFrontiersNodup
    {certificate : Certificate} {after : ReservationState}
    {start : Vertex}
    (step : InitialReservationStep certificate after start) :
    LiveFrontiersNodup after := by
  rcases certificate.reserveAxiomAt?_exact step.core_eq with
    ⟨left, right, component, exactLink, ready, componentLookup,
      frontier, marksEq, parentsEq, componentsEq, counterEq, firedEq⟩
  have different : left ≠ right :=
    ((certificate.linkLocallyWellFormed_iff
      (.axiom left right)).mp ready.1).1
  rw [step.output_eq]
  unfold LiveFrontiersNodup
    UnificationState.liveFrontierVertices
  rw [componentsEq]
  simp [ReservationState.empty,
    Certificate.initialUnificationState, frontier, different]

/-- Exact queue membership after initialization is the search-oriented axiom
endpoint pair. -/
theorem InitialReservationStep.mem_queuedVertices_iff
    {certificate : Certificate} {after : ReservationState}
    {start vertex : Vertex}
    (step : InitialReservationStep certificate after start) :
    vertex ∈ after.stack.queuedVertices ↔
      vertex = step.reached ∨ vertex = step.partner := by
  have stackExact :=
    SequentialStackState.initEnqueue?_exact step.stack_eq
  have afterStackEq : after.stack = step.stackAfter :=
    congrArg (fun state : ReservationState ↦ state.stack) step.output_eq
  rw [show after.stack.queuedVertices =
      step.stackAfter.queuedVertices from congrArg
        SequentialStackState.queuedVertices afterStackEq]
  simp [SequentialStackState.queuedVertices,
    SequentialStackState.waitingVertices,
    stackExact.2.2.2.1, stackExact.2.2.2.2.1,
    ReservationState.empty, SequentialStackState.empty,
    flatMap_replicate_waitingUndefined]

/-- The initial ready pair is globally duplicate-free; the waiting table is
still empty. -/
theorem InitialReservationStep.queuedVerticesNodup
    {certificate : Certificate} {after : ReservationState}
    {start : Vertex}
    (step : InitialReservationStep certificate after start) :
    QueuedVerticesNodup after := by
  have stackExact :=
    SequentialStackState.initEnqueue?_exact step.stack_eq
  rw [step.output_eq]
  unfold QueuedVerticesNodup
    SequentialStackState.queuedVertices
    SequentialStackState.waitingVertices
  rw [stackExact.2.2.2.1, stackExact.2.2.2.2.1]
  simp [ReservationState.empty, SequentialStackState.empty,
    flatMap_replicate_waitingUndefined,
    step.reached_ne_partner]

/-- Both search-oriented initial endpoints are raw-unmarked. -/
theorem InitialReservationStep.queuedVerticesUnmarked
    {certificate : Certificate} {after : ReservationState}
    {start : Vertex}
    (step : InitialReservationStep certificate after start) :
    QueuedVerticesUnmarked after := by
  have route := step.route
  rcases certificate.reserveAxiomAt?_exact step.core_eq with
    ⟨left, right, component, exactLink, ready, componentLookup,
      frontier, marksEq, parentsEq, componentsEq, counterEq, firedEq⟩
  have submitted :
      Link.axiom left right =
        .axiom step.result.left step.result.right :=
    Option.some.inj (exactLink.symm.trans step.result.exactLink)
  injection submitted with leftEq rightEq
  subst left
  subst right
  have stackExact :=
    SequentialStackState.initEnqueue?_exact step.stack_eq
  rw [step.output_eq]
  intro vertex membership
  have endpointMembership :
      vertex = step.reached ∨ vertex = step.partner := by
    simpa [QueuedVerticesUnmarked,
      SequentialStackState.queuedVertices,
      SequentialStackState.waitingVertices,
      stackExact.2.2.2.1, stackExact.2.2.2.2.1,
      ReservationState.empty, SequentialStackState.empty,
      flatMap_replicate_waitingUndefined,
      empty_waitingVertices] using
        membership
  rcases route.storedEndpoints with
    ⟨reachedEq, partnerEq⟩ | ⟨reachedEq, partnerEq⟩
  · rcases endpointMembership with endpoint | endpoint
    · subst vertex
      rw [marksEq, reachedEq]
      exact step.result.leftReady
    · subst vertex
      rw [marksEq, partnerEq]
      exact step.result.rightReady
  · rcases endpointMembership with endpoint | endpoint
    · subst vertex
      rw [marksEq, reachedEq]
      exact step.result.rightReady
    · subst vertex
      rw [marksEq, partnerEq]
      exact step.result.leftReady

/-- A successful initial reservation aligns its search-oriented ready pair
extensionally with the submitted-orientation axiom frontier. -/
theorem InitialReservationStep.readyBucketFrontierExact
    {certificate : Certificate} {after : ReservationState}
    {start : Vertex}
    (step : InitialReservationStep certificate after start) :
    ReadyBucketFrontierExact after := by
  have route := step.route
  rcases certificate.reserveAxiomAt?_exact step.core_eq with
    ⟨left, right, component, exactLink, ready, componentLookup,
      frontier, marksEq, parentsEq, componentsEq, counterEq, firedEq⟩
  have submitted :
      Link.axiom left right =
        .axiom step.result.left step.result.right :=
    Option.some.inj (exactLink.symm.trans step.result.exactLink)
  injection submitted with leftEq rightEq
  subst left
  subst right
  have stackExact :=
    SequentialStackState.initEnqueue?_exact step.stack_eq
  rw [step.output_eq]
  unfold ReadyBucketFrontierExact
  intro position boundary bucket sigmaLookup readyLookup
  rw [stackExact.2.2.1] at sigmaLookup
  rw [stackExact.2.2.2.1] at readyLookup
  have positionBound : position < 1 := by
    simpa using (List.getElem?_eq_some_iff.mp sigmaLookup).1
  have positionZero : position = 0 := by omega
  subst position
  simp at sigmaLookup readyLookup
  subst boundary
  subst bucket
  refine ⟨component, ?_, ?_⟩
  · change step.coreAfter.components[0]? = some (some component)
    rw [componentsEq]
    simp [ReservationState.empty,
      Certificate.initialUnificationState]
  · intro vertex
    have endpoints :
        (step.reached = step.result.left ∧
          step.partner = step.result.right) ∨
        (step.reached = step.result.right ∧
          step.partner = step.result.left) :=
      route.storedEndpoints
    rcases endpoints with
      ⟨reachedEq, partnerEq⟩ | ⟨reachedEq, partnerEq⟩
    · rw [reachedEq, partnerEq, frontier]
      constructor
      · intro membership
        have submittedMembership :
            vertex = step.result.left ∨
              vertex = step.result.right := by
          simpa using membership
        have markReady :
            step.coreAfter.marks[vertex]? = some none := by
          rw [marksEq]
          rcases submittedMembership with rfl | rfl
          · exact step.result.leftReady
          · exact step.result.rightReady
        exact ⟨membership, markReady⟩
      · exact fun result => result.1
    · rw [reachedEq, partnerEq, frontier]
      constructor
      · intro membership
        have submittedMembership :
            vertex = step.result.left ∨
              vertex = step.result.right := by
          simpa [or_comm] using membership
        have markReady :
            step.coreAfter.marks[vertex]? = some none := by
          rw [marksEq]
          rcases submittedMembership with rfl | rfl
          · exact step.result.leftReady
          · exact step.result.rightReady
        exact ⟨by simpa [or_comm] using membership, markReady⟩
      · intro result
        simpa [or_comm] using result.1

/-- The initial reservation has no waiting payload. -/
theorem InitialReservationStep.waitingSpanExact
    {certificate : Certificate} {after : ReservationState}
    {start : Vertex}
    (step : InitialReservationStep certificate after start) :
    WaitingSpanExact certificate after := by
  have stackExact :=
    SequentialStackState.initEnqueue?_exact step.stack_eq
  rw [step.output_eq]
  unfold WaitingSpanExact
  intro boundary payload conclusion waitingLookup
  rw [stackExact.2.2.2.2.1] at waitingLookup
  simp [ReservationState.empty, SequentialStackState.empty,
    Array.getElem?_replicate] at waitingLookup

/-- No premise is marked immediately after initial reservation, so delayed
pending-premise coverage holds independently of the certificate's later
connective structure. -/
theorem InitialReservationStep.pendingPremisesCoveredExceptReady
    {certificate : Certificate} {after : ReservationState}
    {start : Vertex}
    (step : InitialReservationStep certificate after start) :
    PendingPremisesCoveredExceptReady certificate after := by
  rcases certificate.reserveAxiomAt?_exact step.core_eq with
    ⟨left, right, component, exactLink, ready, componentLookup,
      frontier, marksEq, parentsEq, componentsEq, counterEq, firedEq⟩
  rw [step.output_eq]
  intro link membership
  cases link with
  | «axiom» axiomLeft axiomRight => trivial
  | tensor premiseLeft premiseRight conclusion
  | «par» premiseLeft premiseRight conclusion =>
      intro conclusionUnmarked conclusionNotReady premise token
        premiseMembership tokenAt
      unfold UnificationState.tokenAt? at tokenAt
      rw [marksEq] at tokenAt
      by_cases premiseBound :
          premise < certificate.formulas.size <;>
        simp [ReservationState.empty,
          Certificate.initialUnificationState,
          premiseBound] at tokenAt

/-- Initial production contains only the submitted axiom component.  Structural
formula ownership prevents either atomic frontier endpoint from simultaneously
being the conclusion of a submitted par or tensor, so the causal production
obligation holds before any premise has been marked. -/
theorem InitialReservationStep.producedPremisesMarked
    {certificate : Certificate} {after : ReservationState}
    {start : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (step : InitialReservationStep certificate after start) :
    ProducedPremisesMarked certificate after := by
  rcases certificate.reserveAxiomAt?_exact step.core_eq with
    ⟨left, right, component, exactLink, ready, componentLookup,
      frontier, marksEq, parentsEq, componentsEq, counterEq, firedEq⟩
  have axiomMembership :
      (.axiom left right : Link) ∈ certificate.links :=
    List.mem_of_getElem? exactLink
  rw [step.output_eq]
  intro link membership
  cases link with
  | «axiom» axiomLeft axiomRight =>
      trivial
  | tensor premiseLeft premiseRight conclusion
  | «par» premiseLeft premiseRight conclusion =>
      intro produced
      have endpoint : conclusion = left ∨ conclusion = right := by
        rcases produced with ⟨age, marked⟩ | frontierMembership
        · rw [marksEq] at marked
          by_cases conclusionBound :
              conclusion < certificate.formulas.size <;>
            simp [ReservationState.empty,
              Certificate.initialUnificationState,
              conclusionBound] at marked
        · unfold UnificationState.liveFrontierVertices at frontierMembership
          rw [componentsEq] at frontierMembership
          simpa [ReservationState.empty,
            Certificate.initialUnificationState, frontier] using
              frontierMembership
      rcases
          StructurallyWellFormed.axiomEndpointFormula_of_mem
            structural axiomMembership endpoint with
        ⟨name, positive, atomFormula⟩
      have connectiveWellFormed :=
        structural.2.2.2.2.1 _ membership
      rcases connectiveWellFormed with
        ⟨_, _, _, _, _, _, typing⟩
      cases leftFormula :
          certificate.formula? premiseLeft <;>
        cases rightFormula :
          certificate.formula? premiseRight <;>
        simp [leftFormula, rightFormula, atomFormula] at typing

/-- The first reserved component is an axiom tree, so its exact live
connective count is zero. -/
theorem InitialReservationStep.firedCounterExact
    {certificate : Certificate} {after : ReservationState}
    {start : Vertex}
    (step : InitialReservationStep certificate after start) :
    FiredCounterExact after := by
  rcases certificate.reserveAxiomAt?_exact step.core_eq with
    ⟨left, right, component, exactLink, ready, componentLookup,
      frontier, marksEq, parentsEq, componentsEq, counterEq, firedEq⟩
  rcases
      Certificate.UnificationComponent.axiom?_success
        componentLookup with
    ⟨name, positive, leftFormula, componentEq⟩
  subst component
  rw [step.output_eq]
  unfold FiredCounterExact
  change
    step.coreAfter.firedConnectives =
      step.coreAfter.liveConnectiveCount
  rw [firedEq]
  unfold UnificationState.liveConnectiveCount
  rw [componentsEq]
  change
    0 =
      (#[some {
        tree := CutFreeDerivation.axiom name positive
        frontier := [left, right] }] :
        Array (Option UnificationComponent)).toList.foldl
          (fun total cell =>
            total +
              (cell.map
                UnificationComponent.connectiveCount).getD 0)
          0
  rfl

/-- A successful initial wrapper installs the exact one-component occurrence
forest produced by its submitted axiom reservation. -/
theorem InitialReservationStep.componentForestProvenance
    {certificate : Certificate} {after : ReservationState}
    {start : Vertex}
    (step : InitialReservationStep certificate after start)
    (structural : certificate.StructurallyWellFormed) :
    certificate.ComponentForestProvenance after.core := by
  rw [step.output_eq]
  exact
    Certificate.reserveAxiomAt?_componentForestProvenance_of_initial
      structural step.core_eq

/-- Every successful exact initial wrapper call establishes the complete
state-based scheduler foundation. -/
theorem InitialReservationStep.schedulerInvariant
    {certificate : Certificate} {after : ReservationState}
    {start : Vertex}
    (step : InitialReservationStep certificate after start)
    (structural : certificate.StructurallyWellFormed) :
    SchedulerInvariant certificate after := by
  exact {
    toReservationInvariant := step.reservationInvariant
    structural := structural
    component_domain_exact := step.componentDomainExact
    component_forest_provenance :=
      step.componentForestProvenance structural
    live_frontiers_nodup := step.liveFrontiersNodup
    ready_bucket_frontier_exact :=
      step.readyBucketFrontierExact
    queued_vertices_nodup := step.queuedVerticesNodup
    queued_vertices_unmarked := step.queuedVerticesUnmarked
    produced_premises_marked :=
      step.producedPremisesMarked structural
    waiting_span_exact := step.waitingSpanExact
    pending_premises_covered_except_ready :=
      step.pendingPremisesCoveredExceptReady
    fired_counter_exact := step.firedCounterExact }

end SequentialSchedulerBridge

namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge

namespace PreparedStep

private theorem mem_liveFrontierVertices_of_raw
    {state : UnificationState} {token : Nat}
    {component : UnificationComponent} {vertex : Vertex}
    (componentLookup :
      state.components[token]? = some (some component))
    (vertexMembership : vertex ∈ component.frontier) :
    vertex ∈ state.liveFrontierVertices := by
  unfold UnificationState.liveFrontierVertices
  apply List.mem_flatMap.mpr
  refine ⟨some component, ?_, ?_⟩
  · exact List.mem_of_getElem? (by simpa using componentLookup)
  · simpa using vertexMembership

/-- The synchronized pop/raw-mark prefix preserves every current state-only
field of `SchedulerInvariant`.  It removes exactly the selected occurrence
from the active ready bucket and gives that already-live frontier occurrence
its active raw-age mark; components, waiting payloads, `sigma`, counters, and
tags are unchanged. -/
theorem schedulerInvariant
    {certificate : Certificate} {before : ReservationState}
    (step : PreparedStep before)
    (invariant : SchedulerInvariant certificate before) :
    SchedulerInvariant certificate step.after := by
  rcases
      SequentialStackState.popReadyMark?_exact step.stack_eq with
    ⟨topEquation, sigmaTopEquation, stackUnmarked,
      stackMarksEquation, stackNextAgeEquation, stackSigmaEquation,
      stackReadyEquation, stackWaitingEquation, stackMarked⟩
  rcases
      UnificationState.markReadyRaw?_exact step.core_mark_eq with
    ⟨coreUnmarked, coreMarksEquation, coreParentsEquation,
      coreComponentsEquation, coreStartedEquation,
      coreFiredEquation, coreMarked⟩
  rcases List.getLast?_eq_some_iff.mp topEquation with
    ⟨readyPrefix, readyDecomposition⟩
  rcases List.getLast?_eq_some_iff.mp sigmaTopEquation with
    ⟨sigmaPrefix, sigmaDecomposition⟩
  have prefixLengths : readyPrefix.length = sigmaPrefix.length := by
    have aligned := invariant.stack_wellShaped.ready_aligned
    rw [readyDecomposition, sigmaDecomposition] at aligned
    simp at aligned
    omega
  have afterReady :
      step.after.stack.ready =
        readyPrefix ++ [step.stackResult.remainingTop] := by
    change step.stackResult.after.ready =
      readyPrefix ++ [step.stackResult.remainingTop]
    rw [stackReadyEquation, readyDecomposition]
    simp
  have afterSigma :
      step.after.stack.sigma = before.stack.sigma := by
    change step.stackResult.after.sigma = before.stack.sigma
    exact stackSigmaEquation
  have afterWaiting :
      step.after.stack.waiting = before.stack.waiting := by
    change step.stackResult.after.waiting = before.stack.waiting
    exact stackWaitingEquation
  have afterComponents :
      step.after.core.components = before.core.components :=
    coreComponentsEquation
  have afterParents :
      step.after.core.parents = before.core.parents :=
    coreParentsEquation
  have afterMarks :
      step.after.core.marks =
        before.core.marks.setIfInBounds
          step.stackResult.vertex
          (some step.stackResult.rawAge) :=
    coreMarksEquation
  have afterFired :
      step.after.core.firedConnectives =
        before.core.firedConnectives :=
    coreFiredEquation
  have selectedOldReady :
      step.stackResult.vertex ∈ before.stack.ready.flatten := by
    rw [readyDecomposition]
    simp
  have selectedOldQueued :
      step.stackResult.vertex ∈ before.stack.queuedVertices := by
    simp [SequentialStackState.queuedVertices, selectedOldReady]
  have beforeQueued :
      before.stack.queuedVertices =
        readyPrefix.flatten ++
          step.stackResult.vertex ::
            (step.stackResult.remainingTop ++
              before.stack.waitingVertices) := by
    simp [SequentialStackState.queuedVertices, readyDecomposition,
      List.append_assoc]
  have afterQueued :
      step.after.stack.queuedVertices =
        readyPrefix.flatten ++
          (step.stackResult.remainingTop ++
            before.stack.waitingVertices) := by
    simp [SequentialStackState.queuedVertices, afterReady,
      SequentialStackState.waitingVertices, afterWaiting,
      List.append_assoc]
  have oldQueueParts :
      readyPrefix.flatten.Nodup ∧
        (step.stackResult.vertex ::
          (step.stackResult.remainingTop ++
            before.stack.waitingVertices)).Nodup ∧
        ∀ first ∈ readyPrefix.flatten,
          ∀ second ∈
              step.stackResult.vertex ::
                (step.stackResult.remainingTop ++
                  before.stack.waitingVertices),
            first ≠ second := by
    apply List.nodup_append.mp
    rw [← beforeQueued]
    exact invariant.queued_vertices_nodup
  have selectedNotAfterQueued :
      step.stackResult.vertex ∉ step.after.stack.queuedVertices := by
    rw [afterQueued]
    intro membership
    simp only [List.mem_append] at membership
    rcases membership with inPrefix | inTail
    · exact oldQueueParts.2.2
        step.stackResult.vertex inPrefix
        step.stackResult.vertex (by simp) rfl
    · exact
        (List.nodup_cons.mp oldQueueParts.2.1).1
          (by simpa using inTail)
  have afterQueuedSubsetOld :
      ∀ {vertex},
        vertex ∈ step.after.stack.queuedVertices →
          vertex ∈ before.stack.queuedVertices := by
    intro vertex membership
    rw [afterQueued] at membership
    rw [beforeQueued]
    simp only [List.mem_append, List.mem_cons] at membership ⊢
    rcases membership with inPrefix | inTail
    · exact Or.inl inPrefix
    · exact Or.inr (Or.inr inTail)
  have topSigmaLookup :
      before.stack.sigma[readyPrefix.length]? =
        some step.stackResult.rawAge := by
    rw [sigmaDecomposition, prefixLengths]
    simp
  have topReadyLookup :
      before.stack.ready[readyPrefix.length]? =
        some
          (step.stackResult.vertex ::
            step.stackResult.remainingTop) := by
    rw [readyDecomposition]
    simp
  rcases
      invariant.ready_bucket_frontier_exact
        topSigmaLookup topReadyLookup with
    ⟨topComponent, topComponentLookup, topFrontier⟩
  have selectedTopFrontier :
      step.stackResult.vertex ∈ topComponent.frontier :=
    (topFrontier step.stackResult.vertex).mp (by simp) |>.1
  have selectedOldProduced :
      Produced before step.stackResult.vertex :=
    Or.inr
      (mem_liveFrontierVertices_of_raw
        topComponentLookup selectedTopFrontier)
  have rawAgeBound :
      step.stackResult.rawAge < before.stack.nextAge := by
    have membership : step.stackResult.rawAge ∈ before.stack.sigma := by
      rw [sigmaDecomposition]
      simp
    exact invariant.stack_wellShaped.sigma_partition.boundary_lt
      step.stackResult.rawAge membership
  have rawAgeRootBefore :
      before.core.representative step.stackResult.rawAge =
        step.stackResult.rawAge := by
    have boundaryLookup :
        sigmaBoundary? before.stack.sigma
            step.stackResult.rawAge =
          some step.stackResult.rawAge :=
      invariant.stack_wellShaped.sigma_partition
        |>.sigmaBoundary?_eq_top sigmaTopEquation
    have realizesLookup :=
      invariant.realizesSigma.representative_eq_boundary rawAgeBound
    exact Option.some.inj (realizesLookup.symm.trans boundaryLookup)
  have representativeUnchanged :
      ∀ token,
        step.after.core.representative token =
          before.core.representative token := by
    intro token
    unfold UnificationState.representative
    rw [afterParents]
  have rawAgeRootAfter :
      step.after.core.representative step.stackResult.rawAge =
        step.stackResult.rawAge := by
    rw [representativeUnchanged]
    exact rawAgeRootBefore
  have afterComponentForest :
      certificate.ComponentForestProvenance step.after.core :=
    invariant.component_forest_provenance
      |>.markReadyRaw?_of_root_frontier
        rawAgeRootBefore
        ⟨topComponent, topComponentLookup, selectedTopFrontier⟩
        step.core_mark_eq
  have afterSelectedMarked :
      step.after.core.marks[step.stackResult.vertex]? =
        some (some step.stackResult.rawAge) := by
    exact coreMarked
  have preserveOldMarked :
      ∀ {vertex : Vertex} {age : RawTokenAge},
        before.core.marks[vertex]? = some (some age) →
          step.after.core.marks[vertex]? = some (some age) := by
    intro vertex age marked
    have selectedNe :
        step.stackResult.vertex ≠ vertex := by
      intro same
      subst vertex
      rw [coreUnmarked] at marked
      simp at marked
    rw [afterMarks]
    simpa [Array.getElem?_setIfInBounds, selectedNe] using marked
  refine {
    toReservationInvariant :=
      step.reservationInvariant invariant.toReservationInvariant
    structural := invariant.structural
    component_domain_exact := ?_
    component_forest_provenance := afterComponentForest
    live_frontiers_nodup := ?_
    ready_bucket_frontier_exact := ?_
    queued_vertices_nodup := ?_
    queued_vertices_unmarked := ?_
    produced_premises_marked := ?_
    waiting_span_exact := ?_
    pending_premises_covered_except_ready := ?_
    fired_counter_exact := ?_ }
  · intro token
    simpa [ComponentDomainExact, afterComponents, afterSigma] using
      invariant.component_domain_exact token
  · unfold LiveFrontiersNodup
    unfold UnificationState.liveFrontierVertices
    rw [afterComponents]
    exact invariant.live_frontiers_nodup
  · unfold ReadyBucketFrontierExact
    intro position boundary bucket sigmaLookup readyLookup
    have positionBound :
        position < (readyPrefix ++
          [step.stackResult.remainingTop]).length := by
      rw [← afterReady]
      exact (List.getElem?_eq_some_iff.mp readyLookup).1
    have oldSigmaLookup :
        before.stack.sigma[position]? = some boundary := by
      rw [afterSigma] at sigmaLookup
      exact sigmaLookup
    by_cases inPrefix : position < readyPrefix.length
    · have oldReadyLookup :
          before.stack.ready[position]? = some bucket := by
        rw [readyDecomposition, List.getElem?_append_left inPrefix]
        rw [afterReady, List.getElem?_append_left inPrefix] at readyLookup
        exact readyLookup
      rcases
          invariant.ready_bucket_frontier_exact
            oldSigmaLookup oldReadyLookup with
        ⟨component, componentLookup, exactMembership⟩
      refine ⟨component, ?_, ?_⟩
      · rw [afterComponents]
        exact componentLookup
      · intro vertex
        constructor
        · intro vertexInBucket
          have oldExact := (exactMembership vertex).mp vertexInBucket
          have bucketInAfter :
              bucket ∈ step.after.stack.ready :=
            List.mem_of_getElem? readyLookup
          have vertexAfterQueued :
              vertex ∈ step.after.stack.queuedVertices := by
            unfold SequentialStackState.queuedVertices
            apply List.mem_append_left
            exact List.mem_flatten.mpr
              ⟨bucket, bucketInAfter, vertexInBucket⟩
          have selectedNe :
              step.stackResult.vertex ≠ vertex := by
            intro same
            subst vertex
            exact selectedNotAfterQueued vertexAfterQueued
          refine ⟨oldExact.1, ?_⟩
          rw [afterMarks]
          simpa [Array.getElem?_setIfInBounds, selectedNe] using
            oldExact.2
        · rintro ⟨vertexFrontier, vertexUnmarked⟩
          have selectedNe :
              step.stackResult.vertex ≠ vertex := by
            intro same
            subst vertex
            rw [afterSelectedMarked] at vertexUnmarked
            simp at vertexUnmarked
          apply (exactMembership vertex).mpr
          refine ⟨vertexFrontier, ?_⟩
          rw [afterMarks] at vertexUnmarked
          simpa [Array.getElem?_setIfInBounds, selectedNe] using
            vertexUnmarked
    · have positionTop : position = readyPrefix.length := by
        simp at positionBound
        omega
      subst position
      have bucketEquation :
          bucket = step.stackResult.remainingTop := by
        rw [afterReady] at readyLookup
        simp at readyLookup
        exact readyLookup.symm
      have boundaryEquation :
          boundary = step.stackResult.rawAge := by
        rw [sigmaDecomposition, prefixLengths] at oldSigmaLookup
        simp at oldSigmaLookup
        exact oldSigmaLookup.symm
      subst bucket
      subst boundary
      refine ⟨topComponent, ?_, ?_⟩
      · rw [afterComponents]
        exact topComponentLookup
      · intro vertex
        constructor
        · intro vertexInTail
          have oldExact :=
            (topFrontier vertex).mp (by simp [vertexInTail])
          have selectedNe :
              step.stackResult.vertex ≠ vertex := by
            intro same
            apply
              (List.nodup_cons.mp
                (invariant.stack_wellShaped.ready_nodup
                  (step.stackResult.vertex ::
                    step.stackResult.remainingTop)
                  (by rw [readyDecomposition]; simp))).1
            rw [same]
            exact vertexInTail
          refine ⟨oldExact.1, ?_⟩
          rw [afterMarks]
          simpa [Array.getElem?_setIfInBounds, selectedNe] using
            oldExact.2
        · rintro ⟨vertexFrontier, vertexUnmarked⟩
          have selectedNe :
              step.stackResult.vertex ≠ vertex := by
            intro same
            subst vertex
            rw [afterSelectedMarked] at vertexUnmarked
            simp at vertexUnmarked
          have oldUnmarked :
              before.core.marks[vertex]? = some none := by
            rw [afterMarks] at vertexUnmarked
            simpa [Array.getElem?_setIfInBounds, selectedNe] using
              vertexUnmarked
          have oldMembership :=
            (topFrontier vertex).mpr
              ⟨vertexFrontier, oldUnmarked⟩
          have vertexNeSelected :
              vertex ≠ step.stackResult.vertex :=
            selectedNe.symm
          simpa [vertexNeSelected] using oldMembership
  · unfold QueuedVerticesNodup
    rw [afterQueued]
    apply List.nodup_append.mpr
    refine ⟨oldQueueParts.1, ?_, ?_⟩
    · exact (List.nodup_cons.mp oldQueueParts.2.1).2
    · intro first firstMembership second secondMembership same
      exact oldQueueParts.2.2 first firstMembership second
        (by simp [secondMembership]) same
  · intro vertex membership
    have oldMembership := afterQueuedSubsetOld membership
    have oldUnmarked :=
      invariant.queued_vertices_unmarked vertex oldMembership
    have selectedNe :
        step.stackResult.vertex ≠ vertex := by
      intro same
      subst vertex
      exact selectedNotAfterQueued membership
    rw [afterMarks]
    simpa [Array.getElem?_setIfInBounds, selectedNe] using oldUnmarked
  · intro link linkMembership
    cases link with
    | «axiom» left right =>
        trivial
    | tensor left right conclusion
    | «par» left right conclusion =>
        intro producedAfter
        have producedBefore : Produced before conclusion := by
          rcases producedAfter with markedAfter | frontierAfter
          · rcases markedAfter with ⟨age, markedAfter⟩
            by_cases selected :
                step.stackResult.vertex = conclusion
            · subst conclusion
              exact selectedOldProduced
            · left
              refine ⟨age, ?_⟩
              rw [afterMarks] at markedAfter
              simpa [Array.getElem?_setIfInBounds, selected] using
                markedAfter
          · right
            unfold UnificationState.liveFrontierVertices at frontierAfter ⊢
            rw [afterComponents] at frontierAfter
            exact frontierAfter
        rcases
            invariant.produced_premises_marked
              linkMembership producedBefore with
          ⟨⟨leftAge, leftMarked⟩, rightAge, rightMarked⟩
        exact
          ⟨⟨leftAge, preserveOldMarked leftMarked⟩,
            rightAge, preserveOldMarked rightMarked⟩
  · unfold WaitingSpanExact
    intro boundary payload conclusion waitingLookup conclusionMembership
    have oldWaitingLookup :
        before.stack.waiting[boundary]? =
          some (.initialized payload) := by
      rw [afterWaiting] at waitingLookup
      exact waitingLookup
    rcases
        invariant.waiting_span_exact
          oldWaitingLookup conclusionMembership with
      ⟨linkIndex, left, right, olderPremise, youngerPremise,
        olderAge, youngerAge, youngerBoundary,
        linkLookup, sourceLookup, conclusionUnmarked,
        premiseOrientation, olderMarked, youngerMarked,
        olderBoundary, youngerBoundaryLookup, boundaryLt⟩
    have conclusionAfterQueued :
        conclusion ∈ step.after.stack.queuedVertices := by
      unfold SequentialStackState.queuedVertices
      apply List.mem_append_right
      unfold SequentialStackState.waitingVertices
      apply List.mem_flatMap.mpr
      refine ⟨WaitingCell.initialized payload, ?_, ?_⟩
      · exact List.mem_of_getElem? (by simpa using waitingLookup)
      · simpa [WaitingCell.vertices] using conclusionMembership
    have selectedNeConclusion :
        step.stackResult.vertex ≠ conclusion := by
      intro same
      subst conclusion
      exact selectedNotAfterQueued conclusionAfterQueued
    refine
      ⟨linkIndex, left, right, olderPremise, youngerPremise,
        olderAge, youngerAge, youngerBoundary,
        linkLookup, sourceLookup, ?_, premiseOrientation,
        ?_, ?_, ?_, ?_, boundaryLt⟩
    · rw [afterMarks]
      simpa [Array.getElem?_setIfInBounds, selectedNeConclusion] using
        conclusionUnmarked
    · exact preserveOldMarked olderMarked
    · exact preserveOldMarked youngerMarked
    · rw [afterSigma]
      exact olderBoundary
    · rw [afterSigma]
      exact youngerBoundaryLookup
  · intro link linkMembership
    cases link with
    | «axiom» left right =>
        trivial
    | tensor left right conclusion
    | «par» left right conclusion =>
        intro conclusionUnmarked conclusionNotReady premise token
          premiseMembership tokenAt
        have selectedNeConclusion :
            step.stackResult.vertex ≠ conclusion := by
          intro same
          subst conclusion
          rw [afterSelectedMarked] at conclusionUnmarked
          simp at conclusionUnmarked
        have oldConclusionUnmarked :
            before.core.marks[conclusion]? = some none := by
          rw [afterMarks] at conclusionUnmarked
          simpa [Array.getElem?_setIfInBounds,
            selectedNeConclusion] using conclusionUnmarked
        have oldConclusionNotReady :
            conclusion ∉ before.stack.ready.flatten := by
          intro oldMembership
          have oldCases :
              conclusion ∈ readyPrefix.flatten ∨
                conclusion = step.stackResult.vertex ∨
                conclusion ∈ step.stackResult.remainingTop := by
            rw [readyDecomposition] at oldMembership
            simpa using oldMembership
          rcases oldCases with inPrefix | same | inTail
          · apply conclusionNotReady
            rw [afterReady]
            simpa using Or.inl inPrefix
          · exact selectedNeConclusion same.symm
          · apply conclusionNotReady
            rw [afterReady]
            simpa using Or.inr inTail
        by_cases selectedPremise :
            step.stackResult.vertex = premise
        · subst premise
          have tokenEquation :
              token = step.stackResult.rawAge := by
            unfold UnificationState.tokenAt? at tokenAt
            rw [afterSelectedMarked] at tokenAt
            simp [rawAgeRootAfter] at tokenAt
            exact tokenAt.symm
          subst token
          refine ⟨topComponent, ?_, selectedTopFrontier⟩
          unfold UnificationState.componentAt?
          rw [rawAgeRootAfter, afterComponents]
          simp [topComponentLookup]
        · have oldTokenAt :
              before.core.tokenAt? premise = some token := by
            unfold UnificationState.tokenAt? at tokenAt ⊢
            rw [afterMarks] at tokenAt
            simpa [Array.getElem?_setIfInBounds, selectedPremise,
              representativeUnchanged] using tokenAt
          rcases
              invariant.pending_premises_covered_except_ready
                linkMembership oldConclusionUnmarked
                oldConclusionNotReady premiseMembership oldTokenAt with
            ⟨component, componentLookup, frontierMembership⟩
          refine ⟨component, ?_, frontierMembership⟩
          unfold UnificationState.componentAt? at componentLookup ⊢
          rw [representativeUnchanged, afterComponents]
          exact componentLookup
  · unfold FiredCounterExact
    rw [afterFired]
    unfold UnificationState.liveConnectiveCount
    rw [afterComponents]
    exact invariant.fired_counter_exact

/-- The prepared state inherits the general ownership-to-queue bridge. -/
theorem owned_unmarked_mem_after_queued
    {certificate : Certificate} {before : ReservationState}
    (step : PreparedStep before)
    (invariant : SchedulerInvariant certificate before)
    {index : Nat} {component : UnificationComponent}
    {owned : List Vertex} {vertex : Vertex}
    (componentLookup : step.after.core.components[index]? = some (some component))
    (accounted : Certificate.OwnedOccurrenceAccounted step.after.core index component owned)
    (vertexOwned : vertex ∈ owned)
    (vertexUnmarked : step.after.core.marks[vertex]? = some none) :
    vertex ∈ step.after.stack.queuedVertices :=
  (step.schedulerInvariant invariant).owned_unmarked_mem_queued
    componentLookup accounted vertexOwned vertexUnmarked

end PreparedStep

/-- Removing and raw-marking the selected ready head cannot introduce a new
queued occurrence. -/
theorem PreparedStep.after_queued_subset_before
    {before : ReservationState} (step : PreparedStep before) :
    ∀ {vertex}, vertex ∈ step.after.stack.queuedVertices →
      vertex ∈ before.stack.queuedVertices := by
  rcases SequentialStackState.popReadyMark?_exact step.stack_eq with
    ⟨topEquation, _, _, _, _, _, stackReadyEquation,
      stackWaitingEquation, _⟩
  rcases List.getLast?_eq_some_iff.mp topEquation with
    ⟨readyPrefix, readyDecomposition⟩
  have afterReady : step.after.stack.ready =
      readyPrefix ++ [step.stackResult.remainingTop] := by
    change step.stackResult.after.ready = _
    rw [stackReadyEquation, readyDecomposition]
    simp
  have afterWaiting :
      step.after.stack.waiting = before.stack.waiting := by
    change step.stackResult.after.waiting = _
    exact stackWaitingEquation
  intro vertex membership
  unfold SequentialStackState.queuedVertices
    SequentialStackState.waitingVertices at membership ⊢
  rw [afterReady, afterWaiting] at membership
  rw [readyDecomposition]
  simp only [List.flatten_append, List.flatten_cons, List.flatten_nil,
    List.append_nil, List.mem_append, List.mem_cons] at membership ⊢
  rcases membership with (inPrefix | inRemaining) | inWaiting
  · exact Or.inl (Or.inl inPrefix)
  · exact Or.inl (Or.inr (Or.inr inRemaining))
  · exact Or.inr inWaiting

private theorem SchedulerInvariant.ready_mem_liveFrontier
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
  rcases invariant.ready_bucket_frontier_exact
      sigmaLookup readyLookup with
    ⟨component, componentLookup, exactMembership⟩
  have frontierMembership : vertex ∈ component.frontier :=
    (exactMembership vertex).mp vertexMembership |>.1
  unfold UnificationState.liveFrontierVertices
  apply List.mem_flatMap.mpr
  refine ⟨some component, ?_, ?_⟩
  · exact List.mem_of_getElem? (by simpa using componentLookup)
  · simpa using frontierMembership

/-- The complete scheduler invariant derives the representation-only
`forward?` ready-list freshness condition.

The essential contradiction is semantic rather than a global duplicate scan:
if the submitted par conclusion were already in the active ready tail, exact
ready/frontier correspondence would make it `Produced`; then
`ProducedPremisesMarked` would mark both submitted premises, contradicting
the common prefix's exact pre-state fact that the selected premise is raw
unmarked. -/
theorem SchedulerInvariant.forwardExecutableReadyNodup
    {certificate : Certificate} {before : ReservationState}
    (invariant : SchedulerInvariant certificate before) :
    ForwardExecutableReadyNodup certificate before := by
  intro vertex rawAge linkIndex storedLeft storedRight conclusion
    side middle activeReady prefixRule linkEquation premiseEquation
    middleLast
  rcases prefixRule with
    ⟨readyPrefix, readyTail, _sigmaPrefix, readyBeforeEquation,
      _sigmaEquation, _stackUnmarked, coreUnmarked,
      middleStackEquation, _middleCoreEquation, _middleTagsEquation⟩
  have exactMiddleLast :
      middle.stack.ready.getLast? = some readyTail := by
    rw [middleStackEquation]
    simp
  have activeReadyEquation : activeReady = readyTail :=
    Option.some.inj (middleLast.symm.trans exactMiddleLast)
  subst activeReady
  have topMembership :
      vertex :: readyTail ∈ before.stack.ready := by
    rw [readyBeforeEquation]
    simp
  have topNodup : (vertex :: readyTail).Nodup :=
    invariant.stack_wellShaped.ready_nodup
      (vertex :: readyTail) topMembership
  apply List.nodup_cons.mpr
  constructor
  · intro conclusionInTail
    have conclusionInReady :
        conclusion ∈ before.stack.ready.flatten := by
      apply List.mem_flatten.mpr
      exact ⟨vertex :: readyTail, topMembership,
        by simp [conclusionInTail]⟩
    have conclusionInFrontier :
        conclusion ∈ before.core.liveFrontierVertices :=
      SchedulerInvariant.ready_mem_liveFrontier
        invariant conclusionInReady
    have conclusionProduced : Produced before conclusion :=
      Or.inr conclusionInFrontier
    have linkMembership :
        (.par storedLeft storedRight conclusion : Link) ∈
          certificate.links :=
      List.mem_of_getElem? linkEquation
    rcases invariant.produced_premises_marked
        linkMembership conclusionProduced with
      ⟨⟨leftAge, leftMarked⟩, rightAge, rightMarked⟩
    cases side with
    | storedLeft =>
        have selectedEquation : vertex = storedLeft := by
          simpa [TensorPremiseSide.premise] using premiseEquation
        have selectedMarked :
            before.core.marks[vertex]? = some (some leftAge) := by
          simpa [selectedEquation] using leftMarked
        rw [coreUnmarked] at selectedMarked
        simp at selectedMarked
    | storedRight =>
        have selectedEquation : vertex = storedRight := by
          simpa [TensorPremiseSide.premise] using premiseEquation
        have selectedMarked :
            before.core.marks[vertex]? = some (some rightAge) := by
          simpa [selectedEquation] using rightMarked
        rw [coreUnmarked] at selectedMarked
        simp at selectedMarked
  · exact topNodup.tail

private theorem flatMap_set_eq_of_getElem?_eq
    {α β : Type} {values : List α} {index : Nat}
    {before after : α} {mapping : α → List β}
    (lookup : values[index]? = some before)
    (mapped : mapping after = mapping before) :
    (values.set index after).flatMap mapping = values.flatMap mapping := by
  induction values generalizing index with
  | nil => simp at lookup
  | cons head tail induction =>
      cases index with
      | zero =>
          simp at lookup
          subst before
          simp [mapped]
      | succ prior =>
          simp at lookup
          simp [induction lookup]

private theorem array_flatMap_set_eq_of_getElem?_eq
    {α β : Type} {values : Array α} {index : Nat}
    {before after : α} {mapping : α → List β}
    (lookup : values[index]? = some before)
    (mapped : mapping after = mapping before) :
    (values.setIfInBounds index after).toList.flatMap mapping =
      values.toList.flatMap mapping := by
  rw [Array.toList_setIfInBounds]
  exact flatMap_set_eq_of_getElem?_eq (by simpa using lookup) mapped

private theorem mem_flatMap_set_cons_iff
    {α β : Type} {values : List α} {index : Nat}
    {before after : α} {mapping : α → List β} {inserted candidate : β}
    (lookup : values[index]? = some before)
    (mapped : mapping after = inserted :: mapping before) :
    candidate ∈ (values.set index after).flatMap mapping ↔
      candidate = inserted ∨ candidate ∈ values.flatMap mapping := by
  induction values generalizing index with
  | nil => simp at lookup
  | cons head tail induction =>
      cases index with
      | zero =>
          simp at lookup
          subst before
          simp [mapped]
      | succ prior =>
          simp only [List.getElem?_cons_succ] at lookup
          simp only [List.set, List.flatMap_cons, List.mem_append]
          rw [induction lookup]
          constructor
          · rintro (inHead | equal | inTail)
            · exact Or.inr (Or.inl inHead)
            · exact Or.inl equal
            · exact Or.inr (Or.inr inTail)
          · rintro (equal | inHead | inTail)
            · exact Or.inr (Or.inl equal)
            · exact Or.inl inHead
            · exact Or.inr (Or.inr inTail)

/-- Prepending one waiting promise adds exactly that conclusion to the global
queued-occurrence membership relation. -/
theorem PrependWaitingStep.mem_queuedVertices_iff
    {before after : SequentialStackState}
    {boundary : RawTokenAge} {conclusion vertex : Vertex}
    (step : PrependWaitingStep before after boundary conclusion) :
    vertex ∈ after.queuedVertices ↔
      vertex = conclusion ∨ vertex ∈ before.queuedVertices := by
  rcases step with ⟨payload, initialized, rfl⟩
  have initializedList :
      before.waiting.toList[boundary]? = some (.initialized payload) := by
    rw [Array.getElem?_toList]
    exact initialized
  unfold SequentialStackState.queuedVertices
    SequentialStackState.waitingVertices
  rw [Array.toList_setIfInBounds]
  simp only [List.mem_append]
  rw [mem_flatMap_set_cons_iff initializedList (by rfl)]
  constructor
  · rintro (inReady | same | inWaiting)
    · exact Or.inr (Or.inl inReady)
    · exact Or.inl same
    · exact Or.inr (Or.inr inWaiting)
  · rintro (same | inReady | inWaiting)
    · exact Or.inr (Or.inl same)
    · exact Or.inl inReady
    · exact Or.inr (Or.inr inWaiting)

/-- Prepending one active-ready promise adds exactly that conclusion to the
global queued-occurrence membership relation. -/
theorem PrependReadyTopStep.mem_queuedVertices_iff
    {before after : SequentialStackState} {conclusion vertex : Vertex}
    (step : PrependReadyTopStep before after conclusion) :
    vertex ∈ after.queuedVertices ↔
      vertex = conclusion ∨ vertex ∈ before.queuedVertices := by
  rcases step with
    ⟨readyPrefix, activeReady, readyEquation, rfl⟩
  unfold SequentialStackState.queuedVertices
    SequentialStackState.waitingVertices
  rw [readyEquation]
  simp only [List.flatten_append, List.flatten_cons, List.flatten_nil,
    List.append_nil, List.mem_append, List.mem_cons]
  constructor
  · rintro ((inPrefix | same | inActive) | inWaiting)
    · exact Or.inr (Or.inl (Or.inl inPrefix))
    · exact Or.inl same
    · exact Or.inr (Or.inl (Or.inr inActive))
    · exact Or.inr (Or.inr inWaiting)
  · rintro (same | (inPrefix | inActive) | inWaiting)
    · exact Or.inl (Or.inr (Or.inl same))
    · exact Or.inl (Or.inl inPrefix)
    · exact Or.inl (Or.inr (Or.inr inActive))
    · exact Or.inr inWaiting

private theorem flatMap_set_cons_nodup
    {α β : Type} {values : List α} {index : Nat}
    {before after : α} {mapping : α → List β} {inserted : β}
    (lookup : values[index]? = some before)
    (mapped : mapping after = inserted :: mapping before)
    (nodup : (values.flatMap mapping).Nodup)
    (fresh : inserted ∉ values.flatMap mapping) :
    ((values.set index after).flatMap mapping).Nodup := by
  induction values generalizing index with
  | nil => simp at lookup
  | cons head tail induction =>
      cases index with
      | zero =>
          simp at lookup
          subst before
          simpa [mapped] using (List.nodup_cons.mpr ⟨fresh, nodup⟩)
      | succ prior =>
          simp only [List.getElem?_cons_succ] at lookup
          simp only [List.set, List.flatMap_cons]
          rcases List.nodup_append.mp nodup with
            ⟨headNodup, tailNodup, cross⟩
          have freshParts :
              inserted ∉ mapping head ∧
                inserted ∉ tail.flatMap mapping := by
            simpa using fresh
          apply List.nodup_append.mpr
          refine ⟨headNodup,
            induction lookup tailNodup freshParts.2, ?_⟩
          intro left leftMem right rightMem equal
          have rightCases :=
            (mem_flatMap_set_cons_iff lookup mapped).mp rightMem
          rcases rightCases with rfl | rightOld
          · subst left
            exact freshParts.1 leftMem
          · exact cross left leftMem right rightOld equal

/-- `new` inserts its reached/partner pair between the old ready flattening
and the unchanged waiting payloads. -/
theorem operationalNewEnqueue?_queuedVertices_eq
    {state after : SequentialStackState} {reached partner : Vertex}
    (equation : state.operationalNewEnqueue? reached partner = some after) :
    after.queuedVertices = state.ready.flatten ++ [reached, partner] ++
      state.waitingVertices := by
  rcases (operationalNewEnqueue?_some_iff.mp equation) with ⟨step⟩
  rcases step.ready with
    ⟨positive, activeEq, activeLt, reachedBound, partnerBound, distinct,
      reachedAbsent, partnerAbsent, reachedUnmarked, partnerUnmarked,
      activeUndefined, freshUndefined⟩
  rw [step.after_eq]
  unfold SequentialStackState.queuedVertices
    SequentialStackState.waitingVertices
  simp only [List.flatten_append, List.flatten_cons, List.flatten_nil,
    List.append_nil]
  rw [array_flatMap_set_eq_of_getElem?_eq activeUndefined (by rfl)]

namespace NewStep

/-- The synchronized prefix of a successful `new` step, viewed as the
existing prepared transition. -/
private def prepared
    {certificate : Certificate} {before after : ReservationState}
    (step : NewStep certificate before after) : PreparedStep before where
  stackResult := step.stackResult
  coreMarked := step.coreMarked
  stack_eq := step.stack_eq
  core_mark_eq := step.core_mark_eq

/-- The pop/raw-mark middle state of `new` satisfies the complete scheduler
invariant. -/
theorem markedMiddle_schedulerInvariant
    {certificate : Certificate} {before after : ReservationState}
    (step : NewStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    SchedulerInvariant certificate step.markedMiddle :=
  step.prepared.schedulerInvariant invariant

private theorem submittedEndpoints_not_queued
    {certificate : Certificate} {before after : ReservationState}
    (step : NewStep certificate before after) :
    step.search.left ∉ step.stackResult.after.queuedVertices ∧
      step.search.right ∉ step.stackResult.after.queuedVertices := by
  rcases (SequentialStackState.operationalNewEnqueue?_some_iff.mp step.stack_enqueue_eq) with
    ⟨stackStep⟩
  have reachedAbsent := stackStep.ready.2.2.2.2.2.2.1
  have partnerAbsent := stackStep.ready.2.2.2.2.2.2.2.1
  rcases step.route.storedEndpoints with
    ⟨reachedEq, partnerEq⟩ | ⟨reachedEq, partnerEq⟩
  · exact ⟨by simpa [reachedEq] using reachedAbsent,
      by simpa [partnerEq] using partnerAbsent⟩
  · exact ⟨by simpa [partnerEq] using partnerAbsent,
      by simpa [reachedEq] using reachedAbsent⟩

private theorem submittedEndpoints_not_liveFrontier
    {certificate : Certificate} {before after : ReservationState}
    (step : NewStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    step.search.left ∉ step.coreMarked.liveFrontierVertices ∧
      step.search.right ∉ step.coreMarked.liveFrontierVertices := by
  have middleInvariant := step.markedMiddle_schedulerInvariant invariant
  have absent := step.submittedEndpoints_not_queued
  constructor
  · intro membership
    exact absent.1
      (middleInvariant.unmarked_liveFrontier_mem_queued
        membership step.search.leftReady)
  · intro membership
    exact absent.2
      (middleInvariant.unmarked_liveFrontier_mem_queued
        membership step.search.rightReady)

/-- Appending the exact submitted axiom preserves bidirectional,
occurrence-exact component ownership. -/
theorem componentForestProvenance
    {certificate : Certificate} {before after : ReservationState}
    (step : NewStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    certificate.ComponentForestProvenance after.core := by
  have middleInvariant := step.markedMiddle_schedulerInvariant invariant
  have endpointAbsent := step.submittedEndpoints_not_queued
  rw [step.output_eq]
  apply Certificate.ComponentForestProvenance.reserveAxiomAt?_of_fresh
    middleInvariant.structural middleInvariant.core_orderedParents
    middleInvariant.component_forest_provenance
  · intro left right linkLookup index component owned componentLookup accounted
    have submitted : Link.axiom left right =
        .axiom step.search.left step.search.right :=
      Option.some.inj (linkLookup.symm.trans step.search.exactLink)
    injection submitted with leftEq rightEq
    subst left
    subst right
    constructor
    · intro leftOwned
      exact endpointAbsent.1
        (middleInvariant.owned_unmarked_mem_queued
          componentLookup accounted leftOwned step.search.leftReady)
    · intro rightOwned
      exact endpointAbsent.2
        (middleInvariant.owned_unmarked_mem_queued
          componentLookup accounted rightOwned step.search.rightReady)
  · exact step.core_reserve_eq

/-- `new` appends one fresh live component and one matching fresh sigma
boundary while preserving the exact old component domain. -/
theorem componentDomainExact
    {certificate : Certificate} {before after : ReservationState}
    (step : NewStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    ComponentDomainExact after := by
  have middleInvariant := step.markedMiddle_schedulerInvariant invariant
  rcases SequentialStackState.operationalNewEnqueue?_exact step.stack_enqueue_eq with
    ⟨active, activeEquation, activeLt, stackMarksEq, nextAgeEq,
      sigmaEq, readyEq, waitingEq, activeWaiting, freshWaiting⟩
  rcases certificate.reserveAxiomAt?_exact step.core_reserve_eq with
    ⟨left, right, component, linkLookup, reservationReady, componentLookup,
      frontier, coreMarksEq, parentsEq, componentsEq, counterEq, firedEq⟩
  have freshIndex :
      step.coreMarked.components.size = step.stackResult.after.nextAge := by
    calc
      step.coreMarked.components.size = step.coreMarked.parents.size :=
        middleInvariant.core_carriers_aligned
      _ = step.stackResult.after.nextAge :=
        middleInvariant.realizesSigma.horizon_eq
  rw [step.output_eq]
  intro token
  rw [componentsEq, sigmaEq]
  constructor
  · rintro ⟨candidate, lookup⟩
    by_cases fresh : token = step.coreMarked.components.size
    · subst token
      exact List.mem_append_right _ (by simp [freshIndex])
    · have oldLookup :
          step.coreMarked.components[token]? = some (some candidate) := by
        simpa [Array.getElem?_push, fresh] using lookup
      have oldMembership :=
        (middleInvariant.component_domain_exact token).mp
          ⟨candidate, oldLookup⟩
      exact List.mem_append_left _ oldMembership
  · intro membership
    simp only [List.mem_append, List.mem_singleton] at membership
    rcases membership with oldMembership | tokenFresh
    · rcases (middleInvariant.component_domain_exact token).mpr oldMembership with
        ⟨candidate, oldLookup⟩
      change step.coreMarked.components[token]? = some (some candidate) at oldLookup
      refine ⟨candidate, ?_⟩
      have tokenBound := (Array.getElem?_eq_some_iff.mp oldLookup).1
      simpa [Array.getElem?_push, Nat.ne_of_lt tokenBound] using oldLookup
    · subst token
      refine ⟨component, ?_⟩
      rw [← freshIndex]
      exact Array.getElem?_push_size

/-- The two exact endpoints of the newly reserved axiom are fresh against all
old live frontiers, so appending its frontier preserves global occurrence
uniqueness. -/
theorem liveFrontiersNodup
    {certificate : Certificate} {before after : ReservationState}
    (step : NewStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    LiveFrontiersNodup after := by
  have middleInvariant := step.markedMiddle_schedulerInvariant invariant
  have endpointAbsent := step.submittedEndpoints_not_liveFrontier invariant
  rcases certificate.reserveAxiomAt?_exact step.core_reserve_eq with
    ⟨left, right, component, linkLookup, reservationReady, componentLookup,
      frontier, coreMarksEq, parentsEq, componentsEq, counterEq, firedEq⟩
  have submitted :
      Link.axiom left right = .axiom step.search.left step.search.right :=
    Option.some.inj (linkLookup.symm.trans step.search.exactLink)
  injection submitted with leftEq rightEq
  subst left
  subst right
  have different : step.search.left ≠ step.search.right :=
    ((certificate.linkLocallyWellFormed_iff
      (.axiom step.search.left step.search.right)).mp reservationReady.1).1
  rw [step.output_eq]
  unfold LiveFrontiersNodup UnificationState.liveFrontierVertices
  rw [componentsEq]
  simp only [Array.toList_push, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, Option.map_some, Option.getD_some, List.append_nil]
  rw [frontier]
  apply List.nodup_append.mpr
  refine ⟨middleInvariant.live_frontiers_nodup, by simp [different], ?_⟩
  intro vertex oldMembership newVertex newMembership
  simp only [List.mem_cons, List.not_mem_nil, or_false] at newMembership
  rcases newMembership with rfl | rfl
  · intro equal
    subst vertex
    exact endpointAbsent.1 oldMembership
  · intro equal
    subst vertex
    exact endpointAbsent.2 oldMembership

/-- Every old ready bucket retains its exact live frontier, and the new top
bucket is exactly the raw-unmarked frontier of the fresh axiom component. -/
theorem readyBucketFrontierExact
    {certificate : Certificate} {before after : ReservationState}
    (step : NewStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    ReadyBucketFrontierExact after := by
  have middleInvariant := step.markedMiddle_schedulerInvariant invariant
  rcases SequentialStackState.operationalNewEnqueue?_exact step.stack_enqueue_eq with
    ⟨active, activeEquation, activeLt, stackMarksEq, nextAgeEq,
      sigmaEq, readyEq, waitingEq, activeWaiting, freshWaiting⟩
  rcases certificate.reserveAxiomAt?_exact step.core_reserve_eq with
    ⟨left, right, component, linkLookup, reservationReady, componentLookup,
      frontier, coreMarksEq, parentsEq, componentsEq, counterEq, firedEq⟩
  have submitted :
      Link.axiom left right = .axiom step.search.left step.search.right :=
    Option.some.inj (linkLookup.symm.trans step.search.exactLink)
  injection submitted with leftEq rightEq
  subst left
  subst right
  have freshIndex :
      step.coreMarked.components.size = step.stackResult.after.nextAge := by
    calc
      step.coreMarked.components.size = step.coreMarked.parents.size :=
        middleInvariant.core_carriers_aligned
      _ = step.stackResult.after.nextAge :=
        middleInvariant.realizesSigma.horizon_eq
  have aligned :
      step.stackResult.after.ready.length =
        step.stackResult.after.sigma.length :=
    middleInvariant.stack_wellShaped.ready_aligned
  rw [step.output_eq]
  intro position boundary bucket sigmaLookup readyLookup
  have positionBound :
      position <
        (step.stackResult.after.sigma ++
          [step.stackResult.after.nextAge]).length := by
    rw [← sigmaEq]
    exact (List.getElem?_eq_some_iff.mp sigmaLookup).1
  by_cases oldPosition : position < step.stackResult.after.sigma.length
  · have oldSigmaLookup :
        step.stackResult.after.sigma[position]? = some boundary := by
      rw [sigmaEq, List.getElem?_append_left oldPosition] at sigmaLookup
      exact sigmaLookup
    have oldReadyPosition :
        position < step.stackResult.after.ready.length := by
      rw [aligned]
      exact oldPosition
    have oldReadyLookup :
        step.stackResult.after.ready[position]? = some bucket := by
      rw [readyEq, List.getElem?_append_left oldReadyPosition] at readyLookup
      exact readyLookup
    rcases middleInvariant.ready_bucket_frontier_exact
        oldSigmaLookup oldReadyLookup with
      ⟨oldComponent, oldComponentLookup, exactMembership⟩
    change step.coreMarked.components[boundary]? =
      some (some oldComponent) at oldComponentLookup
    have boundaryBound := (Array.getElem?_eq_some_iff.mp oldComponentLookup).1
    refine ⟨oldComponent, ?_, ?_⟩
    · rw [componentsEq]
      simpa [Array.getElem?_push, Nat.ne_of_lt boundaryBound] using
        oldComponentLookup
    · intro vertex
      rw [coreMarksEq]
      exact exactMembership vertex
  · have finalPosition :
        position = step.stackResult.after.sigma.length := by
      simp only [List.length_append, List.length_singleton] at positionBound
      omega
    subst position
    have boundaryEq : boundary = step.stackResult.after.nextAge := by
      rw [sigmaEq] at sigmaLookup
      simp at sigmaLookup
      exact sigmaLookup.symm
    have bucketEq : bucket = [step.reached, step.partner] := by
      rw [readyEq] at readyLookup
      rw [show step.stackResult.after.sigma.length =
        step.stackResult.after.ready.length from aligned.symm] at readyLookup
      simp at readyLookup
      exact readyLookup.symm
    subst boundary
    subst bucket
    refine ⟨component, ?_, ?_⟩
    · rw [componentsEq, ← freshIndex]
      exact Array.getElem?_push_size
    · intro vertex
      rw [frontier, coreMarksEq]
      rcases step.route.storedEndpoints with
        ⟨reachedEq, partnerEq⟩ | ⟨reachedEq, partnerEq⟩
      · simp only [reachedEq, partnerEq, List.mem_cons,
          List.not_mem_nil, or_false]
        constructor
        · intro membership
          rcases membership with rfl | rfl
          · exact ⟨Or.inl rfl, step.search.leftReady⟩
          · exact ⟨Or.inr rfl, step.search.rightReady⟩
        · exact fun pair => pair.1
      · simp only [reachedEq, partnerEq, List.mem_cons,
          List.not_mem_nil, or_false]
        constructor
        · intro membership
          rcases membership with rfl | rfl
          · exact ⟨Or.inr rfl, step.search.rightReady⟩
          · exact ⟨Or.inl rfl, step.search.leftReady⟩
        · intro pair
          rcases pair.1 with rfl | rfl
          · exact Or.inr rfl
          · exact Or.inl rfl

/-- The fresh reached/partner pair is disjoint from both old ready work and old
waiting payloads, so the exact post-`new` queue remains duplicate-free. -/
theorem queuedVerticesNodup
    {certificate : Certificate} {before after : ReservationState}
    (step : NewStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    QueuedVerticesNodup after := by
  have middleInvariant := step.markedMiddle_schedulerInvariant invariant
  rcases (SequentialStackState.operationalNewEnqueue?_some_iff.mp
      step.stack_enqueue_eq) with
    ⟨stackStep⟩
  rcases stackStep.ready with
    ⟨positive, activeEq, activeLt, reachedBound, partnerBound, distinct,
      reachedAbsent, partnerAbsent, reachedUnmarked, partnerUnmarked,
      activeUndefined, freshUndefined⟩
  have oldParts :=
    List.nodup_append.mp middleInvariant.queued_vertices_nodup
  have pairNodup : [step.reached, step.partner].Nodup := by
    simp [distinct]
  have pairAbsentReady : ∀ vertex ∈ [step.reached, step.partner],
      vertex ∉ step.stackResult.after.ready.flatten := by
    intro vertex membership
    simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
    rcases membership with rfl | rfl
    · intro old
      exact reachedAbsent (List.mem_append_left _ old)
    · intro old
      exact partnerAbsent (List.mem_append_left _ old)
  have pairAbsentWaiting : ∀ vertex ∈ [step.reached, step.partner],
      vertex ∉ step.stackResult.after.waitingVertices := by
    intro vertex membership
    simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
    rcases membership with rfl | rfl
    · intro old
      exact reachedAbsent (List.mem_append_right _ old)
    · intro old
      exact partnerAbsent (List.mem_append_right _ old)
  rw [step.output_eq]
  unfold QueuedVerticesNodup
  rw [operationalNewEnqueue?_queuedVertices_eq step.stack_enqueue_eq]
  apply List.nodup_append.mpr
  refine ⟨?_, oldParts.2.1, ?_⟩
  · apply List.nodup_append.mpr
    refine ⟨oldParts.1, pairNodup, ?_⟩
    intro old oldMembership new newMembership equal
    subst old
    exact pairAbsentReady new newMembership oldMembership
  · intro candidate membership waitingVertex waitingMembership equal
    simp only [List.mem_append] at membership
    rcases membership with oldReady | newPair
    · exact oldParts.2.2 candidate oldReady waitingVertex
        waitingMembership equal
    · subst candidate
      exact pairAbsentWaiting waitingVertex newPair waitingMembership

/-- Every post-`new` queued occurrence is raw-unmarked in the production core,
including both orientations of the newly discovered axiom endpoints. -/
theorem queuedVerticesUnmarked
    {certificate : Certificate} {before after : ReservationState}
    (step : NewStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    QueuedVerticesUnmarked after := by
  have middleInvariant := step.markedMiddle_schedulerInvariant invariant
  rcases certificate.reserveAxiomAt?_exact step.core_reserve_eq with
    ⟨left, right, component, linkLookup, ready, componentLookup,
      frontier, coreMarksEq, parentsEq, componentsEq, counterEq, firedEq⟩
  rw [step.output_eq]
  intro vertex membership
  rw [operationalNewEnqueue?_queuedVertices_eq step.stack_enqueue_eq] at membership
  simp only [List.mem_append] at membership
  rcases membership with oldOrNew | oldWaiting
  · rcases oldOrNew with oldReady | newEndpoint
    · rw [coreMarksEq]
      exact middleInvariant.queued_vertices_unmarked vertex
        (by
          unfold SequentialStackState.queuedVertices
          exact List.mem_append_left _ oldReady)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at newEndpoint
      rcases newEndpoint with reachedEq | partnerEq
      · subst vertex
        rw [coreMarksEq]
        rcases step.route.storedEndpoints with
          ⟨rEq, pEq⟩ | ⟨rEq, pEq⟩
        · simpa [rEq] using step.search.leftReady
        · simpa [rEq] using step.search.rightReady
      · subst vertex
        rw [coreMarksEq]
        rcases step.route.storedEndpoints with
          ⟨rEq, pEq⟩ | ⟨rEq, pEq⟩
        · simpa [pEq] using step.search.rightReady
        · simpa [pEq] using step.search.leftReady
  · rw [coreMarksEq]
    exact middleInvariant.queued_vertices_unmarked vertex
      (by
        unfold SequentialStackState.queuedVertices
        exact List.mem_append_right _ oldWaiting)

/-- Reserving a fresh axiom cannot forge a connective conclusion: structural
typing separates its atomic endpoints, while old produced conclusions retain
their marked premises. -/
theorem producedPremisesMarked
    {certificate : Certificate} {before after : ReservationState}
    (step : NewStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    ProducedPremisesMarked certificate after := by
  have middleInvariant := step.markedMiddle_schedulerInvariant invariant
  rcases certificate.reserveAxiomAt?_exact step.core_reserve_eq with
    ⟨axiomLeft, axiomRight, component, axiomLookup, ready,
      componentLookup, frontier, marksEq, parentsEq, componentsEq,
      counterEq, firedEq⟩
  have axiomMembership :
      (.axiom axiomLeft axiomRight : Link) ∈ certificate.links :=
    List.mem_of_getElem? axiomLookup
  rw [step.output_eq]
  intro link linkMembership
  cases link with
  | «axiom» left right => trivial
  | tensor premiseLeft premiseRight conclusion
  | «par» premiseLeft premiseRight conclusion =>
      intro producedAfter
      have producedMiddle : Produced step.markedMiddle conclusion := by
        rcases producedAfter with ⟨age, markedAfter⟩ | frontierAfter
        · apply Or.inl
          refine ⟨age, ?_⟩
          rw [marksEq] at markedAfter
          exact markedAfter
        · unfold UnificationState.liveFrontierVertices at frontierAfter
          rw [componentsEq] at frontierAfter
          simp only [Array.toList_push, List.flatMap_append,
            List.flatMap_cons, List.flatMap_nil, Option.map_some,
            Option.getD_some, List.append_nil, List.mem_append] at frontierAfter
          rcases frontierAfter with oldFrontier | newFrontier
          · exact Or.inr oldFrontier
          · rw [frontier] at newFrontier
            have endpoint :
                conclusion = axiomLeft ∨ conclusion = axiomRight := by
              simpa using newFrontier
            rcases StructurallyWellFormed.axiomEndpointFormula_of_mem
                middleInvariant.structural axiomMembership endpoint with
              ⟨name, positive, atomFormula⟩
            have connectiveWellFormed :=
              middleInvariant.structural.2.2.2.2.1 _ linkMembership
            rcases connectiveWellFormed with
              ⟨_, _, _, _, _, _, typing⟩
            cases leftFormula : certificate.formula? premiseLeft <;>
              cases rightFormula : certificate.formula? premiseRight <;>
              simp [leftFormula, rightFormula, atomFormula] at typing
      rcases middleInvariant.produced_premises_marked
          linkMembership producedMiddle with
        ⟨⟨leftAge, leftMarked⟩, rightAge, rightMarked⟩
      refine ⟨⟨leftAge, ?_⟩, rightAge, ?_⟩
      · rw [marksEq]
        exact leftMarked
      · rw [marksEq]
        exact rightMarked

/-- Appending an axiom component contributes zero logical connectives, so the
production firing counter remains exactly the live connective count. -/
theorem firedCounterExact
    {certificate : Certificate} {before after : ReservationState}
    (step : NewStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    FiredCounterExact after := by
  have middleInvariant := step.markedMiddle_schedulerInvariant invariant
  rcases certificate.reserveAxiomAt?_exact step.core_reserve_eq with
    ⟨left, right, component, linkLookup, ready, componentLookup,
      frontier, marksEq, parentsEq, componentsEq, counterEq, firedEq⟩
  rcases Certificate.UnificationComponent.axiom?_success componentLookup with
    ⟨name, positive, leftFormula, componentEq⟩
  have middleCounter := middleInvariant.fired_counter_exact
  unfold FiredCounterExact UnificationState.liveConnectiveCount at middleCounter
  change step.coreMarked.firedConnectives =
    step.coreMarked.components.toList.foldl
      (fun total cell => total +
        (cell.map UnificationComponent.connectiveCount).getD 0) 0 at middleCounter
  rw [step.output_eq]
  unfold FiredCounterExact UnificationState.liveConnectiveCount
  rw [firedEq, componentsEq]
  simp only [Array.toList_push, List.foldl_append, List.foldl_cons,
    List.foldl_nil, Option.map_some, Option.getD_some]
  rw [componentEq]
  simpa [UnificationComponent.connectiveCount,
    CutFreeDerivation.connectiveCount] using middleCounter

/-- Initializing the old active waiting cell to empty adds no promise; every
old payload and both of its sigma-boundary lookups survive the fresh append. -/
theorem waitingSpanExact
    {certificate : Certificate} {before after : ReservationState}
    (step : NewStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    WaitingSpanExact certificate after := by
  have middleInvariant := step.markedMiddle_schedulerInvariant invariant
  have middleMarks :
      step.coreMarked.marks = step.stackResult.after.marks :=
    middleInvariant.realizesSigma.marks_eq
  rcases SequentialStackState.operationalNewEnqueue?_exact
      step.stack_enqueue_eq with
    ⟨active, activeEquation, activeLt, stackMarksEq, nextAgeEq,
      sigmaEq, readyEq, waitingEq, activeWaiting, freshWaiting⟩
  rcases certificate.reserveAxiomAt?_exact step.core_reserve_eq with
    ⟨axiomLeft, axiomRight, component, axiomLookup, reservationReady,
      componentLookup, frontier, coreMarksEq, parentsEq, componentsEq,
      counterEq, firedEq⟩
  have activeUndefined :
      step.stackResult.after.waiting[active]? = some .undefined :=
    middleInvariant.stack_operationalWaitingDomain.active_undefined
      middleInvariant.stack_wellShaped activeEquation
  rw [step.output_eq]
  unfold WaitingSpanExact
  intro boundary payload conclusion waitingLookup conclusionMembership
  by_cases same : boundary = active
  · subst boundary
    rw [waitingEq] at waitingLookup
    have activeBound := (Array.getElem?_eq_some_iff.mp activeUndefined).1
    rw [Array.getElem?_setIfInBounds] at waitingLookup
    simp [activeBound] at waitingLookup
    subst payload
    simp at conclusionMembership
  · have oldWaitingLookup :
        step.stackResult.after.waiting[boundary]? =
          some (.initialized payload) := by
      rw [waitingEq] at waitingLookup
      rw [Array.getElem?_setIfInBounds_ne (Ne.symm same)] at waitingLookup
      exact waitingLookup
    rcases middleInvariant.waiting_span_exact
        oldWaitingLookup conclusionMembership with
      ⟨linkIndex, left, right, olderPremise, youngerPremise, olderAge,
        youngerAge, youngerBoundary, linkLookup, sourceLookup,
        conclusionUnmarked, orientation, olderMarked, youngerMarked,
        olderSigma, youngerSigma, boundaryOrder⟩
    change step.coreMarked.marks[conclusion]? =
      some none at conclusionUnmarked
    change step.coreMarked.marks[olderPremise]? =
      some (some olderAge) at olderMarked
    change step.coreMarked.marks[youngerPremise]? =
      some (some youngerAge) at youngerMarked
    change sigmaBoundary? step.stackResult.after.sigma olderAge =
      some boundary at olderSigma
    change sigmaBoundary? step.stackResult.after.sigma youngerAge =
      some youngerBoundary at youngerSigma
    have stackOlderMarked :
        step.stackResult.after.marks[olderPremise]? =
          some (some olderAge) := by
      rw [← middleMarks]
      exact olderMarked
    have stackYoungerMarked :
        step.stackResult.after.marks[youngerPremise]? =
          some (some youngerAge) := by
      rw [← middleMarks]
      exact youngerMarked
    have olderAgeBound : olderAge < step.stackResult.after.nextAge :=
      middleInvariant.stack_wellShaped.assigned_age_bound
        olderPremise olderAge stackOlderMarked
    have youngerAgeBound : youngerAge < step.stackResult.after.nextAge :=
      middleInvariant.stack_wellShaped.assigned_age_bound
        youngerPremise youngerAge stackYoungerMarked
    refine ⟨linkIndex, left, right, olderPremise, youngerPremise,
      olderAge, youngerAge, youngerBoundary, linkLookup, sourceLookup,
      ?_, orientation, ?_, ?_, ?_, ?_, boundaryOrder⟩
    · rw [coreMarksEq]
      exact conclusionUnmarked
    · rw [coreMarksEq]
      exact olderMarked
    · rw [coreMarksEq]
      exact youngerMarked
    · rw [sigmaEq, sigmaBoundary?_append_fresh_old olderAgeBound]
      exact olderSigma
    · rw [sigmaEq, sigmaBoundary?_append_fresh_old youngerAgeBound]
      exact youngerSigma

/-- Every old pending premise remains covered by the same live component after
the fresh axiom append; the newly queued endpoint pair is excluded by the
ready-side exception. -/
theorem pendingPremisesCoveredExceptReady
    {certificate : Certificate} {before after : ReservationState}
    (step : NewStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    PendingPremisesCoveredExceptReady certificate after := by
  have middleInvariant := step.markedMiddle_schedulerInvariant invariant
  have middleOrdered : step.coreMarked.OrderedParents :=
    middleInvariant.core_orderedParents
  rcases SequentialStackState.operationalNewEnqueue?_exact
      step.stack_enqueue_eq with
    ⟨active, activeEquation, activeLt, stackMarksEq, nextAgeEq,
      sigmaEq, stackReadyEq, waitingEq, activeWaiting, freshWaiting⟩
  rcases certificate.reserveAxiomAt?_exact step.core_reserve_eq with
    ⟨axiomLeft, axiomRight, newComponent, axiomLookup, reservationReady,
      newComponentLookup, frontier, coreMarksEq, parentsEq, componentsEq,
      counterEq, firedEq⟩
  rw [step.output_eq]
  intro link linkMembership
  cases link with
  | «axiom» left right => trivial
  | tensor left right conclusion
  | «par» left right conclusion =>
      intro conclusionUnmarked conclusionNotReady premise token
        premiseMembership tokenAt
      have middleConclusionUnmarked :
          step.coreMarked.marks[conclusion]? = some none := by
        rw [coreMarksEq] at conclusionUnmarked
        exact conclusionUnmarked
      have middleConclusionNotReady :
          conclusion ∉ step.stackResult.after.ready.flatten := by
        intro oldMembership
        apply conclusionNotReady
        rw [stackReadyEq]
        simp only [List.flatten_append]
        exact List.mem_append_left _ oldMembership
      change step.coreAfter.tokenAt? premise = some token at tokenAt
      have tokenEq :
          step.coreAfter.tokenAt? premise =
            step.coreMarked.tokenAt? premise :=
        certificate.reserveAxiomAt?_tokenAt_eq
          middleOrdered step.core_reserve_eq premise
      have middleTokenAt :
          step.coreMarked.tokenAt? premise = some token :=
        tokenEq.symm.trans tokenAt
      rcases middleInvariant.pending_premises_covered_except_ready
          linkMembership middleConclusionUnmarked middleConclusionNotReady
          premiseMembership middleTokenAt with
        ⟨component, middleComponentLookup, premiseFrontier⟩
      refine ⟨component, ?_, premiseFrontier⟩
      exact certificate.reserveAxiomAt?_componentAt?_of_some
        middleOrdered step.core_reserve_eq middleComponentLookup

/-- A successful deterministic Figure-7 `new` step preserves every field of
the current occurrence-exact, state-only scheduler invariant.  This theorem is
preservation only; it does not assert executable success or progress. -/
theorem schedulerInvariant
    {certificate : Certificate} {before after : ReservationState}
    (step : NewStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    SchedulerInvariant certificate after := by
  exact {
    toReservationInvariant := step.reservationInvariant
    structural := invariant.structural
    component_domain_exact := step.componentDomainExact invariant
    component_forest_provenance :=
      step.componentForestProvenance invariant
    live_frontiers_nodup := step.liveFrontiersNodup invariant
    ready_bucket_frontier_exact :=
      step.readyBucketFrontierExact invariant
    queued_vertices_nodup := step.queuedVerticesNodup invariant
    queued_vertices_unmarked := step.queuedVerticesUnmarked invariant
    produced_premises_marked := step.producedPremisesMarked invariant
    waiting_span_exact := step.waitingSpanExact invariant
    pending_premises_covered_except_ready :=
      step.pendingPremisesCoveredExceptReady invariant
    fired_counter_exact := step.firedCounterExact invariant }

end NewStep

/-- Executable `new?` success preserves the complete current scheduler
invariant.  Totality and dispatcher progress remain separate obligations. -/
theorem new?_schedulerInvariant
    {certificate : Certificate} {before after : ReservationState}
    (invariant : SchedulerInvariant certificate before)
    (equation :
      new? certificate before invariant.toReservationInvariant = some after) :
    SchedulerInvariant certificate after := by
  rcases (new?_some_iff invariant.toReservationInvariant).mp equation with
    ⟨step⟩
  exact step.schedulerInvariant invariant

namespace ForwardStep

private theorem par_wellFormed
    {certificate : Certificate} {before after : ReservationState}
    (step : ForwardStep certificate before after) :
    certificate.LinkWellFormed
      (.par step.consumer.storedLeft step.consumer.storedRight
        step.consumer.conclusion) := by
  simpa [step.par_eq, SequentialConnectiveKind.asLink] using
    step.consumer.wellFormed

private theorem premise_orientation
    {certificate : Certificate} {before after : ReservationState}
    (step : ForwardStep certificate before after) :
    ((step.consumer.mate = step.consumer.storedLeft ∧
        step.prepared.stackResult.vertex = step.consumer.storedRight) ∨
      (step.consumer.mate = step.consumer.storedRight ∧
        step.prepared.stackResult.vertex = step.consumer.storedLeft)) := by
  cases sideEquation : step.consumer.side with
  | storedLeft =>
      right
      constructor
      · simp [ConnectiveBelow.mate, TensorPremiseSide.mate,
          sideEquation]
      · simpa [TensorBelow.premise, TensorPremiseSide.premise,
          sideEquation] using
          step.consumer.premise_eq
  | storedRight =>
      left
      constructor
      · simp [ConnectiveBelow.mate, TensorPremiseSide.mate,
          sideEquation]
      · simpa [TensorBelow.premise, TensorPremiseSide.premise,
          sideEquation] using
          step.consumer.premise_eq

private theorem conclusion_ne_selected
    {certificate : Certificate} {before after : ReservationState}
    (step : ForwardStep certificate before after) :
    step.consumer.conclusion ≠ step.prepared.stackResult.vertex := by
  have parWellFormed := step.par_wellFormed
  cases sideEquation : step.consumer.side with
  | storedLeft =>
      have selectedEq : step.prepared.stackResult.vertex =
          step.consumer.storedLeft := by
        simpa [TensorBelow.premise, TensorPremiseSide.premise,
          sideEquation] using
          step.consumer.premise_eq
      intro same
      exact parWellFormed.2.1 (selectedEq.symm.trans same.symm)
  | storedRight =>
      have selectedEq : step.prepared.stackResult.vertex =
          step.consumer.storedRight := by
        simpa [TensorBelow.premise, TensorPremiseSide.premise,
          sideEquation] using
          step.consumer.premise_eq
      intro same
      exact parWellFormed.2.2.1 (selectedEq.symm.trans same.symm)

private theorem conclusion_not_produced_before
    {certificate : Certificate} {before after : ReservationState}
    (step : ForwardStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    ¬ Produced before step.consumer.conclusion := by
  intro produced
  have linkMembership :
      (.par step.consumer.storedLeft step.consumer.storedRight
        step.consumer.conclusion : Link) ∈ certificate.links :=
    List.mem_of_getElem? step.submitted_par
  rcases invariant.produced_premises_marked linkMembership produced with
    ⟨⟨leftAge, leftMarked⟩, rightAge, rightMarked⟩
  rcases UnificationState.markReadyRaw?_exact
      step.prepared.core_mark_eq with
    ⟨selectedUnmarked, _, _, _, _, _, _⟩
  cases sideEquation : step.consumer.side with
  | storedLeft =>
      have selectedEq : step.prepared.stackResult.vertex =
          step.consumer.storedLeft := by
        simpa [TensorBelow.premise, TensorPremiseSide.premise,
          sideEquation] using
          step.consumer.premise_eq
      have leftUnmarked :
          before.core.marks[step.consumer.storedLeft]? = some none :=
        (congrArg (fun vertex => before.core.marks[vertex]?)
          selectedEq).symm.trans selectedUnmarked
      rw [leftUnmarked] at leftMarked
      simp at leftMarked
  | storedRight =>
      have selectedEq : step.prepared.stackResult.vertex =
          step.consumer.storedRight := by
        simpa [TensorBelow.premise, TensorPremiseSide.premise,
          sideEquation] using
          step.consumer.premise_eq
      have rightUnmarked :
          before.core.marks[step.consumer.storedRight]? = some none :=
        (congrArg (fun vertex => before.core.marks[vertex]?)
          selectedEq).symm.trans selectedUnmarked
      rw [rightUnmarked] at rightMarked
      simp at rightMarked

private theorem conclusion_not_produced_middle
    {certificate : Certificate} {before after : ReservationState}
    (step : ForwardStep certificate before after)
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
    (step : ForwardStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    step.consumer.conclusion ∉ before.stack.waitingVertices := by
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
          (.par oldLeft oldRight step.consumer.conclusion : Link) ∈
            certificate.links :=
        List.mem_of_getElem? oldLinkLookup
      have currentLinkMembership :
          (.par step.consumer.storedLeft step.consumer.storedRight
            step.consumer.conclusion : Link) ∈ certificate.links :=
        List.mem_of_getElem? step.submitted_par
      have linkEq := invariant.structural.par_producer_unique
        oldLinkMembership currentLinkMembership
      injection linkEq with leftEq rightEq
      subst oldLeft
      subst oldRight
      rcases UnificationState.markReadyRaw?_exact
          step.prepared.core_mark_eq with
        ⟨selectedUnmarked, _, _, _, _, _, _⟩
      cases sideEquation : step.consumer.side with
      | storedLeft =>
          have selectedEq : step.prepared.stackResult.vertex =
              step.consumer.storedLeft := by
            simpa [TensorPremiseSide.premise, sideEquation] using
              step.consumer.premise_eq
          have selectedMarked :
              before.core.marks[step.prepared.stackResult.vertex]? =
                some (some olderAge) ∨
              before.core.marks[step.prepared.stackResult.vertex]? =
                some (some youngerAge) := by
            rcases oldOrientation with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact Or.inl (by simpa [selectedEq] using olderMarked)
            · exact Or.inr (by simpa [selectedEq] using youngerMarked)
          rcases selectedMarked with marked | marked <;>
            rw [selectedUnmarked] at marked <;> simp at marked
      | storedRight =>
          have selectedEq : step.prepared.stackResult.vertex =
              step.consumer.storedRight := by
            simpa [TensorPremiseSide.premise, sideEquation] using
              step.consumer.premise_eq
          have selectedMarked :
              before.core.marks[step.prepared.stackResult.vertex]? =
                some (some olderAge) ∨
              before.core.marks[step.prepared.stackResult.vertex]? =
                some (some youngerAge) := by
            rcases oldOrientation with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact Or.inr (by simpa [selectedEq] using youngerMarked)
            · exact Or.inl (by simpa [selectedEq] using olderMarked)
          rcases selectedMarked with marked | marked <;>
            rw [selectedUnmarked] at marked <;> simp at marked

private theorem conclusion_not_mem_waiting_middle
    {certificate : Certificate} {before after : ReservationState}
    (step : ForwardStep certificate before after)
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
    (step : ForwardStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    step.consumer.conclusion ∉
      step.prepared.after.stack.queuedVertices := by
  intro queued
  unfold SequentialStackState.queuedVertices at queued
  rcases List.mem_append.mp queued with ready | waiting
  · exact step.conclusion_not_produced_middle invariant
      (Or.inr
        (SchedulerInvariant.ready_mem_liveFrontier
          (step.prepared.schedulerInvariant invariant) ready))
  · exact step.conclusion_not_mem_waiting_middle invariant waiting

private theorem active_root
    {certificate : Certificate} {before after : ReservationState}
    (step : ForwardStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    step.prepared.coreMarked.representative step.queueStep.outputToken =
      step.queueStep.outputToken := by
  have middleInvariant := step.prepared.schedulerInvariant invariant
  rcases SequentialStackState.popReadyMark?_exact
      step.prepared.stack_eq with
    ⟨_, sigmaTopEquation, _, _, _, stackSigmaEq, _, _, selectedMarked⟩
  have middleSigmaTop :
      step.prepared.after.stack.sigma.getLast? =
        some step.prepared.stackResult.rawAge := by
    change step.prepared.stackResult.after.sigma.getLast? = _
    rw [stackSigmaEq]
    exact sigmaTopEquation
  have ageBound :
      step.prepared.stackResult.rawAge <
        step.prepared.after.stack.nextAge :=
    middleInvariant.stack_wellShaped.assigned_age_bound
      step.prepared.stackResult.vertex
      step.prepared.stackResult.rawAge selectedMarked
  have boundaryLookup :
      sigmaBoundary? step.prepared.after.stack.sigma
          step.prepared.stackResult.rawAge =
        some step.prepared.stackResult.rawAge :=
    middleInvariant.stack_wellShaped.sigma_partition
      |>.sigmaBoundary?_eq_top middleSigmaTop
  have representativeLookup :=
    middleInvariant.realizesSigma.representative_eq_boundary ageBound
  have root :
      step.prepared.coreMarked.representative
          step.prepared.stackResult.rawAge =
        step.prepared.stackResult.rawAge :=
    Option.some.inj (representativeLookup.symm.trans boundaryLookup)
  simpa [step.output_token_eq_active] using root

private theorem active_component_lookup
    {certificate : Certificate} {before after : ReservationState}
    (step : ForwardStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    step.prepared.coreMarked.components[step.queueStep.outputToken]? =
      some (some step.queueStep.component) := by
  have rawLookup :=
    UnificationState.componentAt?_some_raw
      step.queueStep.component_lookup
  simpa [step.active_root invariant] using rawLookup

private theorem componentForestProvenance
    {certificate : Certificate} {before after : ReservationState}
    (step : ForwardStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    certificate.ComponentForestProvenance after.core := by
  have middleInvariant := step.prepared.schedulerInvariant invariant
  have conclusionFresh :
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
      change step.prepared.after.core.components[index]? =
        some (some component) at componentLookup
      change step.consumer.conclusion ∈
        step.prepared.after.core.liveFrontierVertices
      unfold UnificationState.liveFrontierVertices
      apply List.mem_flatMap.mpr
      refine ⟨some component, ?_, ?_⟩
      · exact List.mem_of_getElem? (by simpa using componentLookup)
      · simpa using frontier
  have forestAfterCore :=
    middleInvariant.component_forest_provenance
      |>.queueParStep_of_root_fresh step.queueStep
        (step.active_root invariant)
        step.consumer.linkIndex step.submitted_par conclusionFresh
  have coreEq : after.core = step.coreAfter :=
    congrArg (fun state : ReservationState => state.core) step.output_eq
  rw [coreEq]
  exact forestAfterCore

private theorem perm_insert_after
    {α : Type} (initial suffix : List α) (inserted : α) :
    (initial ++ inserted :: suffix).Perm
      (inserted :: (initial ++ suffix)) := by
  induction initial with
  | nil => simp
  | cons head tail induction =>
      simp only [List.cons_append]
      exact (List.Perm.cons head induction).trans
        (List.Perm.swap inserted head (tail ++ suffix))

private theorem queuedVertices_perm
    {certificate : Certificate} {before after : ReservationState}
    (step : ForwardStep certificate before after) :
    after.stack.queuedVertices.Perm
      (step.consumer.conclusion ::
        step.prepared.after.stack.queuedVertices) := by
  have afterStackEq : after.stack = step.stackAfter :=
    congrArg (fun state : ReservationState => state.stack) step.output_eq
  rw [afterStackEq, step.prependStep.after_eq]
  unfold SequentialStackState.queuedVertices
    SequentialStackState.waitingVertices
  change
    ((step.prependStep.readyPrefix ++
          [step.consumer.conclusion :: step.prependStep.activeReady]).flatten ++
        step.prepared.stackResult.after.waiting.toList.flatMap
          WaitingCell.vertices).Perm
      (step.consumer.conclusion ::
        (step.prepared.stackResult.after.ready.flatten ++
          step.prepared.stackResult.after.waiting.toList.flatMap
            WaitingCell.vertices))
  rw [step.prependStep.ready_eq]
  simp only [List.flatten_append, List.flatten_cons, List.flatten_nil,
    List.append_nil]
  simp only [List.append_assoc, List.cons_append]
  exact
    perm_insert_after step.prependStep.readyPrefix.flatten
      (step.prependStep.activeReady ++
        step.prepared.stackResult.after.waiting.toList.flatMap
          WaitingCell.vertices)
      step.consumer.conclusion

private theorem queuedVerticesNodup
    {certificate : Certificate} {before after : ReservationState}
    (step : ForwardStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    QueuedVerticesNodup after := by
  have middleInvariant := step.prepared.schedulerInvariant invariant
  have targetNodup :
      (step.consumer.conclusion ::
        step.prepared.after.stack.queuedVertices).Nodup :=
    List.nodup_cons.mpr
      ⟨step.conclusion_not_queued_middle invariant,
        middleInvariant.queued_vertices_nodup⟩
  exact step.queuedVertices_perm.symm.nodup targetNodup

private theorem queuedVerticesUnmarked
    {certificate : Certificate} {before after : ReservationState}
    (step : ForwardStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    QueuedVerticesUnmarked after := by
  have middleInvariant := step.prepared.schedulerInvariant invariant
  have marksEq : after.core.marks =
      step.prepared.after.core.marks := by
    have afterCoreEq : after.core = step.coreAfter :=
      congrArg (fun state : ReservationState => state.core) step.output_eq
    rw [afterCoreEq, step.queueStep.after_eq]
    rfl
  intro vertex membership
  have targetMembership := step.queuedVertices_perm.mem_iff.mp membership
  simp only [List.mem_cons] at targetMembership
  rcases targetMembership with rfl | oldMembership
  · rw [marksEq]
    exact (UnificationState.forwardToken?_success
      step.queueStep.token_guard).1
  · rw [marksEq]
    exact middleInvariant.queued_vertices_unmarked vertex oldMembership

private theorem componentDomainExact
    {certificate : Certificate} {before after : ReservationState}
    (step : ForwardStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    ComponentDomainExact after := by
  have middleInvariant := step.prepared.schedulerInvariant invariant
  have activeLookup := step.active_component_lookup invariant
  have activeBound :
      step.queueStep.outputToken <
        step.prepared.coreMarked.components.size :=
    (Array.getElem?_eq_some_iff.mp activeLookup).1
  have activeInSigma :
      step.queueStep.outputToken ∈ step.prepared.after.stack.sigma :=
    (middleInvariant.component_domain_exact
      step.queueStep.outputToken).mp
        ⟨step.queueStep.component, by
          change step.prepared.after.core.components[
              step.queueStep.outputToken]? = _
          exact activeLookup⟩
  intro token
  have afterCoreEq : after.core = step.coreAfter :=
    congrArg (fun state : ReservationState => state.core) step.output_eq
  have afterStackEq : after.stack = step.stackAfter :=
    congrArg (fun state : ReservationState => state.stack) step.output_eq
  rw [afterCoreEq, step.queueStep.after_eq,
    afterStackEq, step.prependStep.after_eq]
  change
    (∃ component,
      (step.prepared.coreMarked.components.setIfInBounds
        step.queueStep.outputToken
        (some {
          tree := .par step.queueStep.leftFocus
            step.queueStep.rightFocus step.queueStep.component.tree
          frontier := step.queueStep.context ++
            [step.consumer.conclusion] }))[token]? =
        some (some component)) ↔
      token ∈ step.prepared.after.stack.sigma
  by_cases same : token = step.queueStep.outputToken
  · subst token
    constructor
    · intro _
      exact activeInSigma
    · intro _
      refine ⟨{
        tree := .par step.queueStep.leftFocus
          step.queueStep.rightFocus step.queueStep.component.tree
        frontier := step.queueStep.context ++
          [step.consumer.conclusion] }, ?_⟩
      simp [activeBound]
  · have oldDomain := middleInvariant.component_domain_exact token
    change
      (∃ component,
        step.prepared.coreMarked.components[token]? =
          some (some component)) ↔
        token ∈ step.prepared.after.stack.sigma at oldDomain
    rw [Array.getElem?_setIfInBounds_ne (Ne.symm same)]
    exact oldDomain

private theorem mate_boundary_middle
    {certificate : Certificate} {before after : ReservationState}
    (step : ForwardStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    sigmaBoundary? step.prepared.after.stack.sigma step.mateRawAge =
      some step.prepared.stackResult.rawAge := by
  have middleInvariant := step.prepared.schedulerInvariant invariant
  rcases SequentialStackState.popReadyMark?_exact
      step.prepared.stack_eq with
    ⟨_, sigmaTopEquation, _, _, _, stackSigmaEq, _, _, _⟩
  have middleSigmaTop :
      step.prepared.after.stack.sigma.getLast? =
        some step.prepared.stackResult.rawAge := by
    change step.prepared.stackResult.after.sigma.getLast? = _
    rw [stackSigmaEq]
    exact sigmaTopEquation
  have stackMateMarked :
      step.prepared.after.stack.marks[step.consumer.mate]? =
        some (some step.mateRawAge) := by
    rw [← middleInvariant.realizesSigma.marks_eq]
    exact step.mate_marked
  have mateAgeBound :
      step.mateRawAge < step.prepared.after.stack.nextAge :=
    middleInvariant.stack_wellShaped.assigned_age_bound
      step.consumer.mate step.mateRawAge stackMateMarked
  exact middleInvariant.stack_wellShaped.sigma_partition
    |>.sigmaBoundary?_eq_top_of_le middleSigmaTop
      step.not_older mateAgeBound

private theorem readyBucketFrontierExact
    {certificate : Certificate} {before after : ReservationState}
    (step : ForwardStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    ReadyBucketFrontierExact after := by
  have middleInvariant := step.prepared.schedulerInvariant invariant
  rcases SequentialStackState.popReadyMark?_exact
      step.prepared.stack_eq with
    ⟨_, sigmaTopEquation, _, _, _, stackSigmaEq,
      preparedReadyEq, _, _⟩
  have middleSigmaTop :
      step.prepared.after.stack.sigma.getLast? =
        some step.queueStep.outputToken := by
    change step.prepared.stackResult.after.sigma.getLast? = _
    rw [stackSigmaEq]
    simpa [step.output_token_eq_active] using sigmaTopEquation
  rcases List.getLast?_eq_some_iff.mp middleSigmaTop with
    ⟨sigmaPrefix, sigmaDecomposition⟩
  change step.prepared.stackResult.after.sigma =
    sigmaPrefix ++ [step.queueStep.outputToken] at sigmaDecomposition
  have prefixLengths :
      step.prependStep.readyPrefix.length = sigmaPrefix.length := by
    have aligned := middleInvariant.stack_wellShaped.ready_aligned
    change step.prepared.stackResult.after.ready.length =
      step.prepared.stackResult.after.sigma.length at aligned
    rw [step.prependStep.ready_eq, sigmaDecomposition] at aligned
    simp at aligned
    omega
  have topSigmaLookup :
      step.prepared.after.stack.sigma[
          step.prependStep.readyPrefix.length]? =
        some step.queueStep.outputToken := by
    change step.prepared.stackResult.after.sigma[
        step.prependStep.readyPrefix.length]? = _
    rw [sigmaDecomposition, prefixLengths]
    simp
  have topReadyLookup :
      step.prepared.after.stack.ready[
          step.prependStep.readyPrefix.length]? =
        some step.prependStep.activeReady := by
    change step.prepared.stackResult.after.ready[
        step.prependStep.readyPrefix.length]? = _
    rw [step.prependStep.ready_eq]
    simp
  rcases middleInvariant.ready_bucket_frontier_exact
      topSigmaLookup topReadyLookup with
    ⟨topComponent, topComponentLookup, topExact⟩
  change step.prepared.coreMarked.components[
      step.queueStep.outputToken]? = some (some topComponent) at topComponentLookup
  change (∀ vertex,
      vertex ∈ step.prependStep.activeReady ↔
        vertex ∈ topComponent.frontier ∧
          step.prepared.coreMarked.marks[vertex]? = some none) at topExact
  have topComponentEq : topComponent = step.queueStep.component := by
    have activeLookup := step.active_component_lookup invariant
    change step.prepared.after.core.components[
        step.queueStep.outputToken]? =
      some (some step.queueStep.component) at activeLookup
    exact Option.some.inj
      (Option.some.inj (topComponentLookup.symm.trans activeLookup))
  subst topComponent
  have activeBound :
      step.queueStep.outputToken <
        step.prepared.coreMarked.components.size :=
    (Array.getElem?_eq_some_iff.mp
      (step.active_component_lookup invariant)).1
  have tokenGuards :=
    UnificationState.forwardToken?_success step.queueStep.token_guard
  have context_of_frontier_unmarked :
      ∀ {vertex},
        vertex ∈ step.queueStep.component.frontier →
        step.prepared.coreMarked.marks[vertex]? = some none →
        vertex ∈ step.queueStep.context := by
    intro vertex frontier unmarked
    have vertexNeLeft : vertex ≠ step.consumer.storedLeft := by
      intro same
      subst vertex
      unfold UnificationState.tokenAt? at tokenGuards
      rw [unmarked] at tokenGuards
      simp at tokenGuards
    have vertexNeRight : vertex ≠ step.consumer.storedRight := by
      intro same
      subst vertex
      unfold UnificationState.tokenAt? at tokenGuards
      rw [unmarked] at tokenGuards
      simp at tokenGuards
    have inAfterLeft :=
      Certificate.FirstOccurrencePick.mem_remaining_of_ne
        step.queueStep.left_pick vertexNeLeft frontier
    exact Certificate.FirstOccurrencePick.mem_remaining_of_ne
      step.queueStep.right_pick vertexNeRight inAfterLeft
  have frontier_of_context :
      ∀ {vertex}, vertex ∈ step.queueStep.context →
        vertex ∈ step.queueStep.component.frontier := by
    intro vertex contextMembership
    have inAfterLeft : vertex ∈ step.queueStep.afterLeft :=
      (CutFreeDerivation.pick?_perm
        step.queueStep.right_pick.positional).mem_iff.mpr (by
          simp [contextMembership])
    exact
      (CutFreeDerivation.pick?_perm
        step.queueStep.left_pick.positional).mem_iff.mpr (by
          simp [inAfterLeft])
  have afterCoreEq : after.core = step.coreAfter :=
    congrArg (fun state : ReservationState => state.core) step.output_eq
  have afterStackEq : after.stack = step.stackAfter :=
    congrArg (fun state : ReservationState => state.stack) step.output_eq
  have afterMarks : after.core.marks =
      step.prepared.coreMarked.marks := by
    rw [afterCoreEq, step.queueStep.after_eq]
  have coreComponentsEq :
      after.core.components =
        step.prepared.coreMarked.components.setIfInBounds
          step.queueStep.outputToken
          (some {
            tree := .par step.queueStep.leftFocus
              step.queueStep.rightFocus step.queueStep.component.tree
            frontier := step.queueStep.context ++
              [step.consumer.conclusion] }) := by
    exact (congrArg (fun core : UnificationState => core.components)
      afterCoreEq).trans
      (congrArg (fun core : UnificationState => core.components)
        step.queueStep.after_eq)
  unfold ReadyBucketFrontierExact
  intro position boundary bucket sigmaLookup readyLookup
  rw [afterStackEq, step.prependStep.after_eq] at sigmaLookup readyLookup
  change step.prepared.after.stack.sigma[position]? =
    some boundary at sigmaLookup
  change
    (step.prependStep.readyPrefix ++
      [step.consumer.conclusion ::
        step.prependStep.activeReady])[position]? =
      some bucket at readyLookup
  have positionBound :
      position <
        (step.prependStep.readyPrefix ++
          [step.consumer.conclusion ::
            step.prependStep.activeReady]).length :=
    (List.getElem?_eq_some_iff.mp readyLookup).1
  by_cases inPrefix : position < step.prependStep.readyPrefix.length
  · have oldReadyLookup :
        step.prepared.after.stack.ready[position]? = some bucket := by
      change step.prepared.stackResult.after.ready[position]? = some bucket
      rw [step.prependStep.ready_eq,
        List.getElem?_append_left inPrefix]
      rw [List.getElem?_append_left inPrefix] at readyLookup
      exact readyLookup
    rcases middleInvariant.ready_bucket_frontier_exact
        sigmaLookup oldReadyLookup with
      ⟨component, componentLookup, exactMembership⟩
    change step.prepared.coreMarked.components[boundary]? =
      some (some component) at componentLookup
    change (∀ vertex,
      vertex ∈ bucket ↔
        vertex ∈ component.frontier ∧
          step.prepared.coreMarked.marks[vertex]? = some none) at exactMembership
    have boundaryInPrefix : boundary ∈ sigmaPrefix := by
      have sigmaPrefixLookup : sigmaPrefix[position]? = some boundary := by
        have lookup := sigmaLookup
        change step.prepared.stackResult.after.sigma[position]? =
          some boundary at lookup
        rw [sigmaDecomposition,
          List.getElem?_append_left (by simpa [prefixLengths] using inPrefix)]
          at lookup
        exact lookup
      exact List.mem_of_getElem? sigmaPrefixLookup
    have increasing :
        (sigmaPrefix ++ [step.queueStep.outputToken]).Pairwise
          (· < ·) := by
      have oldIncreasing :=
        middleInvariant.stack_wellShaped.sigma_partition.strictIncreasing
      change step.prepared.stackResult.after.sigma.Pairwise
        (· < ·) at oldIncreasing
      rw [sigmaDecomposition] at oldIncreasing
      exact oldIncreasing
    have boundaryLtActive : boundary < step.queueStep.outputToken :=
      (List.pairwise_append.mp increasing).2.2
        boundary boundaryInPrefix step.queueStep.outputToken (by simp)
    have boundaryNeActive :
        step.queueStep.outputToken ≠ boundary :=
      Nat.ne_of_gt boundaryLtActive
    refine ⟨component, ?_, ?_⟩
    · rw [coreComponentsEq]
      simpa [Array.getElem?_setIfInBounds, boundaryNeActive] using
        componentLookup
    · intro vertex
      rw [afterMarks]
      exact exactMembership vertex
  · have positionTop :
        position = step.prependStep.readyPrefix.length := by
      simp at positionBound
      omega
    subst position
    have boundaryEq : boundary = step.queueStep.outputToken := by
      rw [topSigmaLookup] at sigmaLookup
      exact Option.some.inj sigmaLookup.symm
    have bucketEq :
        bucket = step.consumer.conclusion ::
          step.prependStep.activeReady := by
      simp at readyLookup
      exact readyLookup.symm
    subst boundary
    subst bucket
    refine ⟨{
      tree := .par step.queueStep.leftFocus
        step.queueStep.rightFocus step.queueStep.component.tree
      frontier := step.queueStep.context ++
        [step.consumer.conclusion] }, ?_, ?_⟩
    · rw [coreComponentsEq]
      simp [activeBound]
    · intro vertex
      rw [afterMarks]
      constructor
      · intro bucketMembership
        simp only [List.mem_cons] at bucketMembership
        rcases bucketMembership with rfl | oldReady
        · exact ⟨by simp, tokenGuards.1⟩
        · have oldFacts := (topExact vertex).mp oldReady
          exact ⟨by
            simp [context_of_frontier_unmarked oldFacts.1 oldFacts.2],
            oldFacts.2⟩
      · rintro ⟨newFrontier, unmarked⟩
        rw [List.mem_append] at newFrontier
        rcases newFrontier with contextMembership | conclusionMembership
        · simp only [List.mem_cons]
          exact Or.inr ((topExact vertex).mpr
            ⟨frontier_of_context contextMembership, unmarked⟩)
        · have same : vertex = step.consumer.conclusion := by
            simpa using conclusionMembership
          simp [same]

private theorem waitingSpanExact
    {certificate : Certificate} {before after : ReservationState}
    (step : ForwardStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    WaitingSpanExact certificate after := by
  have middleInvariant := step.prepared.schedulerInvariant invariant
  have marksEq : after.core.marks =
      step.prepared.after.core.marks := by
    have afterCoreEq : after.core = step.coreAfter :=
      congrArg (fun state : ReservationState => state.core) step.output_eq
    rw [afterCoreEq, step.queueStep.after_eq]
    rfl
  have sigmaEq : after.stack.sigma =
      step.prepared.after.stack.sigma := by
    have afterStackEq : after.stack = step.stackAfter :=
      congrArg (fun state : ReservationState => state.stack) step.output_eq
    rw [afterStackEq, step.prependStep.after_eq]
    rfl
  have waitingEq : after.stack.waiting =
      step.prepared.after.stack.waiting := by
    have afterStackEq : after.stack = step.stackAfter :=
      congrArg (fun state : ReservationState => state.stack) step.output_eq
    rw [afterStackEq, step.prependStep.after_eq]
    rfl
  intro boundary payload conclusion waitingLookup conclusionMembership
  rw [waitingEq] at waitingLookup
  rcases middleInvariant.waiting_span_exact
      waitingLookup conclusionMembership with
    ⟨linkIndex, left, right, olderPremise, youngerPremise,
      olderAge, youngerAge, youngerBoundary, linkLookup,
      sourceLookup, conclusionUnmarked, orientation,
      olderMarked, youngerMarked, olderBoundary,
      youngerBoundaryLookup, boundaryOrder⟩
  refine ⟨linkIndex, left, right, olderPremise, youngerPremise,
    olderAge, youngerAge, youngerBoundary, linkLookup,
    sourceLookup, ?_, orientation, ?_, ?_, ?_, ?_, boundaryOrder⟩
  · rw [marksEq]
    exact conclusionUnmarked
  · rw [marksEq]
    exact olderMarked
  · rw [marksEq]
    exact youngerMarked
  · rw [sigmaEq]
    exact olderBoundary
  · rw [sigmaEq]
    exact youngerBoundaryLookup

private theorem produced_after_cases
    {certificate : Certificate} {before after : ReservationState}
    (step : ForwardStep certificate before after)
    (invariant : SchedulerInvariant certificate before)
    {vertex : Vertex}
    (produced : Produced after vertex) :
    vertex = step.consumer.conclusion ∨
      Produced step.prepared.after vertex := by
  have afterCoreEq : after.core = step.coreAfter :=
    congrArg (fun state : ReservationState => state.core) step.output_eq
  have marksEq : after.core.marks =
      step.prepared.coreMarked.marks := by
    rw [afterCoreEq, step.queueStep.after_eq]
  have componentsEq :
      after.core.components =
        step.prepared.coreMarked.components.setIfInBounds
          step.queueStep.outputToken
          (some {
            tree := .par step.queueStep.leftFocus
              step.queueStep.rightFocus step.queueStep.component.tree
            frontier := step.queueStep.context ++
              [step.consumer.conclusion] }) := by
    exact (congrArg (fun core : UnificationState => core.components)
      afterCoreEq).trans
        (congrArg (fun core : UnificationState => core.components)
          step.queueStep.after_eq)
  rcases produced with ⟨rawAge, marked⟩ | frontierMembership
  · apply Or.inr
    apply Or.inl
    refine ⟨rawAge, ?_⟩
    rw [marksEq] at marked
    exact marked
  · unfold UnificationState.liveFrontierVertices at frontierMembership
    rcases List.mem_flatMap.mp frontierMembership with
      ⟨cell, cellMembership, vertexFrontier⟩
    cases cell with
    | none => simp at vertexFrontier
    | some component =>
        simp only [Option.map_some, Option.getD_some] at vertexFrontier
        rcases List.mem_iff_getElem.mp cellMembership with
          ⟨index, indexBound, indexEquation⟩
        have afterLookup :
            after.core.components[index]? = some (some component) := by
          rw [← Array.getElem?_toList]
          rw [List.getElem?_eq_getElem indexBound, indexEquation]
        by_cases active : index = step.queueStep.outputToken
        · subst index
          have activeBound :
              step.queueStep.outputToken <
                step.prepared.coreMarked.components.size :=
            (Array.getElem?_eq_some_iff.mp
              (step.active_component_lookup invariant)).1
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
            · have rawLookup := step.active_component_lookup invariant
              change step.prepared.after.core.components[
                  step.queueStep.outputToken]? =
                some (some step.queueStep.component) at rawLookup
              exact List.mem_of_getElem? (by simpa using rawLookup)
            · have inAfterLeft :
                  vertex ∈ step.queueStep.afterLeft :=
                (CutFreeDerivation.pick?_perm
                  step.queueStep.right_pick.positional).mem_iff.mpr (by
                    simp [contextMembership])
              exact
                (CutFreeDerivation.pick?_perm
                  step.queueStep.left_pick.positional).mem_iff.mpr (by
                    simp [inAfterLeft])
          · left
            simpa using conclusionMembership
        · apply Or.inr
          apply Or.inr
          unfold UnificationState.liveFrontierVertices
          apply List.mem_flatMap.mpr
          refine ⟨some component, ?_, ?_⟩
          · have oldLookup :
                step.prepared.coreMarked.components[index]? =
                  some (some component) := by
              rw [componentsEq] at afterLookup
              simpa [Array.getElem?_setIfInBounds, Ne.symm active] using
                afterLookup
            exact List.mem_of_getElem? (by
              have lookup := oldLookup
              change step.prepared.after.core.components[index]? =
                some (some component) at lookup
              simpa using lookup)
          · simpa using vertexFrontier

private theorem submittedPremisesMarkedAfter
    {certificate : Certificate} {before after : ReservationState}
    (step : ForwardStep certificate before after) :
    (∃ leftAge,
      after.core.marks[step.consumer.storedLeft]? =
        some (some leftAge)) ∧
      ∃ rightAge,
        after.core.marks[step.consumer.storedRight]? =
          some (some rightAge) := by
  have afterCoreEq : after.core = step.coreAfter :=
    congrArg (fun state : ReservationState => state.core) step.output_eq
  have marksEq : after.core.marks =
      step.prepared.coreMarked.marks := by
    rw [afterCoreEq, step.queueStep.after_eq]
  have selectedMarked :
      step.prepared.coreMarked.marks[
          step.prepared.stackResult.vertex]? =
        some (some step.prepared.stackResult.rawAge) :=
    (UnificationState.markReadyRaw?_exact
      step.prepared.core_mark_eq).2.2.2.2.2.2
  rcases step.premise_orientation with
    ⟨mateEq, selectedEq⟩ | ⟨mateEq, selectedEq⟩
  · constructor
    · exact ⟨step.mateRawAge, by
        rw [marksEq, ← mateEq]
        exact step.mate_marked⟩
    · exact ⟨step.prepared.stackResult.rawAge, by
        rw [marksEq, ← selectedEq]
        exact selectedMarked⟩
  · constructor
    · exact ⟨step.prepared.stackResult.rawAge, by
        rw [marksEq, ← selectedEq]
        exact selectedMarked⟩
    · exact ⟨step.mateRawAge, by
        rw [marksEq, ← mateEq]
        exact step.mate_marked⟩

private theorem producedPremisesMarked
    {certificate : Certificate} {before after : ReservationState}
    (step : ForwardStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    ProducedPremisesMarked certificate after := by
  have middleInvariant := step.prepared.schedulerInvariant invariant
  have afterCoreEq : after.core = step.coreAfter :=
    congrArg (fun state : ReservationState => state.core) step.output_eq
  have marksEq : after.core.marks =
      step.prepared.after.core.marks := by
    rw [afterCoreEq, step.queueStep.after_eq]
    rfl
  intro link linkMembership
  cases link with
  | «axiom» left right => trivial
  | tensor left right conclusion
  | «par» left right conclusion =>
      intro producedAfter
      rcases step.produced_after_cases invariant producedAfter with
        conclusionEq | producedMiddle
      · subst conclusion
        have currentMembership :
            (.par step.consumer.storedLeft step.consumer.storedRight
              step.consumer.conclusion : Link) ∈ certificate.links :=
          List.mem_of_getElem? step.submitted_par
        have producerEq :=
          UnificationState.StructurallyWellFormed.producerLink_unique
            invariant.structural
            (conclusion := step.consumer.conclusion)
            linkMembership (by simp [Link.produces])
            currentMembership (by simp [Link.produces])
        cases producerEq <;>
          exact step.submittedPremisesMarkedAfter
      · rcases middleInvariant.produced_premises_marked
            linkMembership producedMiddle with
          ⟨⟨leftAge, leftMarked⟩, rightAge, rightMarked⟩
        refine ⟨⟨leftAge, ?_⟩, rightAge, ?_⟩
        · rw [marksEq]
          exact leftMarked
        · rw [marksEq]
          exact rightMarked

private theorem conclusion_mem_ready_after
    {certificate : Certificate} {before after : ReservationState}
    (step : ForwardStep certificate before after) :
    step.consumer.conclusion ∈ after.stack.ready.flatten := by
  have afterStackEq : after.stack = step.stackAfter :=
    congrArg (fun state : ReservationState => state.stack) step.output_eq
  rw [afterStackEq, step.prependStep.after_eq]
  apply List.mem_flatten.mpr
  exact ⟨step.consumer.conclusion :: step.prependStep.activeReady,
    by simp, by simp⟩

private theorem pendingPremisesCoveredExceptReady
    {certificate : Certificate} {before after : ReservationState}
    (step : ForwardStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    PendingPremisesCoveredExceptReady certificate after := by
  have middleInvariant := step.prepared.schedulerInvariant invariant
  have afterCoreEq : after.core = step.coreAfter :=
    congrArg (fun state : ReservationState => state.core) step.output_eq
  have afterStackEq : after.stack = step.stackAfter :=
    congrArg (fun state : ReservationState => state.stack) step.output_eq
  have marksEq : after.core.marks =
      step.prepared.coreMarked.marks := by
    rw [afterCoreEq, step.queueStep.after_eq]
  have parentsEq : after.core.parents =
      step.prepared.coreMarked.parents := by
    rw [afterCoreEq, step.queueStep.after_eq]
  have componentsEq :
      after.core.components =
        step.prepared.coreMarked.components.setIfInBounds
          step.queueStep.outputToken
          (some {
            tree := .par step.queueStep.leftFocus
              step.queueStep.rightFocus step.queueStep.component.tree
            frontier := step.queueStep.context ++
              [step.consumer.conclusion] }) := by
    exact (congrArg (fun core : UnificationState => core.components)
      afterCoreEq).trans
        (congrArg (fun core : UnificationState => core.components)
          step.queueStep.after_eq)
  have representativeEq : ∀ token,
      after.core.representative token =
        step.prepared.coreMarked.representative token := by
    intro token
    unfold UnificationState.representative
    rw [parentsEq]
  have activeLookup := step.active_component_lookup invariant
  have activeBound :
      step.queueStep.outputToken <
        step.prepared.coreMarked.components.size :=
    (Array.getElem?_eq_some_iff.mp activeLookup).1
  have oldReady_subset_after :
      ∀ {vertex},
        vertex ∈ step.prepared.after.stack.ready.flatten →
          vertex ∈ after.stack.ready.flatten := by
    intro vertex membership
    change vertex ∈
      step.prepared.stackResult.after.ready.flatten at membership
    rw [step.prependStep.ready_eq] at membership
    rw [afterStackEq, step.prependStep.after_eq]
    simp only [List.flatten_append, List.flatten_cons, List.flatten_nil,
      List.append_nil, List.mem_append, List.mem_cons] at membership ⊢
    rcases membership with inPrefix | inActive
    · exact Or.inl inPrefix
    · exact Or.inr (Or.inr inActive)
  intro link linkMembership
  cases link with
  | «axiom» left right => trivial
  | tensor left right conclusion
  | «par» left right conclusion =>
      intro conclusionUnmarked conclusionNotReady premise token
        premiseMembership tokenAt
      have conclusionNeNew :
          conclusion ≠ step.consumer.conclusion := by
        intro same
        subst conclusion
        exact conclusionNotReady step.conclusion_mem_ready_after
      have middleConclusionUnmarked :
          step.prepared.after.core.marks[conclusion]? = some none := by
        change step.prepared.coreMarked.marks[conclusion]? = some none
        rw [← marksEq]
        exact conclusionUnmarked
      have middleConclusionNotReady :
          conclusion ∉ step.prepared.after.stack.ready.flatten := by
        intro membership
        exact conclusionNotReady (oldReady_subset_after membership)
      have middleTokenAt :
          step.prepared.after.core.tokenAt? premise = some token := by
        change step.prepared.coreMarked.tokenAt? premise = some token
        unfold UnificationState.tokenAt? at tokenAt ⊢
        rw [marksEq] at tokenAt
        simpa [representativeEq] using tokenAt
      rcases middleInvariant.pending_premises_covered_except_ready
          linkMembership middleConclusionUnmarked middleConclusionNotReady
          premiseMembership middleTokenAt with
        ⟨component, componentLookup, premiseFrontier⟩
      change step.prepared.coreMarked.componentAt? token =
        some component at componentLookup
      have premiseNeLeft : premise ≠ step.consumer.storedLeft := by
        intro same
        subst premise
        have sameLink :=
          UnificationState.StructurallyWellFormed.parentLink_unique
            invariant.structural
            (premise := step.consumer.storedLeft)
            (first := .par step.consumer.storedLeft
              step.consumer.storedRight step.consumer.conclusion)
            (List.mem_of_getElem? step.submitted_par)
            (by simp [Link.premises]) linkMembership
            (by simpa [Link.premises] using premiseMembership)
        have impossible : False := by
          cases sameLink <;> exact conclusionNeNew rfl
        exact impossible.elim
      have premiseNeRight : premise ≠ step.consumer.storedRight := by
        intro same
        subst premise
        have sameLink :=
          UnificationState.StructurallyWellFormed.parentLink_unique
            invariant.structural
            (premise := step.consumer.storedRight)
            (first := .par step.consumer.storedLeft
              step.consumer.storedRight step.consumer.conclusion)
            (List.mem_of_getElem? step.submitted_par)
            (by simp [Link.premises]) linkMembership
            (by simpa [Link.premises] using premiseMembership)
        have impossible : False := by
          cases sameLink <;> exact conclusionNeNew rfl
        exact impossible.elim
      by_cases activeRepresentative :
          step.prepared.coreMarked.representative token =
            step.queueStep.outputToken
      · have rawLookup :=
          UnificationState.componentAt?_some_raw componentLookup
        rw [activeRepresentative] at rawLookup
        have componentEq : component = step.queueStep.component :=
          Option.some.inj
            (Option.some.inj (rawLookup.symm.trans activeLookup))
        subst component
        have inAfterLeft :=
          Certificate.FirstOccurrencePick.mem_remaining_of_ne
            step.queueStep.left_pick premiseNeLeft premiseFrontier
        have inContext :=
          Certificate.FirstOccurrencePick.mem_remaining_of_ne
            step.queueStep.right_pick premiseNeRight inAfterLeft
        refine ⟨{
          tree := .par step.queueStep.leftFocus
            step.queueStep.rightFocus step.queueStep.component.tree
          frontier := step.queueStep.context ++
            [step.consumer.conclusion] }, ?_, by simp [inContext]⟩
        unfold UnificationState.componentAt?
        rw [representativeEq, activeRepresentative, componentsEq]
        simp [activeBound]
      · refine ⟨component, ?_, premiseFrontier⟩
        unfold UnificationState.componentAt? at componentLookup ⊢
        rw [representativeEq, componentsEq]
        simpa [Array.getElem?_setIfInBounds,
          Ne.symm activeRepresentative] using componentLookup

/-- The occurrence-exact component forest already supplies the global live
frontier duplicate-freedom required by the scheduler invariant. -/
private theorem liveFrontiersNodup
    {certificate : Certificate} {before after : ReservationState}
    (step : ForwardStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    LiveFrontiersNodup after := by
  unfold LiveFrontiersNodup
  simpa [UnificationState.liveFrontierVertices] using
    (step.componentForestProvenance invariant).liveFrontiers_nodup

private theorem foldl_add_weight_eq
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

private theorem map_sum_set_add_one
    {alpha : Type} {values : List alpha} {index : Nat}
    {oldValue newValue : alpha} (weight : alpha → Nat)
    (lookup : values[index]? = some oldValue)
    (weight_eq : weight newValue = weight oldValue + 1) :
    ((values.set index newValue).map weight).sum =
      (values.map weight).sum + 1 := by
  induction values generalizing index with
  | nil => simp at lookup
  | cons head tail induction =>
      cases index with
      | zero =>
          have head_eq : head = oldValue := by simpa using lookup
          subst head
          simp only [List.set, List.map_cons, List.sum_cons]
          omega
      | succ prior =>
          simp only [List.getElem?_cons_succ] at lookup
          simp only [List.set, List.map_cons, List.sum_cons]
          rw [induction lookup]
          omega

/-- A successful forward par construction adds exactly one connective to the
active component and increments the production counter exactly once. -/
private theorem firedCounterExact
    {certificate : Certificate} {before after : ReservationState}
    (step : ForwardStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    FiredCounterExact after := by
  let weight : Option UnificationComponent → Nat := fun cell =>
    (cell.map UnificationComponent.connectiveCount).getD 0
  let nextComponent : UnificationComponent := {
    tree := .par step.queueStep.leftFocus step.queueStep.rightFocus
      step.queueStep.component.tree
    frontier := step.queueStep.context ++ [step.consumer.conclusion] }
  have middleInvariant := step.prepared.schedulerInvariant invariant
  have activeLookup := step.active_component_lookup invariant
  have activeListLookup :
      step.prepared.coreMarked.components.toList[
          step.queueStep.outputToken]? =
        some (some step.queueStep.component) := by
    simpa using activeLookup
  have weightIncrease :
      weight (some nextComponent) =
        weight (some step.queueStep.component) + 1 := by
    simp [weight, nextComponent, UnificationComponent.connectiveCount,
      CutFreeDerivation.connectiveCount]
  have sumIncrease :=
    map_sum_set_add_one weight activeListLookup weightIncrease
  have totalIncrease :
      (step.prepared.coreMarked.components.toList.set
          step.queueStep.outputToken (some nextComponent)).foldl
          (fun total cell => total + weight cell) 0 =
        step.prepared.coreMarked.components.toList.foldl
            (fun total cell => total + weight cell) 0 + 1 := by
    rw [foldl_add_weight_eq, foldl_add_weight_eq]
    simpa using sumIncrease
  have middleCounter := middleInvariant.fired_counter_exact
  unfold FiredCounterExact UnificationState.liveConnectiveCount at middleCounter
  have afterCoreEq : after.core = step.coreAfter :=
    congrArg (fun state : ReservationState => state.core) step.output_eq
  unfold FiredCounterExact
  rw [afterCoreEq, step.queueStep.after_eq]
  unfold UnificationState.liveConnectiveCount
  rw [Array.toList_setIfInBounds]
  change
    step.prepared.coreMarked.firedConnectives + 1 =
      (step.prepared.coreMarked.components.toList.set
        step.queueStep.outputToken (some nextComponent)).foldl
          (fun total cell => total + weight cell) 0
  rw [totalIncrease]
  exact congrArg (fun count => count + 1) middleCounter

/-- A successful local Figure-7 `forward` step preserves every field of the
current occurrence-exact, state-only scheduler invariant.  This theorem is a
preservation result only; it does not assert applicability or progress. -/
theorem schedulerInvariant
    {certificate : Certificate} {before after : ReservationState}
    (step : ForwardStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    SchedulerInvariant certificate after := by
  exact {
    toReservationInvariant := step.reservationInvariant
    structural := invariant.structural
    component_domain_exact := step.componentDomainExact invariant
    component_forest_provenance :=
      step.componentForestProvenance invariant
    live_frontiers_nodup := step.liveFrontiersNodup invariant
    ready_bucket_frontier_exact :=
      step.readyBucketFrontierExact invariant
    queued_vertices_nodup := step.queuedVerticesNodup invariant
    queued_vertices_unmarked := step.queuedVerticesUnmarked invariant
    produced_premises_marked := step.producedPremisesMarked invariant
    waiting_span_exact := step.waitingSpanExact invariant
    pending_premises_covered_except_ready :=
      step.pendingPremisesCoveredExceptReady invariant
    fired_counter_exact := step.firedCounterExact invariant }

end ForwardStep

/-- Executable `forward?` success preserves the complete current scheduler
invariant.  Dispatcher totality and progress remain separate obligations. -/
theorem forward?_schedulerInvariant
    {certificate : Certificate} {before after : ReservationState}
    (invariant : SchedulerInvariant certificate before)
    (equation :
      forward? certificate before invariant.toReservationInvariant =
        some after) :
    SchedulerInvariant certificate after := by
  rcases (forward?_some_iff invariant.toReservationInvariant).mp equation with
    ⟨step⟩
  exact step.schedulerInvariant invariant

/-- A direct `ForwardRule` witness is executable in a state satisfying the
complete scheduler invariant.  The invariant supplies both structural
validity and the separately proved ready-list freshness condition.  This is
rule-witness completeness, not an applicability or progress theorem. -/
theorem forward?_complete_of_schedulerInvariant
    {certificate : Certificate} {before after : ReservationState}
    (invariant : SchedulerInvariant certificate before)
    (rule : ForwardRule certificate before after) :
    forward? certificate before invariant.toReservationInvariant =
      some after :=
  forward?_complete_of_structural invariant.structural
    invariant.toReservationInvariant
    (ProofNetIR.SequentialFigure7.SchedulerInvariant.forwardExecutableReadyNodup
      invariant) rule

/-- Exact executable/direct correspondence for `forward` in a state carrying
the complete scheduler invariant.  No branch existence or dispatcher
totality is asserted. -/
theorem forward?_some_iff_rule_of_schedulerInvariant
    {certificate : Certificate} {before after : ReservationState}
    (invariant : SchedulerInvariant certificate before) :
    forward? certificate before invariant.toReservationInvariant =
        some after ↔
      ForwardRule certificate before after :=
  forward?_some_iff_rule_of_structural invariant.structural
    invariant.toReservationInvariant
    (ProofNetIR.SequentialFigure7.SchedulerInvariant.forwardExecutableReadyNodup
      invariant)

namespace WaitStep

private theorem conclusion_not_produced_before
    {certificate : Certificate} {before after : ReservationState}
    (step : WaitStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    ¬ Produced before step.consumer.conclusion := by
  intro produced
  have linkMembership :
      (.par step.consumer.storedLeft step.consumer.storedRight
        step.consumer.conclusion : Link) ∈ certificate.links :=
    List.mem_of_getElem? step.submitted_par
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
          step.consumer.premise_eq
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
          step.consumer.premise_eq
      have rightUnmarked :
          before.core.marks[step.consumer.storedRight]? = some none :=
        (congrArg (fun vertex => before.core.marks[vertex]?)
          selectedEq).symm.trans selectedUnmarked
      rw [rightUnmarked] at rightMarked
      simp at rightMarked

private theorem conclusion_unmarked_before
    {certificate : Certificate} {before after : ReservationState}
    (step : WaitStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    before.core.marks[step.consumer.conclusion]? = some none := by
  have parWellFormed : certificate.LinkWellFormed
      (.par step.consumer.storedLeft step.consumer.storedRight
        step.consumer.conclusion) := by
    simpa [step.par_eq, SequentialConnectiveKind.asLink] using
      step.consumer.wellFormed
  have conclusionBound := parWellFormed.2.2.2.2.2.1
  have coreMarksSize :
      before.core.marks.size = certificate.formulas.size := by
    rw [invariant.realizesSigma.marks_eq]
    exact invariant.stack_wellShaped.marks_size
  have coreConclusionBound :
      step.consumer.conclusion < before.core.marks.size := by
    simpa [coreMarksSize] using conclusionBound
  cases conclusionLookup :
      before.core.marks[step.consumer.conclusion]? with
  | none =>
      rw [Array.getElem?_eq_getElem coreConclusionBound] at conclusionLookup
      simp at conclusionLookup
  | some mark =>
      cases mark with
      | none => rfl
      | some conclusionAge =>
          exact (step.conclusion_not_produced_before invariant
            (Or.inl ⟨conclusionAge, conclusionLookup⟩)).elim

private theorem conclusion_not_mem_waiting_before
    {certificate : Certificate} {before after : ReservationState}
    (step : WaitStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    step.consumer.conclusion ∉ before.stack.waitingVertices := by
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
          (.par oldLeft oldRight step.consumer.conclusion : Link) ∈
            certificate.links :=
        List.mem_of_getElem? oldLinkLookup
      have currentLinkMembership :
          (.par step.consumer.storedLeft step.consumer.storedRight
            step.consumer.conclusion : Link) ∈ certificate.links :=
        List.mem_of_getElem? step.submitted_par
      have linkEq := invariant.structural.par_producer_unique
        oldLinkMembership currentLinkMembership
      injection linkEq with leftEq rightEq
      subst oldLeft
      subst oldRight
      rcases UnificationState.markReadyRaw?_exact
          step.prepared.core_mark_eq with
        ⟨selectedUnmarked, _, _, _, _, _, _⟩
      cases sideEquation : step.consumer.side with
      | storedLeft =>
          have selectedEq : step.prepared.stackResult.vertex =
              step.consumer.storedLeft := by
            simpa [TensorPremiseSide.premise, sideEquation] using
              step.consumer.premise_eq
          have selectedMarked :
              before.core.marks[step.prepared.stackResult.vertex]? =
                some (some olderAge) ∨
              before.core.marks[step.prepared.stackResult.vertex]? =
                some (some youngerAge) := by
            rcases oldOrientation with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact Or.inl (by simpa [selectedEq] using olderMarked)
            · exact Or.inr (by simpa [selectedEq] using youngerMarked)
          rcases selectedMarked with marked | marked <;>
            rw [selectedUnmarked] at marked <;> simp at marked
      | storedRight =>
          have selectedEq : step.prepared.stackResult.vertex =
              step.consumer.storedRight := by
            simpa [TensorPremiseSide.premise, sideEquation] using
              step.consumer.premise_eq
          have selectedMarked :
              before.core.marks[step.prepared.stackResult.vertex]? =
                some (some olderAge) ∨
              before.core.marks[step.prepared.stackResult.vertex]? =
                some (some youngerAge) := by
            rcases oldOrientation with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact Or.inr (by simpa [selectedEq] using youngerMarked)
            · exact Or.inl (by simpa [selectedEq] using olderMarked)
          rcases selectedMarked with marked | marked <;>
            rw [selectedUnmarked] at marked <;> simp at marked

private theorem conclusion_not_queued_before
    {certificate : Certificate} {before after : ReservationState}
    (step : WaitStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    step.consumer.conclusion ∉ before.stack.queuedVertices := by
  intro queued
  unfold SequentialStackState.queuedVertices at queued
  rcases List.mem_append.mp queued with ready | waiting
  · exact step.conclusion_not_produced_before invariant
      (Or.inr
        (SchedulerInvariant.ready_mem_liveFrontier invariant ready))
  · exact step.conclusion_not_mem_waiting_before invariant waiting

private theorem conclusion_not_queued_middle
    {certificate : Certificate} {before after : ReservationState}
    (step : WaitStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    step.consumer.conclusion ∉
      step.prepared.after.stack.queuedVertices := by
  intro queued
  exact step.conclusion_not_queued_before invariant
    (step.prepared.after_queued_subset_before queued)

private theorem conclusion_ne_selected
    {certificate : Certificate} {before after : ReservationState}
    (step : WaitStep certificate before after) :
    step.consumer.conclusion ≠ step.prepared.stackResult.vertex := by
  have parWellFormed : certificate.LinkWellFormed
      (.par step.consumer.storedLeft step.consumer.storedRight
        step.consumer.conclusion) := by
    simpa [step.par_eq, SequentialConnectiveKind.asLink] using
      step.consumer.wellFormed
  cases sideEquation : step.consumer.side with
  | storedLeft =>
      have selectedEq : step.prepared.stackResult.vertex =
          step.consumer.storedLeft := by
        simpa [TensorPremiseSide.premise, sideEquation] using
          step.consumer.premise_eq
      intro same
      exact parWellFormed.2.1 (selectedEq.symm.trans same.symm)
  | storedRight =>
      have selectedEq : step.prepared.stackResult.vertex =
          step.consumer.storedRight := by
        simpa [TensorPremiseSide.premise, sideEquation] using
          step.consumer.premise_eq
      intro same
      exact parWellFormed.2.2.1 (selectedEq.symm.trans same.symm)

private theorem conclusion_unmarked_middle
    {certificate : Certificate} {before after : ReservationState}
    (step : WaitStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    step.prepared.after.core.marks[step.consumer.conclusion]? =
      some none := by
  rcases UnificationState.markReadyRaw?_exact
      step.prepared.core_mark_eq with
    ⟨_, marksEq, _, _, _, _, _⟩
  change step.prepared.coreMarked.marks[step.consumer.conclusion]? =
    some none
  rw [marksEq]
  simpa [Array.getElem?_setIfInBounds,
    Ne.symm step.conclusion_ne_selected] using
      step.conclusion_unmarked_before invariant

private theorem premise_orientation
    {certificate : Certificate} {before after : ReservationState}
    (step : WaitStep certificate before after) :
    ((step.consumer.mate = step.consumer.storedLeft ∧
        step.prepared.stackResult.vertex = step.consumer.storedRight) ∨
      (step.consumer.mate = step.consumer.storedRight ∧
        step.prepared.stackResult.vertex = step.consumer.storedLeft)) := by
  cases sideEquation : step.consumer.side with
  | storedLeft =>
      right
      constructor
      · simp [ConnectiveBelow.mate, TensorPremiseSide.mate,
          sideEquation]
      · simpa [TensorPremiseSide.premise, sideEquation] using
          step.consumer.premise_eq
  | storedRight =>
      left
      constructor
      · simp [ConnectiveBelow.mate, TensorPremiseSide.mate,
          sideEquation]
      · simpa [TensorPremiseSide.premise, sideEquation] using
          step.consumer.premise_eq

private theorem selected_boundary_middle
    {certificate : Certificate} {before after : ReservationState}
    (step : WaitStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    sigmaBoundary? step.prepared.after.stack.sigma
        step.prepared.stackResult.rawAge =
      some step.prepared.stackResult.rawAge := by
  rcases SequentialStackState.popReadyMark?_exact
      step.prepared.stack_eq with
    ⟨topEquation, sigmaTopEquation, stackUnmarked,
      stackMarksEq, stackNextAgeEq, stackSigmaEq,
      stackReadyEq, stackWaitingEq, stackMarked⟩
  change sigmaBoundary? step.prepared.stackResult.after.sigma
      step.prepared.stackResult.rawAge =
    some step.prepared.stackResult.rawAge
  rw [stackSigmaEq]
  exact invariant.stack_wellShaped.sigma_partition
    |>.sigmaBoundary?_eq_top sigmaTopEquation

/-- Prepending the fresh delayed conclusion preserves global queue
uniqueness. -/
theorem queuedVerticesNodup
    {certificate : Certificate} {before after : ReservationState}
    (step : WaitStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    QueuedVerticesNodup after := by
  have middleInvariant := step.prepared.schedulerInvariant invariant
  have fresh := step.conclusion_not_queued_middle invariant
  rcases SequentialStackState.prependWaiting?_exact
      step.destination.stack_eq with
    ⟨payload, initialized, waitingEq, updated, marksEq,
      nextAgeEq, sigmaEq, readyEq⟩
  have initializedList :
      step.prepared.after.stack.waiting.toList[
        step.destination.boundary]? =
          some (.initialized payload) := by
    rw [Array.getElem?_toList]
    exact initialized
  have oldParts := List.nodup_append.mp
    middleInvariant.queued_vertices_nodup
  have freshReady :
      step.consumer.conclusion ∉
        step.prepared.after.stack.ready.flatten := by
    intro membership
    exact fresh (List.mem_append_left _ membership)
  have freshWaiting : step.consumer.conclusion ∉
      step.prepared.after.stack.waiting.toList.flatMap
        WaitingCell.vertices := by
    intro membership
    exact fresh (List.mem_append_right _ membership)
  have newWaitingNodup :
      (step.prepared.after.stack.waiting.toList.set
        step.destination.boundary
        (.initialized (step.consumer.conclusion :: payload))).flatMap
          WaitingCell.vertices |>.Nodup := by
    apply flatMap_set_cons_nodup initializedList (by rfl)
      oldParts.2.1 freshWaiting
  rw [step.destination.output_eq]
  unfold QueuedVerticesNodup SequentialStackState.queuedVertices
    SequentialStackState.waitingVertices
  rw [readyEq, waitingEq, Array.toList_setIfInBounds]
  apply List.nodup_append.mpr
  refine ⟨oldParts.1, newWaitingNodup, ?_⟩
  intro left leftMembership right rightMembership equal
  have rightCases :=
    (mem_flatMap_set_cons_iff initializedList (by rfl)).mp
      rightMembership
  rcases rightCases with rfl | oldRight
  · subst left
    exact freshReady leftMembership
  · exact oldParts.2.2 left leftMembership right oldRight equal

/-- The new waiting conclusion is raw-unmarked, and every pre-existing queued
occurrence retains its raw-unmarked status. -/
theorem queuedVerticesUnmarked
    {certificate : Certificate} {before after : ReservationState}
    (step : WaitStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    QueuedVerticesUnmarked after := by
  have middleInvariant := step.prepared.schedulerInvariant invariant
  rcases SequentialStackState.prependWaiting?_exact
      step.destination.stack_eq with
    ⟨payload, initialized, waitingEq, updated, marksEq,
      nextAgeEq, sigmaEq, readyEq⟩
  have initializedList :
      step.prepared.after.stack.waiting.toList[
        step.destination.boundary]? =
          some (.initialized payload) := by
    rw [Array.getElem?_toList]
    exact initialized
  rw [step.destination.output_eq]
  intro vertex membership
  unfold SequentialStackState.queuedVertices
    SequentialStackState.waitingVertices at membership
  rw [readyEq, waitingEq, Array.toList_setIfInBounds] at membership
  rcases List.mem_append.mp membership with ready | waiting
  · exact middleInvariant.queued_vertices_unmarked vertex
      (List.mem_append_left _ ready)
  · have waitingCases :=
      (mem_flatMap_set_cons_iff initializedList (by rfl)).mp waiting
    rcases waitingCases with rfl | oldWaiting
    · exact step.conclusion_unmarked_middle invariant
    · exact middleInvariant.queued_vertices_unmarked vertex
        (List.mem_append_right _ oldWaiting)

/-- A successful wait adds exactly its submitted par promise at the computed
older boundary and preserves every pre-existing exact waiting span. -/
theorem waitingSpanExact
    {certificate : Certificate} {before after : ReservationState}
    (step : WaitStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    WaitingSpanExact certificate after := by
  have middleInvariant := step.prepared.schedulerInvariant invariant
  rcases SequentialStackState.prependWaiting?_exact
      step.destination.stack_eq with
    ⟨oldPayload, initialized, waitingEq, updated, marksEq,
      nextAgeEq, sigmaEq, readyEq⟩
  have afterStackEq : after.stack = step.destination.stackAfter :=
    congrArg (fun state : ReservationState => state.stack)
      step.destination.output_eq
  have afterCore : after.core = step.prepared.after.core := by
    have exact := congrArg (fun state : ReservationState => state.core)
      step.destination.output_eq
    exact exact
  have afterSigma :
      after.stack.sigma = step.prepared.after.stack.sigma :=
    (congrArg (fun stack => stack.sigma) afterStackEq).trans sigmaEq
  have afterUpdated :
      after.stack.waiting[step.destination.boundary]? =
        some (.initialized
          (step.consumer.conclusion :: oldPayload)) := by
    rw [afterStackEq]
    exact updated
  unfold WaitingSpanExact
  intro boundary payload conclusion waitingLookup conclusionMembership
  by_cases sameBoundary : boundary = step.destination.boundary
  · subst boundary
    have payloadEq :
        payload = step.consumer.conclusion :: oldPayload := by
      have equal := waitingLookup.symm.trans afterUpdated
      simpa using Option.some.inj equal
    subst payload
    simp only [List.mem_cons] at conclusionMembership
    rcases conclusionMembership with rfl | oldMembership
    · have sourceLookup :=
        SequentialUnification.StructurallyWellFormed.sourceIndex_lookup_eq_submitted_par
          invariant.structural step.submitted_par
      have selectedMarked :
          step.prepared.after.core.marks[
              step.prepared.stackResult.vertex]? =
            some (some step.prepared.stackResult.rawAge) := by
        exact (UnificationState.markReadyRaw?_exact
          step.prepared.core_mark_eq).2.2.2.2.2.2
      have mateMarked :
          step.prepared.after.core.marks[step.consumer.mate]? =
            some (some step.mateRawAge) := by
        exact step.mate_marked
      refine ⟨step.consumer.linkIndex,
        step.consumer.storedLeft, step.consumer.storedRight,
        step.consumer.mate, step.prepared.stackResult.vertex,
        step.mateRawAge, step.prepared.stackResult.rawAge,
        step.prepared.stackResult.rawAge,
        step.submitted_par, sourceLookup, ?_,
        step.premise_orientation, ?_, ?_, ?_, ?_, ?_⟩
      · rw [afterCore]
        exact step.conclusion_unmarked_middle invariant
      · rw [afterCore]
        exact mateMarked
      · rw [afterCore]
        exact selectedMarked
      · rw [afterSigma]
        exact step.destination.boundary_eq
      · rw [afterSigma]
        exact step.selected_boundary_middle invariant
      · have boundaryLe :=
          sigmaBoundary?_le step.destination.boundary_eq
        exact Nat.lt_of_le_of_lt boundaryLe step.younger
    · rcases middleInvariant.waiting_span_exact
          initialized oldMembership with
        ⟨linkIndex, left, right, olderPremise, youngerPremise,
          olderAge, youngerAge, youngerBoundary, linkLookup,
          sourceLookup, conclusionUnmarked, orientation,
          olderMarked, youngerMarked, olderBoundary,
          youngerBoundaryLookup, boundaryOrder⟩
      refine ⟨linkIndex, left, right, olderPremise, youngerPremise,
        olderAge, youngerAge, youngerBoundary, linkLookup,
        sourceLookup, ?_, orientation, ?_, ?_, ?_, ?_, boundaryOrder⟩
      · rw [afterCore]
        exact conclusionUnmarked
      · rw [afterCore]
        exact olderMarked
      · rw [afterCore]
        exact youngerMarked
      · rw [afterSigma]
        exact olderBoundary
      · rw [afterSigma]
        exact youngerBoundaryLookup
  · have unchanged := SequentialStackState.prependWaiting?_of_ne
        step.destination.stack_eq sameBoundary
    have afterLookupEq :
        after.stack.waiting[boundary]? =
          step.prepared.after.stack.waiting[boundary]? := by
      rw [afterStackEq]
      exact unchanged
    rw [afterLookupEq] at waitingLookup
    rcases middleInvariant.waiting_span_exact
        waitingLookup conclusionMembership with
      ⟨linkIndex, left, right, olderPremise, youngerPremise,
        olderAge, youngerAge, youngerBoundary, linkLookup,
        sourceLookup, conclusionUnmarked, orientation,
        olderMarked, youngerMarked, olderBoundary,
        youngerBoundaryLookup, boundaryOrder⟩
    refine ⟨linkIndex, left, right, olderPremise, youngerPremise,
      olderAge, youngerAge, youngerBoundary, linkLookup,
      sourceLookup, ?_, orientation, ?_, ?_, ?_, ?_, boundaryOrder⟩
    · rw [afterCore]
      exact conclusionUnmarked
    · rw [afterCore]
      exact olderMarked
    · rw [afterCore]
      exact youngerMarked
    · rw [afterSigma]
      exact olderBoundary
    · rw [afterSigma]
      exact youngerBoundaryLookup

/-- An exact successful `wait` preserves every field of the current
state-based scheduler invariant.  This is a successful-step theorem, not a
claim that `wait` is the applicable rule or that the dispatcher makes
progress. -/
theorem schedulerInvariant
    {certificate : Certificate} {before after : ReservationState}
    (step : WaitStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    SchedulerInvariant certificate after := by
  have middleInvariant := step.prepared.schedulerInvariant invariant
  rcases step.destination.exact with
    ⟨payload, initialized, updated, stackMarksEq, nextAgeEq,
      sigmaEq, readyEq, coreEq, tagsEq⟩
  exact {
    toReservationInvariant := step.reservationInvariant
    structural := invariant.structural
    component_domain_exact := by
      simpa [ComponentDomainExact, coreEq, sigmaEq] using
        middleInvariant.component_domain_exact
    component_forest_provenance := by
      simpa [coreEq] using
        middleInvariant.component_forest_provenance
    live_frontiers_nodup := by
      simpa [LiveFrontiersNodup, coreEq] using
        middleInvariant.live_frontiers_nodup
    ready_bucket_frontier_exact := by
      unfold ReadyBucketFrontierExact
      intro position boundary bucket sigmaLookup readyLookup
      rw [sigmaEq] at sigmaLookup
      rw [readyEq] at readyLookup
      rcases middleInvariant.ready_bucket_frontier_exact
          sigmaLookup readyLookup with
        ⟨component, componentLookup, exactMembership⟩
      refine ⟨component, ?_, ?_⟩
      · rw [coreEq]
        exact componentLookup
      · intro vertex
        rw [coreEq]
        exact exactMembership vertex
    queued_vertices_nodup := step.queuedVerticesNodup invariant
    queued_vertices_unmarked := step.queuedVerticesUnmarked invariant
    produced_premises_marked := by
      intro link linkMembership
      cases link with
      | «axiom» left right => trivial
      | «par» left right conclusion
      | tensor left right conclusion =>
          intro producedAfter
          have producedMiddle :
              Produced step.prepared.after conclusion := by
            simpa [Produced, coreEq] using producedAfter
          rcases middleInvariant.produced_premises_marked
              linkMembership producedMiddle with
            ⟨⟨leftAge, leftMarked⟩, rightAge, rightMarked⟩
          refine ⟨⟨leftAge, ?_⟩, rightAge, ?_⟩
          · rw [coreEq]
            exact leftMarked
          · rw [coreEq]
            exact rightMarked
    waiting_span_exact := step.waitingSpanExact invariant
    pending_premises_covered_except_ready := by
      intro link linkMembership
      cases link with
      | «axiom» left right => trivial
      | «par» left right conclusion
      | tensor left right conclusion =>
          intro conclusionUnmarked conclusionNotReady premise token
            premiseMembership tokenAt
          rw [coreEq] at conclusionUnmarked tokenAt ⊢
          rw [readyEq] at conclusionNotReady
          exact middleInvariant.pending_premises_covered_except_ready
            linkMembership conclusionUnmarked conclusionNotReady
            premiseMembership tokenAt
    fired_counter_exact := by
      simpa [FiredCounterExact, coreEq] using
        middleInvariant.fired_counter_exact }

end WaitStep

namespace UnifyEmptyStep

private theorem tensor_wellFormed
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyEmptyStep certificate before after) :
    certificate.LinkWellFormed
      (.tensor step.consumer.storedLeft step.consumer.storedRight
        step.consumer.conclusion) := by
  simpa [step.tensor_eq, SequentialConnectiveKind.asLink] using
    step.consumer.wellFormed

private theorem premise_orientation
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyEmptyStep certificate before after) :
    ((step.consumer.mate = step.consumer.storedLeft ∧
        step.prepared.stackResult.vertex = step.consumer.storedRight) ∨
      (step.consumer.mate = step.consumer.storedRight ∧
        step.prepared.stackResult.vertex = step.consumer.storedLeft)) := by
  cases sideEquation : step.consumer.side with
  | storedLeft =>
      right
      constructor
      · simp [ConnectiveBelow.mate, TensorPremiseSide.mate,
          sideEquation]
      · simpa [TensorPremiseSide.premise, sideEquation] using
          step.consumer.premise_eq
  | storedRight =>
      left
      constructor
      · simp [ConnectiveBelow.mate, TensorPremiseSide.mate,
          sideEquation]
      · simpa [TensorPremiseSide.premise, sideEquation] using
          step.consumer.premise_eq

private theorem conclusion_ne_selected
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyEmptyStep certificate before after) :
    step.consumer.conclusion ≠ step.prepared.stackResult.vertex := by
  have tensorWellFormed := step.tensor_wellFormed
  cases sideEquation : step.consumer.side with
  | storedLeft =>
      have selectedEq : step.prepared.stackResult.vertex =
          step.consumer.storedLeft := by
        simpa [TensorPremiseSide.premise, sideEquation] using
          step.consumer.premise_eq
      intro same
      exact tensorWellFormed.2.1 (selectedEq.symm.trans same.symm)
  | storedRight =>
      have selectedEq : step.prepared.stackResult.vertex =
          step.consumer.storedRight := by
        simpa [TensorPremiseSide.premise, sideEquation] using
          step.consumer.premise_eq
      intro same
      exact tensorWellFormed.2.2.1 (selectedEq.symm.trans same.symm)

private theorem conclusion_not_produced_before
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyEmptyStep certificate before after)
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
          step.consumer.premise_eq
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
          step.consumer.premise_eq
      have rightUnmarked :
          before.core.marks[step.consumer.storedRight]? = some none :=
        (congrArg (fun vertex => before.core.marks[vertex]?)
          selectedEq).symm.trans selectedUnmarked
      rw [rightUnmarked] at rightMarked
      simp at rightMarked

private theorem conclusion_not_produced_middle
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyEmptyStep certificate before after)
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
    (step : UnifyEmptyStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    step.consumer.conclusion ∉ before.stack.waitingVertices := by
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
    (step : UnifyEmptyStep certificate before after)
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
    (step : UnifyEmptyStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    step.consumer.conclusion ∉
      step.prepared.after.stack.queuedVertices := by
  intro queued
  unfold SequentialStackState.queuedVertices at queued
  rcases List.mem_append.mp queued with ready | waiting
  · exact step.conclusion_not_produced_middle invariant
      (Or.inr
        (SchedulerInvariant.ready_mem_liveFrontier
          (step.prepared.schedulerInvariant invariant) ready))
  · exact step.conclusion_not_mem_waiting_middle invariant waiting

private theorem activeBoundary_eq
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyEmptyStep certificate before after) :
    step.mergeStep.activeBoundary =
      step.prepared.stackResult.rawAge := by
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

private theorem middle_sigma_eq
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyEmptyStep certificate before after) :
    step.prepared.stackResult.after.sigma =
      step.mergeStep.sigmaPrefix ++
        [step.previousBoundary, step.prepared.stackResult.rawAge] := by
  simpa [step.activeBoundary_eq] using step.mergeStep.sigma_eq

private theorem previous_lt_active
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyEmptyStep certificate before after) :
    step.previousBoundary < step.prepared.stackResult.rawAge :=
  Nat.lt_of_le_of_lt step.lower step.upper

private theorem min_token_eq
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyEmptyStep certificate before after) :
    min step.queueStep.leftToken step.queueStep.rightToken =
      step.previousBoundary := by
  rcases step.tokens_eq_adjacent with orientation | orientation
  · rw [orientation.2.1, orientation.2.2]
    exact Nat.min_eq_right (Nat.le_of_lt step.previous_lt_active)
  · rw [orientation.2.1, orientation.2.2]
    exact Nat.min_eq_left (Nat.le_of_lt step.previous_lt_active)

private theorem max_token_eq
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyEmptyStep certificate before after) :
    max step.queueStep.leftToken step.queueStep.rightToken =
      step.prepared.stackResult.rawAge := by
  rcases step.tokens_eq_adjacent with orientation | orientation
  · rw [orientation.2.1, orientation.2.2]
    exact Nat.max_eq_left (Nat.le_of_lt step.previous_lt_active)
  · rw [orientation.2.1, orientation.2.2]
    exact Nat.max_eq_right (Nat.le_of_lt step.previous_lt_active)

private def mergedComponent
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyEmptyStep certificate before after) :
    UnificationComponent := {
  tree := .tensor step.queueStep.leftFocus step.queueStep.rightFocus
    step.queueStep.leftComponent.tree step.queueStep.rightComponent.tree
  frontier := step.consumer.conclusion ::
    (step.queueStep.leftContext ++ step.queueStep.rightContext) }

private theorem payload_eq_empty
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyEmptyStep certificate before after) :
    step.mergeStep.payload = [] := by
  exact WaitingCell.initialized.inj
    (Option.some.inj
      (step.mergeStep.waiting_initialized.symm.trans step.waiting_empty))

private theorem after_core_eq
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyEmptyStep certificate before after) :
    after.core = step.coreAfter :=
  congrArg (fun state : ReservationState => state.core) step.output_eq

private theorem after_stack_eq
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyEmptyStep certificate before after) :
    after.stack = step.stackAfter :=
  congrArg (fun state : ReservationState => state.stack) step.output_eq

private theorem core_marks_eq
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyEmptyStep certificate before after) :
    after.core.marks = step.prepared.coreMarked.marks := by
  rw [step.after_core_eq, step.queueStep.after_eq]

private theorem core_components_eq
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyEmptyStep certificate before after) :
    after.core.components =
      ((step.prepared.coreMarked.components.setIfInBounds
          step.previousBoundary (some step.mergedComponent))
        |>.setIfInBounds step.prepared.stackResult.rawAge none) := by
  rw [step.after_core_eq, step.queueStep.after_eq,
    step.min_token_eq, step.max_token_eq]
  rfl

private theorem after_sigma_eq
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyEmptyStep certificate before after) :
    after.stack.sigma =
      step.mergeStep.sigmaPrefix ++ [step.previousBoundary] := by
  calc
    after.stack.sigma = step.stackAfter.sigma :=
      congrArg (fun state : SequentialStackState => state.sigma)
        step.after_stack_eq
    _ = step.mergeStep.sigmaPrefix ++ [step.previousBoundary] := by
      simpa using congrArg
        (fun state : SequentialStackState => state.sigma)
        step.mergeStep.after_eq

private theorem after_ready_eq
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyEmptyStep certificate before after) :
    after.stack.ready =
      step.mergeStep.readyPrefix ++
        [step.consumer.conclusion ::
          (step.mergeStep.previousReady ++ step.mergeStep.activeReady)] := by
  calc
    after.stack.ready = step.stackAfter.ready :=
      congrArg (fun state : SequentialStackState => state.ready)
        step.after_stack_eq
    _ = step.mergeStep.readyPrefix ++
          [step.consumer.conclusion ::
            (step.mergeStep.previousReady ++
              step.mergeStep.activeReady)] := by
      simpa [step.payload_eq_empty] using congrArg
        (fun state : SequentialStackState => state.ready)
        step.mergeStep.after_eq

private theorem after_waiting_eq
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyEmptyStep certificate before after) :
    after.stack.waiting =
      step.prepared.stackResult.after.waiting.setIfInBounds
        step.previousBoundary .undefined := by
  calc
    after.stack.waiting = step.stackAfter.waiting :=
      congrArg (fun state : SequentialStackState => state.waiting)
        step.after_stack_eq
    _ = step.prepared.stackResult.after.waiting.setIfInBounds
          step.previousBoundary .undefined := by
      simpa using congrArg
        (fun state : SequentialStackState => state.waiting)
        step.mergeStep.after_eq

private theorem left_root
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyEmptyStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    step.prepared.coreMarked.representative step.queueStep.leftToken =
      step.queueStep.leftToken := by
  have middleInvariant := step.prepared.schedulerInvariant invariant
  exact middleInvariant.core_abstractable.tokenAt?_root
    (UnificationState.unifyTokens?_success
      step.queueStep.token_guard).2.1

private theorem right_root
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyEmptyStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    step.prepared.coreMarked.representative step.queueStep.rightToken =
      step.queueStep.rightToken := by
  have middleInvariant := step.prepared.schedulerInvariant invariant
  exact middleInvariant.core_abstractable.tokenAt?_root
    (UnificationState.unifyTokens?_success
      step.queueStep.token_guard).2.2.1

private theorem left_component_raw
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyEmptyStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    step.prepared.coreMarked.components[step.queueStep.leftToken]? =
      some (some step.queueStep.leftComponent) := by
  have raw := UnificationState.componentAt?_some_raw
    step.queueStep.left_component
  simpa [step.left_root invariant] using raw

private theorem right_component_raw
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyEmptyStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    step.prepared.coreMarked.components[step.queueStep.rightToken]? =
      some (some step.queueStep.rightComponent) := by
  have raw := UnificationState.componentAt?_some_raw
    step.queueStep.right_component
  simpa [step.right_root invariant] using raw

private theorem previous_bound
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyEmptyStep certificate before after)
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
    (step : UnifyEmptyStep certificate before after)
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

private theorem componentDomainExact
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyEmptyStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    ComponentDomainExact after := by
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
  rw [step.core_components_eq, step.after_sigma_eq]
  by_cases previous : token = step.previousBoundary
  · subst token
    constructor
    · intro _
      simp
    · intro _
      refine ⟨step.mergedComponent, ?_⟩
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

private theorem readyBucketFrontierExact
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyEmptyStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    ReadyBucketFrontierExact after := by
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
    UnificationState.unifyTokens?_success step.queueStep.token_guard
  have left_context_of_frontier_unmarked :
      ∀ {vertex},
        vertex ∈ step.queueStep.leftComponent.frontier →
        step.prepared.coreMarked.marks[vertex]? = some none →
        vertex ∈ step.queueStep.leftContext := by
    intro vertex frontier unmarked
    have vertexNeLeft : vertex ≠ step.consumer.storedLeft := by
      intro same
      subst vertex
      unfold UnificationState.tokenAt? at tokenGuards
      rw [unmarked] at tokenGuards
      simp at tokenGuards
    exact Certificate.FirstOccurrencePick.mem_remaining_of_ne
      step.queueStep.left_pick vertexNeLeft frontier
  have right_context_of_frontier_unmarked :
      ∀ {vertex},
        vertex ∈ step.queueStep.rightComponent.frontier →
        step.prepared.coreMarked.marks[vertex]? = some none →
        vertex ∈ step.queueStep.rightContext := by
    intro vertex frontier unmarked
    have vertexNeRight : vertex ≠ step.consumer.storedRight := by
      intro same
      subst vertex
      unfold UnificationState.tokenAt? at tokenGuards
      rw [unmarked] at tokenGuards
      simp at tokenGuards
    exact Certificate.FirstOccurrencePick.mem_remaining_of_ne
      step.queueStep.right_pick vertexNeRight frontier
  have left_frontier_of_context :
      ∀ {vertex}, vertex ∈ step.queueStep.leftContext →
        vertex ∈ step.queueStep.leftComponent.frontier := by
    intro vertex membership
    exact (CutFreeDerivation.pick?_perm
      step.queueStep.left_pick.positional).mem_iff.mpr (by
        simp [membership])
  have right_frontier_of_context :
      ∀ {vertex}, vertex ∈ step.queueStep.rightContext →
        vertex ∈ step.queueStep.rightComponent.frontier := by
    intro vertex membership
    exact (CutFreeDerivation.pick?_perm
      step.queueStep.right_pick.positional).mem_iff.mpr (by
        simp [membership])
  unfold ReadyBucketFrontierExact
  intro position boundary bucket sigmaLookup readyLookup
  rw [step.after_sigma_eq] at sigmaLookup
  rw [step.after_ready_eq] at readyLookup
  have positionBound :
      position <
        (step.mergeStep.readyPrefix ++
          [step.consumer.conclusion ::
            (step.mergeStep.previousReady ++
              step.mergeStep.activeReady)]).length :=
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
            step.prepared.stackResult.rawAge]).Pairwise ( · < · ) := by
      have oldIncreasing :=
        middleInvariant.stack_wellShaped.sigma_partition.strictIncreasing
      change step.prepared.stackResult.after.sigma.Pairwise ( · < · )
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
    · rw [step.core_components_eq,
        Array.getElem?_setIfInBounds_ne activeNeBoundary,
        Array.getElem?_setIfInBounds_ne previousNeBoundary]
      exact componentLookup
    · intro vertex
      rw [step.core_marks_eq]
      exact exactMembership vertex
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
          (step.mergeStep.previousReady ++
            step.mergeStep.activeReady) := by
      simp at readyLookup
      exact readyLookup.symm
    subst boundary
    subst bucket
    refine ⟨step.mergedComponent, ?_, ?_⟩
    · rw [step.core_components_eq,
        Array.getElem?_setIfInBounds_ne
          (Nat.ne_of_gt step.previous_lt_active)]
      simp [step.previous_bound invariant]
    · intro vertex
      rw [step.core_marks_eq]
      rcases step.tokens_eq_adjacent with orientation | orientation
      · have rightRaw := step.right_component_raw invariant
        have leftRaw := step.left_component_raw invariant
        rw [orientation.2.2] at rightRaw
        rw [orientation.2.1] at leftRaw
        have previousComponentEq :
            previousComponent = step.queueStep.rightComponent :=
          Option.some.inj (Option.some.inj
            (previousComponentLookup.symm.trans rightRaw))
        have activeComponentEq :
            activeComponent = step.queueStep.leftComponent :=
          Option.some.inj (Option.some.inj
            (activeComponentLookup.symm.trans leftRaw))
        subst previousComponent
        subst activeComponent
        change vertex ∈ step.consumer.conclusion ::
            (step.mergeStep.previousReady ++ step.mergeStep.activeReady) ↔
          vertex ∈ step.consumer.conclusion ::
              (step.queueStep.leftContext ++ step.queueStep.rightContext) ∧
            step.prepared.coreMarked.marks[vertex]? = some none
        constructor
        · intro membership
          simp only [List.mem_cons, List.mem_append] at membership ⊢
          rcases membership with rfl | inPrevious | inActive
          · exact ⟨Or.inl rfl, tokenGuards.1⟩
          · have facts := (previousExact vertex).mp inPrevious
            exact ⟨Or.inr (Or.inr
              (right_context_of_frontier_unmarked facts.1 facts.2)),
              facts.2⟩
          · have facts := (activeExact vertex).mp inActive
            exact ⟨Or.inr (Or.inl
              (left_context_of_frontier_unmarked facts.1 facts.2)),
              facts.2⟩
        · rintro ⟨frontier, unmarked⟩
          simp only [List.mem_cons, List.mem_append] at frontier ⊢
          rcases frontier with rfl | inLeft | inRight
          · exact Or.inl rfl
          · exact Or.inr (Or.inr ((activeExact vertex).mpr
              ⟨left_frontier_of_context inLeft, unmarked⟩))
          · exact Or.inr (Or.inl ((previousExact vertex).mpr
              ⟨right_frontier_of_context inRight, unmarked⟩))
      · have leftRaw := step.left_component_raw invariant
        have rightRaw := step.right_component_raw invariant
        rw [orientation.2.1] at leftRaw
        rw [orientation.2.2] at rightRaw
        have previousComponentEq :
            previousComponent = step.queueStep.leftComponent :=
          Option.some.inj (Option.some.inj
            (previousComponentLookup.symm.trans leftRaw))
        have activeComponentEq :
            activeComponent = step.queueStep.rightComponent :=
          Option.some.inj (Option.some.inj
            (activeComponentLookup.symm.trans rightRaw))
        subst previousComponent
        subst activeComponent
        change vertex ∈ step.consumer.conclusion ::
            (step.mergeStep.previousReady ++ step.mergeStep.activeReady) ↔
          vertex ∈ step.consumer.conclusion ::
              (step.queueStep.leftContext ++ step.queueStep.rightContext) ∧
            step.prepared.coreMarked.marks[vertex]? = some none
        constructor
        · intro membership
          simp only [List.mem_cons, List.mem_append] at membership ⊢
          rcases membership with rfl | inPrevious | inActive
          · exact ⟨Or.inl rfl, tokenGuards.1⟩
          · have facts := (previousExact vertex).mp inPrevious
            exact ⟨Or.inr (Or.inl
              (left_context_of_frontier_unmarked facts.1 facts.2)),
              facts.2⟩
          · have facts := (activeExact vertex).mp inActive
            exact ⟨Or.inr (Or.inr
              (right_context_of_frontier_unmarked facts.1 facts.2)),
              facts.2⟩
        · rintro ⟨frontier, unmarked⟩
          simp only [List.mem_cons, List.mem_append] at frontier ⊢
          rcases frontier with rfl | inLeft | inRight
          · exact Or.inl rfl
          · exact Or.inr (Or.inl ((previousExact vertex).mpr
              ⟨left_frontier_of_context inLeft, unmarked⟩))
          · exact Or.inr (Or.inr ((activeExact vertex).mpr
              ⟨right_frontier_of_context inRight, unmarked⟩))

private theorem representative_after
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyEmptyStep certificate before after)
    (invariant : SchedulerInvariant certificate before)
    {rawAge : RawTokenAge}
    (rawBound : rawAge < step.prepared.coreMarked.parents.size) :
    after.core.representative rawAge =
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
  calc
    after.core.representative rawAge =
        (step.prepared.coreMarked.setParent
          step.prepared.stackResult.rawAge
          step.previousBoundary).representative rawAge := by
      unfold UnificationState.representative
      rw [step.after_core_eq, step.queueStep.after_eq,
        step.max_token_eq, step.min_token_eq]
      rfl
    _ = _ :=
      middleOrdered.setParent_representative
        previousParentBound activeParentBound
        step.previous_lt_active previousRoot activeRoot rawBound

private theorem merged_componentAt
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyEmptyStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    after.core.componentAt? step.previousBoundary =
      some step.mergedComponent := by
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
      after.core.representative step.previousBoundary =
        step.previousBoundary := by
    rw [step.representative_after invariant previousParentBound,
      previousRootMiddle]
    simp [Nat.ne_of_lt step.previous_lt_active]
  unfold UnificationState.componentAt?
  rw [previousRootAfter, step.core_components_eq]
  rw [Array.getElem?_setIfInBounds_ne
    (Nat.ne_of_gt step.previous_lt_active)]
  simp [step.previous_bound invariant]

private theorem perm_insert_after
    {α : Type} (initial suffix : List α) (inserted : α) :
    (initial ++ inserted :: suffix).Perm
      (inserted :: (initial ++ suffix)) := by
  induction initial with
  | nil => simp
  | cons head tail induction =>
      simp only [List.cons_append]
      exact (List.Perm.cons head induction).trans
        (List.Perm.swap inserted head (tail ++ suffix))

private theorem queuedVertices_perm
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyEmptyStep certificate before after) :
    after.stack.queuedVertices.Perm
      (step.consumer.conclusion ::
        step.prepared.after.stack.queuedVertices) := by
  have waitingFlatEq :
      (step.prepared.stackResult.after.waiting.setIfInBounds
          step.previousBoundary .undefined).toList.flatMap
          WaitingCell.vertices =
        step.prepared.stackResult.after.waiting.toList.flatMap
          WaitingCell.vertices :=
    array_flatMap_set_eq_of_getElem?_eq step.waiting_empty (by rfl)
  unfold SequentialStackState.queuedVertices
    SequentialStackState.waitingVertices
  rw [step.after_ready_eq, step.after_waiting_eq]
  simp only [PreparedStep.after]
  rw [waitingFlatEq, step.mergeStep.ready_eq]
  simp only [List.flatten_append, List.flatten_cons, List.flatten_nil,
    List.append_nil, List.append_assoc, List.cons_append]
  exact perm_insert_after step.mergeStep.readyPrefix.flatten
    (step.mergeStep.previousReady ++
      (step.mergeStep.activeReady ++
        step.prepared.stackResult.after.waiting.toList.flatMap
          WaitingCell.vertices))
    step.consumer.conclusion

private theorem queuedVerticesNodup
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyEmptyStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    QueuedVerticesNodup after := by
  have middleInvariant := step.prepared.schedulerInvariant invariant
  have targetNodup :
      (step.consumer.conclusion ::
        step.prepared.after.stack.queuedVertices).Nodup :=
    List.nodup_cons.mpr
      ⟨step.conclusion_not_queued_middle invariant,
        middleInvariant.queued_vertices_nodup⟩
  exact step.queuedVertices_perm.symm.nodup targetNodup

private theorem queuedVerticesUnmarked
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyEmptyStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    QueuedVerticesUnmarked after := by
  have middleInvariant := step.prepared.schedulerInvariant invariant
  intro vertex membership
  have targetMembership := step.queuedVertices_perm.mem_iff.mp membership
  simp only [List.mem_cons] at targetMembership
  rcases targetMembership with rfl | oldMembership
  · rw [step.core_marks_eq]
    exact (UnificationState.unifyTokens?_success
      step.queueStep.token_guard).1
  · rw [step.core_marks_eq]
    exact middleInvariant.queued_vertices_unmarked vertex oldMembership

private theorem componentForestProvenance
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyEmptyStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    certificate.ComponentForestProvenance after.core := by
  have middleInvariant := step.prepared.schedulerInvariant invariant
  have middleOrdered : step.prepared.coreMarked.OrderedParents := by
    intro token parent lookup
    exact middleInvariant.core_orderedParents lookup
  have conclusionFresh :
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
      change step.prepared.after.core.components[index]? =
        some (some component) at componentLookup
      change step.consumer.conclusion ∈
        step.prepared.after.core.liveFrontierVertices
      unfold UnificationState.liveFrontierVertices
      apply List.mem_flatMap.mpr
      refine ⟨some component, ?_, ?_⟩
      · exact List.mem_of_getElem? (by simpa using componentLookup)
      · simpa using frontier
  have forestAfterCore :=
    Certificate.ComponentForestProvenance.queueTensorStep_of_roots_fresh
      middleInvariant.core_abstractable middleOrdered
      middleInvariant.component_forest_provenance step.queueStep
      step.consumer.linkIndex step.submitted_tensor conclusionFresh
  have coreEq : after.core = step.coreAfter :=
    congrArg (fun state : ReservationState => state.core) step.output_eq
  rw [coreEq]
  exact forestAfterCore

/-- The occurrence-exact component forest supplies duplicate-freedom after
the two-component tensor merge. -/
private theorem liveFrontiersNodup
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyEmptyStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    LiveFrontiersNodup after := by
  unfold LiveFrontiersNodup
  simpa [UnificationState.liveFrontierVertices] using
    (step.componentForestProvenance invariant).liveFrontiers_nodup

private theorem submittedPremisesMarkedAfter
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyEmptyStep certificate before after) :
    (∃ leftAge,
      after.core.marks[step.consumer.storedLeft]? =
        some (some leftAge)) ∧
      ∃ rightAge,
        after.core.marks[step.consumer.storedRight]? =
          some (some rightAge) := by
  have selectedMarked :
      step.prepared.coreMarked.marks[
          step.prepared.stackResult.vertex]? =
        some (some step.prepared.stackResult.rawAge) :=
    (UnificationState.markReadyRaw?_exact
      step.prepared.core_mark_eq).2.2.2.2.2.2
  rcases step.premise_orientation with
    ⟨mateEq, selectedEq⟩ | ⟨mateEq, selectedEq⟩
  · constructor
    · exact ⟨step.mateRawAge, by
        rw [step.core_marks_eq, ← mateEq]
        exact step.mate_marked⟩
    · exact ⟨step.prepared.stackResult.rawAge, by
        rw [step.core_marks_eq, ← selectedEq]
        exact selectedMarked⟩
  · constructor
    · exact ⟨step.prepared.stackResult.rawAge, by
        rw [step.core_marks_eq, ← selectedEq]
        exact selectedMarked⟩
    · exact ⟨step.mateRawAge, by
        rw [step.core_marks_eq, ← mateEq]
        exact step.mate_marked⟩

private theorem produced_after_cases
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyEmptyStep certificate before after)
    (invariant : SchedulerInvariant certificate before)
    {vertex : Vertex}
    (produced : Produced after vertex) :
    vertex = step.consumer.conclusion ∨
      Produced step.prepared.after vertex := by
  rcases produced with ⟨rawAge, marked⟩ | frontierMembership
  · apply Or.inr
    apply Or.inl
    refine ⟨rawAge, ?_⟩
    rw [step.core_marks_eq] at marked
    exact marked
  · unfold UnificationState.liveFrontierVertices at frontierMembership
    rcases List.mem_flatMap.mp frontierMembership with
      ⟨cell, cellMembership, vertexFrontier⟩
    cases cell with
    | none => simp at vertexFrontier
    | some component =>
        simp only [Option.map_some, Option.getD_some] at vertexFrontier
        rcases List.mem_iff_getElem.mp cellMembership with
          ⟨index, indexBound, indexEquation⟩
        have afterLookup :
            after.core.components[index]? = some (some component) := by
          rw [← Array.getElem?_toList]
          rw [List.getElem?_eq_getElem indexBound, indexEquation]
        by_cases previous : index = step.previousBoundary
        · subst index
          rw [step.core_components_eq] at afterLookup
          simp [step.previous_bound invariant,
            Nat.ne_of_gt step.previous_lt_active] at afterLookup
          subst component
          simp only [mergedComponent, List.mem_cons,
            List.mem_append] at vertexFrontier
          rcases vertexFrontier with rfl | inLeft | inRight
          · exact Or.inl rfl
          · apply Or.inr
            apply Or.inr
            unfold UnificationState.liveFrontierVertices
            apply List.mem_flatMap.mpr
            refine ⟨some step.queueStep.leftComponent, ?_, ?_⟩
            · exact List.mem_of_getElem? (by
                simpa [PreparedStep.after] using
                  step.left_component_raw invariant)
            · exact (CutFreeDerivation.pick?_perm
                step.queueStep.left_pick.positional).mem_iff.mpr (by
                  simp [inLeft])
          · apply Or.inr
            apply Or.inr
            unfold UnificationState.liveFrontierVertices
            apply List.mem_flatMap.mpr
            refine ⟨some step.queueStep.rightComponent, ?_, ?_⟩
            · exact List.mem_of_getElem? (by
                simpa [PreparedStep.after] using
                  step.right_component_raw invariant)
            · exact (CutFreeDerivation.pick?_perm
                step.queueStep.right_pick.positional).mem_iff.mpr (by
                  simp [inRight])
        · by_cases active :
              index = step.prepared.stackResult.rawAge
          · subst index
            rw [step.core_components_eq] at afterLookup
            simp [step.active_bound invariant] at afterLookup
          · apply Or.inr
            apply Or.inr
            unfold UnificationState.liveFrontierVertices
            apply List.mem_flatMap.mpr
            refine ⟨some component, ?_, by simpa using vertexFrontier⟩
            have oldLookup :
                step.prepared.coreMarked.components[index]? =
                  some (some component) := by
              rw [step.core_components_eq] at afterLookup
              simpa [Array.getElem?_setIfInBounds, Ne.symm previous,
                Ne.symm active] using afterLookup
            exact List.mem_of_getElem? (by
              simpa [PreparedStep.after] using oldLookup)

private theorem producedPremisesMarked
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyEmptyStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    ProducedPremisesMarked certificate after := by
  have middleInvariant := step.prepared.schedulerInvariant invariant
  intro link linkMembership
  cases link with
  | «axiom» left right => trivial
  | «par» left right conclusion
  | tensor left right conclusion =>
      intro producedAfter
      rcases step.produced_after_cases invariant producedAfter with
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
          exact step.submittedPremisesMarkedAfter
      · rcases middleInvariant.produced_premises_marked
            linkMembership producedMiddle with
          ⟨⟨leftAge, leftMarked⟩, rightAge, rightMarked⟩
        refine ⟨⟨leftAge, ?_⟩, rightAge, ?_⟩
        · rw [step.core_marks_eq]
          exact leftMarked
        · rw [step.core_marks_eq]
          exact rightMarked

private theorem conclusion_mem_ready_after
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyEmptyStep certificate before after) :
    step.consumer.conclusion ∈ after.stack.ready.flatten := by
  rw [step.after_ready_eq]
  apply List.mem_flatten.mpr
  exact ⟨step.consumer.conclusion ::
      (step.mergeStep.previousReady ++ step.mergeStep.activeReady),
    by simp, by simp⟩

private theorem oldReady_subset_after
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyEmptyStep certificate before after)
    {vertex : Vertex}
    (membership :
      vertex ∈ step.prepared.after.stack.ready.flatten) :
    vertex ∈ after.stack.ready.flatten := by
  change vertex ∈
    step.prepared.stackResult.after.ready.flatten at membership
  rw [step.mergeStep.ready_eq] at membership
  rw [step.after_ready_eq]
  simp only [List.flatten_append, List.flatten_cons,
    List.flatten_nil, List.append_nil, List.mem_append,
    List.mem_cons] at membership ⊢
  rcases membership with inPrefix | inPrevious | inActive
  · exact Or.inl inPrefix
  · exact Or.inr (Or.inr (Or.inl inPrevious))
  · exact Or.inr (Or.inr (Or.inr inActive))

private theorem pendingPremisesCoveredExceptReady
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyEmptyStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    PendingPremisesCoveredExceptReady certificate after := by
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
        exact conclusionNotReady step.conclusion_mem_ready_after
      have middleConclusionUnmarked :
          step.prepared.after.core.marks[conclusion]? = some none := by
        change step.prepared.coreMarked.marks[conclusion]? = some none
        rw [← step.core_marks_eq]
        exact conclusionUnmarked
      have middleConclusionNotReady :
          conclusion ∉ step.prepared.after.stack.ready.flatten := by
        intro membership
        exact conclusionNotReady (step.oldReady_subset_after membership)
      rcases after.core.tokenAt?_some_witness tokenAt with
        ⟨rawAge, assignedAfter, representativeAfter⟩
      have assignedMiddle :
          step.prepared.coreMarked.assignedToken? premise =
            some rawAge := by
        unfold UnificationState.assignedToken? at assignedAfter ⊢
        rw [step.core_marks_eq] at assignedAfter
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
        have transported := step.representative_after invariant rawBound
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
      by_cases oldIsLeft : oldToken = step.queueStep.leftToken
      · have rawLookup :=
          UnificationState.componentAt?_some_raw componentLookup
        rw [oldRoot, oldIsLeft] at rawLookup
        have componentEq : component = step.queueStep.leftComponent :=
          Option.some.inj (Option.some.inj
            (rawLookup.symm.trans (step.left_component_raw invariant)))
        subst component
        have inContext :=
          Certificate.FirstOccurrencePick.mem_remaining_of_ne
            step.queueStep.left_pick premiseNeLeft premiseFrontier
        have tokenPrevious : token = step.previousBoundary := by
          rw [tokenTransport, oldIsLeft]
          rcases step.tokens_eq_adjacent with orientation | orientation
          · rw [orientation.2.1]
            simp
          · rw [orientation.2.1]
            simp [Nat.ne_of_lt step.previous_lt_active]
        refine ⟨step.mergedComponent, ?_,
          by simp [mergedComponent, inContext]⟩
        rw [tokenPrevious]
        exact step.merged_componentAt invariant
      · by_cases oldIsRight : oldToken = step.queueStep.rightToken
        · have rawLookup :=
            UnificationState.componentAt?_some_raw componentLookup
          rw [oldRoot, oldIsRight] at rawLookup
          have componentEq : component = step.queueStep.rightComponent :=
            Option.some.inj (Option.some.inj
              (rawLookup.symm.trans (step.right_component_raw invariant)))
          subst component
          have inContext :=
            Certificate.FirstOccurrencePick.mem_remaining_of_ne
              step.queueStep.right_pick premiseNeRight premiseFrontier
          have tokenPrevious : token = step.previousBoundary := by
            rw [tokenTransport, oldIsRight]
            rcases step.tokens_eq_adjacent with orientation | orientation
            · rw [orientation.2.2]
              simp [Nat.ne_of_lt step.previous_lt_active]
            · rw [orientation.2.2]
              simp
          refine ⟨step.mergedComponent, ?_,
            by simp [mergedComponent, inContext]⟩
          rw [tokenPrevious]
          exact step.merged_componentAt invariant
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
              after.core.representative oldToken = oldToken := by
            rw [step.representative_after invariant oldParentBound,
              oldRoot]
            simp [oldNeActive]
          rw [tokenOld]
          unfold UnificationState.componentAt? at componentLookup ⊢
          rw [oldRoot] at componentLookup
          rw [afterOldRoot, step.core_components_eq]
          rw [Array.getElem?_setIfInBounds_ne (Ne.symm oldNeActive),
            Array.getElem?_setIfInBounds_ne (Ne.symm oldNePrevious)]
          exact componentLookup

private theorem waitingSpanExact
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyEmptyStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    WaitingSpanExact certificate after := by
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
      (Array.getElem?_eq_some_iff.mp step.waiting_empty).1
    rw [step.after_waiting_eq] at waitingLookup
    simp [previousWaitingBound] at waitingLookup
  have middleWaitingLookup :
      step.prepared.stackResult.after.waiting[boundary]? =
        some (.initialized payload) := by
    rw [step.after_waiting_eq,
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
      |>.payload_boundary_lt_previous middlePartition
        step.middle_sigma_eq step.waiting_empty boundaryBound
        middleWaitingLookup conclusionMembership
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
      sigmaBoundary? after.stack.sigma olderAge = some boundary := by
    rw [step.after_sigma_eq]
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
    · rw [step.core_marks_eq]
      exact conclusionUnmarked
    · rw [step.core_marks_eq]
      exact olderMarked
    · rw [step.core_marks_eq]
      exact youngerMarked
    · rw [step.after_sigma_eq]
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
    · rw [step.core_marks_eq]
      exact conclusionUnmarked
    · rw [step.core_marks_eq]
      exact olderMarked
    · rw [step.core_marks_eq]
      exact youngerMarked
    · rw [step.after_sigma_eq]
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

private theorem foldl_add_weight_eq
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

private theorem map_sum_set_balance
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

private theorem map_sum_set_merge_clear
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
  have first := map_sum_set_balance weight survivorLookup
    (newValue := mergedValue)
  have second := map_sum_set_balance weight retiredAfter
    (newValue := clearedValue)
  rw [clearedWeight] at second
  omega

private theorem firedCounterExact
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyEmptyStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    FiredCounterExact after := by
  let weight : Option UnificationComponent → Nat := fun cell =>
    (cell.map UnificationComponent.connectiveCount).getD 0
  let values := step.prepared.coreMarked.components.toList
  have middleInvariant := step.prepared.schedulerInvariant invariant
  have leftLookup :
      values[step.queueStep.leftToken]? =
        some (some step.queueStep.leftComponent) := by
    simpa [values] using step.left_component_raw invariant
  have rightLookup :
      values[step.queueStep.rightToken]? =
        some (some step.queueStep.rightComponent) := by
    simpa [values] using step.right_component_raw invariant
  have sumIncrease :
      (((values.set step.previousBoundary
          (some step.mergedComponent)).set
          step.prepared.stackResult.rawAge none).map weight).sum =
        (values.map weight).sum + 1 := by
    rcases step.tokens_eq_adjacent with orientation | orientation
    · rw [orientation.2.1] at leftLookup
      rw [orientation.2.2] at rightLookup
      apply map_sum_set_merge_clear weight
        (Nat.ne_of_lt step.previous_lt_active)
        rightLookup leftLookup
      · simp [weight]
      · simp [weight, mergedComponent,
          UnificationComponent.connectiveCount,
          CutFreeDerivation.connectiveCount]
        omega
    · rw [orientation.2.1] at leftLookup
      rw [orientation.2.2] at rightLookup
      apply map_sum_set_merge_clear weight
        (Nat.ne_of_lt step.previous_lt_active)
        leftLookup rightLookup
      · simp [weight]
      · simp [weight, mergedComponent,
          UnificationComponent.connectiveCount,
          CutFreeDerivation.connectiveCount]
  have totalIncrease :
      ((values.set step.previousBoundary
          (some step.mergedComponent)).set
          step.prepared.stackResult.rawAge none).foldl
          (fun total cell => total + weight cell) 0 =
        values.foldl
          (fun total cell => total + weight cell) 0 + 1 := by
    rw [foldl_add_weight_eq, foldl_add_weight_eq]
    simpa using sumIncrease
  have middleCounter := middleInvariant.fired_counter_exact
  unfold FiredCounterExact UnificationState.liveConnectiveCount at middleCounter
  change step.prepared.coreMarked.firedConnectives =
    step.prepared.coreMarked.components.toList.foldl
      (fun total cell => total +
        (cell.map UnificationComponent.connectiveCount).getD 0) 0
    at middleCounter
  unfold FiredCounterExact
  rw [step.after_core_eq, step.queueStep.after_eq,
    step.max_token_eq, step.min_token_eq]
  unfold UnificationState.liveConnectiveCount
  rw [Array.toList_setIfInBounds, Array.toList_setIfInBounds]
  change step.prepared.coreMarked.firedConnectives + 1 =
    ((values.set step.previousBoundary
      (some step.mergedComponent)).set
      step.prepared.stackResult.rawAge none).foldl
      (fun total cell => total + weight cell) 0
  rw [totalIncrease]
  exact congrArg (fun count => count + 1) middleCounter

/-- A successful bounded empty-waiting-cell tensor merge preserves every
field of the occurrence-exact state-only scheduler invariant.  This is a
preservation theorem for the local `unify` rule; it does not assert that the
rule is applicable, that the dispatcher progresses, or that nonempty waiting
payloads are handled. -/
theorem schedulerInvariant
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyEmptyStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    SchedulerInvariant certificate after := by
  exact {
    toReservationInvariant := step.reservationInvariant
    structural := invariant.structural
    component_domain_exact := step.componentDomainExact invariant
    component_forest_provenance :=
      step.componentForestProvenance invariant
    live_frontiers_nodup := step.liveFrontiersNodup invariant
    ready_bucket_frontier_exact :=
      step.readyBucketFrontierExact invariant
    queued_vertices_nodup := step.queuedVerticesNodup invariant
    queued_vertices_unmarked := step.queuedVerticesUnmarked invariant
    produced_premises_marked :=
      step.producedPremisesMarked invariant
    waiting_span_exact := step.waitingSpanExact invariant
    pending_premises_covered_except_ready :=
      step.pendingPremisesCoveredExceptReady invariant
    fired_counter_exact := step.firedCounterExact invariant }

end UnifyEmptyStep

/-- Executable bounded `unifyEmpty?` success preserves the complete current
scheduler invariant.  The theorem deliberately covers only the empty waiting
payload branch represented by `UnifyEmptyStep`. -/
theorem unifyEmpty?_schedulerInvariant
    {certificate : Certificate} {before after : ReservationState}
    (invariant : SchedulerInvariant certificate before)
    (equation :
      unifyEmpty? certificate before invariant.toReservationInvariant =
        some after) :
    SchedulerInvariant certificate after := by
  rcases
      (unifyEmpty?_some_iff invariant.toReservationInvariant).mp equation with
    ⟨step⟩
  exact step.schedulerInvariant invariant

namespace UnifyOneStep

private theorem tensor_wellFormed
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyOneStep certificate before after) :
    certificate.LinkWellFormed
      (.tensor step.consumer.storedLeft step.consumer.storedRight
        step.consumer.conclusion) :=
  Certificate.tensorBelow?_wellFormed step.consumer_eq

private theorem selected_eq_premise
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyOneStep certificate before after) :
    step.prepared.stackResult.vertex =
      step.consumer.side.premise step.consumer.storedLeft
        step.consumer.storedRight := by
  change step.prepared.stackResult.vertex = step.consumer.premise
  exact Certificate.tensorBelow?_premise step.consumer_eq

private theorem premise_orientation
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyOneStep certificate before after) :
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
    (step : UnifyOneStep certificate before after) :
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
    (step : UnifyOneStep certificate before after)
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
    (step : UnifyOneStep certificate before after)
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
    (step : UnifyOneStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    step.consumer.conclusion ∉ before.stack.waitingVertices := by
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
    (step : UnifyOneStep certificate before after)
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
    (step : UnifyOneStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    step.consumer.conclusion ∉
      step.prepared.after.stack.queuedVertices := by
  intro queued
  unfold SequentialStackState.queuedVertices at queued
  rcases List.mem_append.mp queued with ready | waiting
  · exact step.conclusion_not_produced_middle invariant
      (Or.inr
        (SchedulerInvariant.ready_mem_liveFrontier
          (step.prepared.schedulerInvariant invariant) ready))
  · exact step.conclusion_not_mem_waiting_middle invariant waiting

private theorem activeBoundary_eq
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyOneStep certificate before after) :
    step.mergeStep.activeBoundary =
      step.prepared.stackResult.rawAge := by
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

private theorem middle_sigma_eq
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyOneStep certificate before after) :
    step.prepared.stackResult.after.sigma =
      step.mergeStep.sigmaPrefix ++
        [step.previousBoundary, step.prepared.stackResult.rawAge] := by
  simpa [step.activeBoundary_eq] using step.mergeStep.sigma_eq

private theorem previous_lt_active
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyOneStep certificate before after) :
    step.previousBoundary < step.prepared.stackResult.rawAge :=
  Nat.lt_of_le_of_lt step.lower step.upper

private theorem min_token_eq
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyOneStep certificate before after) :
    min step.tensorStep.leftToken step.tensorStep.rightToken =
      step.previousBoundary := by
  rcases step.tokens_eq_adjacent with orientation | orientation
  · rw [orientation.2.1, orientation.2.2]
    exact Nat.min_eq_right (Nat.le_of_lt step.previous_lt_active)
  · rw [orientation.2.1, orientation.2.2]
    exact Nat.min_eq_left (Nat.le_of_lt step.previous_lt_active)

private theorem max_token_eq
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyOneStep certificate before after) :
    max step.tensorStep.leftToken step.tensorStep.rightToken =
      step.prepared.stackResult.rawAge := by
  rcases step.tokens_eq_adjacent with orientation | orientation
  · rw [orientation.2.1, orientation.2.2]
    exact Nat.max_eq_left (Nat.le_of_lt step.previous_lt_active)
  · rw [orientation.2.1, orientation.2.2]
    exact Nat.max_eq_right (Nat.le_of_lt step.previous_lt_active)

private def tensorComponent
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyOneStep certificate before after) :
    UnificationComponent := {
  tree := .tensor step.tensorStep.leftFocus step.tensorStep.rightFocus
    step.tensorStep.leftComponent.tree step.tensorStep.rightComponent.tree
  frontier := step.consumer.conclusion ::
    (step.tensorStep.leftContext ++ step.tensorStep.rightContext) }

private def activatedComponent
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyOneStep certificate before after) :
    UnificationComponent := {
  tree := .par step.activationStep.queueStep.leftFocus
    step.activationStep.queueStep.rightFocus
    step.activationStep.queueStep.component.tree
  frontier := step.activationStep.queueStep.context ++
    [step.waitingConclusion] }

private theorem payload_eq_singleton
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyOneStep certificate before after) :
    step.mergeStep.payload = [step.waitingConclusion] := by
  exact WaitingCell.initialized.inj
    (Option.some.inj
      (step.mergeStep.waiting_initialized.symm.trans step.waiting_one))

private theorem after_core_eq
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyOneStep certificate before after) :
    after.core = step.coreAfter :=
  congrArg (fun state : ReservationState => state.core) step.output_eq

private theorem after_stack_eq
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyOneStep certificate before after) :
    after.stack = step.stackAfter :=
  congrArg (fun state : ReservationState => state.stack) step.output_eq

private theorem core_marks_eq
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyOneStep certificate before after) :
    after.core.marks = step.prepared.coreMarked.marks := by
  calc
    after.core.marks = step.coreAfter.marks :=
      congrArg (fun core : UnificationState => core.marks)
        step.after_core_eq
    _ = step.coreTensor.marks := step.activationStep.exact.2.1
    _ = step.prepared.coreMarked.marks := by
      rw [step.tensorStep.after_eq]

private theorem core_parents_eq
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyOneStep certificate before after) :
    after.core.parents =
      step.prepared.coreMarked.parents.setIfInBounds
        step.prepared.stackResult.rawAge step.previousBoundary := by
  calc
    after.core.parents = step.coreAfter.parents :=
      congrArg (fun core : UnificationState => core.parents)
        step.after_core_eq
    _ = step.coreTensor.parents := step.activationStep.exact.2.2.1
    _ = step.prepared.coreMarked.parents.setIfInBounds
          step.prepared.stackResult.rawAge step.previousBoundary := by
      rw [step.tensorStep.after_eq, step.max_token_eq, step.min_token_eq]

private theorem tensor_components_eq
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyOneStep certificate before after) :
    step.coreTensor.components =
      ((step.prepared.coreMarked.components.setIfInBounds
          step.previousBoundary (some step.tensorComponent))
        |>.setIfInBounds step.prepared.stackResult.rawAge none) := by
  rw [step.tensorStep.after_eq, step.min_token_eq, step.max_token_eq]
  rfl

private theorem core_components_eq
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyOneStep certificate before after) :
    after.core.components =
      step.coreTensor.components.setIfInBounds
        step.activationStep.queueStep.outputToken
        (some step.activatedComponent) := by
  calc
    after.core.components = step.coreAfter.components :=
      congrArg (fun core : UnificationState => core.components)
        step.after_core_eq
    _ = step.coreTensor.components.setIfInBounds
          step.activationStep.queueStep.outputToken
          (some step.activatedComponent) := step.activationStep.exact.1

private theorem after_sigma_eq
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyOneStep certificate before after) :
    after.stack.sigma =
      step.mergeStep.sigmaPrefix ++ [step.previousBoundary] := by
  calc
    after.stack.sigma = step.stackAfter.sigma :=
      congrArg (fun state : SequentialStackState => state.sigma)
        step.after_stack_eq
    _ = step.mergeStep.sigmaPrefix ++ [step.previousBoundary] := by
      simpa using congrArg
        (fun state : SequentialStackState => state.sigma)
        step.mergeStep.after_eq

private theorem after_ready_eq
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyOneStep certificate before after) :
    after.stack.ready =
      step.mergeStep.readyPrefix ++
        [step.consumer.conclusion ::
          (step.waitingConclusion :: step.mergeStep.previousReady ++
            step.mergeStep.activeReady)] := by
  calc
    after.stack.ready = step.stackAfter.ready :=
      congrArg (fun state : SequentialStackState => state.ready)
        step.after_stack_eq
    _ = step.mergeStep.readyPrefix ++
          [step.consumer.conclusion ::
            (step.waitingConclusion :: step.mergeStep.previousReady ++
              step.mergeStep.activeReady)] := by
      simpa [step.payload_eq_singleton] using congrArg
        (fun state : SequentialStackState => state.ready)
        step.mergeStep.after_eq

private theorem after_waiting_eq
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyOneStep certificate before after) :
    after.stack.waiting =
      step.prepared.stackResult.after.waiting.setIfInBounds
        step.previousBoundary .undefined := by
  calc
    after.stack.waiting = step.stackAfter.waiting :=
      congrArg (fun state : SequentialStackState => state.waiting)
        step.after_stack_eq
    _ = step.prepared.stackResult.after.waiting.setIfInBounds
          step.previousBoundary .undefined := by
      simpa using congrArg
        (fun state : SequentialStackState => state.waiting)
        step.mergeStep.after_eq

private theorem left_root
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyOneStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    step.prepared.coreMarked.representative step.tensorStep.leftToken =
      step.tensorStep.leftToken := by
  have middleInvariant := step.prepared.schedulerInvariant invariant
  exact middleInvariant.core_abstractable.tokenAt?_root
    (UnificationState.unifyTokens?_success
      step.tensorStep.token_guard).2.1

private theorem right_root
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyOneStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    step.prepared.coreMarked.representative step.tensorStep.rightToken =
      step.tensorStep.rightToken := by
  have middleInvariant := step.prepared.schedulerInvariant invariant
  exact middleInvariant.core_abstractable.tokenAt?_root
    (UnificationState.unifyTokens?_success
      step.tensorStep.token_guard).2.2.1

private theorem left_component_raw
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyOneStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    step.prepared.coreMarked.components[step.tensorStep.leftToken]? =
      some (some step.tensorStep.leftComponent) := by
  have raw := UnificationState.componentAt?_some_raw
    step.tensorStep.left_component
  simpa [step.left_root invariant] using raw

private theorem right_component_raw
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyOneStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    step.prepared.coreMarked.components[step.tensorStep.rightToken]? =
      some (some step.tensorStep.rightComponent) := by
  have raw := UnificationState.componentAt?_some_raw
    step.tensorStep.right_component
  simpa [step.right_root invariant] using raw

private theorem previous_bound
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyOneStep certificate before after)
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
    (step : UnifyOneStep certificate before after)
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

private theorem activation_tokenAt_eq
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyOneStep certificate before after) (vertex : Vertex) :
    step.coreAfter.tokenAt? vertex = step.coreTensor.tokenAt? vertex := by
  have exact := step.activationStep.exact
  unfold UnificationState.tokenAt?
  rw [exact.2.1]
  cases step.coreTensor.marks[vertex]? with
  | none => rfl
  | some assigned =>
      cases assigned with
      | none => rfl
      | some rawAge =>
          change some (step.coreAfter.representative rawAge) =
            some (step.coreTensor.representative rawAge)
          unfold UnificationState.representative
          rw [exact.2.2.1]

private theorem waiting_premise_token_after
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyOneStep certificate before after)
    (invariant : SchedulerInvariant certificate before)
    {premise : Vertex}
    (membership : premise ∈
      [step.activationStep.producer.storedLeft,
        step.activationStep.producer.storedRight]) :
    after.core.tokenAt? premise = some step.previousBoundary := by
  have middleInvariant := step.prepared.schedulerInvariant invariant
  rcases middleInvariant.waiting_span_exact
      (boundary := step.previousBoundary)
      (payload := [step.waitingConclusion])
      (conclusion := step.waitingConclusion)
      step.waiting_one (by simp) with
    ⟨linkIndex, left, right, olderPremise, youngerPremise,
      olderAge, youngerAge, youngerBoundary, linkLookup,
      sourceLookup, conclusionUnmarked, orientation,
      olderMarked, youngerMarked, olderBoundary,
      youngerBoundaryLookup, boundaryOrder⟩
  have incidenceEq := Option.some.inj
    (sourceLookup.symm.trans step.activationStep.producer.source_eq)
  have singletonEq := List.singleton_inj.mp incidenceEq
  have linkEq := congrArg
    SequentialUnification.SourceIncidence.link singletonEq
  injection linkEq with leftEq rightEq
  subst left
  subst right
  have markedAndLower : ∃ rawAge,
      step.prepared.coreMarked.marks[premise]? = some (some rawAge) ∧
        step.previousBoundary ≤ rawAge := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
    rcases orientation with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases membership with rfl | rfl
      · exact ⟨olderAge, olderMarked,
          sigmaBoundary?_le olderBoundary⟩
      · exact ⟨youngerAge, youngerMarked,
          Nat.le_trans (Nat.le_of_lt boundaryOrder)
            (sigmaBoundary?_le youngerBoundaryLookup)⟩
    · rcases membership with rfl | rfl
      · exact ⟨youngerAge, youngerMarked,
          Nat.le_trans (Nat.le_of_lt boundaryOrder)
            (sigmaBoundary?_le youngerBoundaryLookup)⟩
      · exact ⟨olderAge, olderMarked,
          sigmaBoundary?_le olderBoundary⟩
  rcases markedAndLower with ⟨rawAge, marked, lower⟩
  have finalInvariant := step.reservationInvariant
  have finalMark : after.core.marks[premise]? = some (some rawAge) := by
    rw [step.core_marks_eq]
    exact marked
  have stackMark : after.stack.marks[premise]? = some (some rawAge) := by
    rw [← finalInvariant.realizesSigma.marks_eq]
    exact finalMark
  have rawBound : rawAge < after.stack.nextAge :=
    finalInvariant.stack_wellShaped.assigned_age_bound
      premise rawAge stackMark
  have top : after.stack.sigma.getLast? = some step.previousBoundary := by
    rw [step.after_sigma_eq]
    simp
  have boundaryLookup :
      sigmaBoundary? after.stack.sigma rawAge =
        some step.previousBoundary :=
    finalInvariant.stack_wellShaped.sigma_partition
      |>.sigmaBoundary?_eq_top_of_le top lower rawBound
  have realized :=
    finalInvariant.realizesSigma.representative_eq_boundary rawBound
  unfold UnificationState.tokenAt?
  rw [finalMark]
  exact congrArg some (Option.some.inj (realized.symm.trans boundaryLookup))

private theorem activation_output_eq_previous
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyOneStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    step.activationStep.queueStep.outputToken =
      step.previousBoundary := by
  have tokenGuard :=
    (UnificationState.forwardToken?_success
      step.activationStep.queueStep.token_guard).2.1
  have afterToken :
      after.core.tokenAt? step.activationStep.producer.storedLeft =
        some step.activationStep.queueStep.outputToken := by
    rw [step.after_core_eq, step.activation_tokenAt_eq]
    exact tokenGuard
  have previousToken := step.waiting_premise_token_after invariant
    (premise := step.activationStep.producer.storedLeft) (by simp)
  exact Option.some.inj (afterToken.symm.trans previousToken)

private theorem core_components_expanded_eq
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyOneStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    after.core.components =
      (((step.prepared.coreMarked.components.setIfInBounds
          step.previousBoundary (some step.tensorComponent))
        |>.setIfInBounds step.prepared.stackResult.rawAge none)
        |>.setIfInBounds step.previousBoundary
          (some step.activatedComponent)) := by
  calc
    after.core.components =
        step.coreTensor.components.setIfInBounds
          step.activationStep.queueStep.outputToken
          (some step.activatedComponent) := step.core_components_eq
    _ = step.coreTensor.components.setIfInBounds
          step.previousBoundary (some step.activatedComponent) := by
      rw [step.activation_output_eq_previous invariant]
    _ =
        (((step.prepared.coreMarked.components.setIfInBounds
            step.previousBoundary (some step.tensorComponent))
          |>.setIfInBounds step.prepared.stackResult.rawAge none)
          |>.setIfInBounds step.previousBoundary
            (some step.activatedComponent)) := by
      rw [step.tensor_components_eq]

private theorem componentDomainExact
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyOneStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    ComponentDomainExact after := by
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
  rw [step.core_components_expanded_eq invariant, step.after_sigma_eq]
  by_cases previous : token = step.previousBoundary
  · subst token
    constructor
    · intro _
      simp
    · intro _
      refine ⟨step.activatedComponent, ?_⟩
      rw [Array.getElem?_setIfInBounds]
      simp [step.previous_bound invariant]
  · by_cases active : token = step.prepared.stackResult.rawAge
    · subst token
      rw [Array.getElem?_setIfInBounds_ne
        (Nat.ne_of_lt step.previous_lt_active)]
      simp [step.active_bound invariant, activeNotReduced]
    · have oldDomain :
        (∃ component,
          step.prepared.coreMarked.components[token]? =
            some (some component)) ↔
          token ∈ step.prepared.stackResult.after.sigma := by
        simpa [PreparedStep.after] using
          middleInvariant.component_domain_exact token
      rw [step.middle_sigma_eq] at oldDomain
      rw [Array.getElem?_setIfInBounds_ne (Ne.symm previous),
        Array.getElem?_setIfInBounds_ne (Ne.symm active),
        Array.getElem?_setIfInBounds_ne (Ne.symm previous)]
      simpa [active] using oldDomain

private theorem queuedVerticesNodup
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyOneStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    QueuedVerticesNodup after := by
  have middleInvariant := step.prepared.schedulerInvariant invariant
  have targetNodup :
      (step.consumer.conclusion ::
        step.prepared.after.stack.queuedVertices).Nodup :=
    List.nodup_cons.mpr
      ⟨step.conclusion_not_queued_middle invariant,
        middleInvariant.queued_vertices_nodup⟩
  have stackEq : after.stack = step.stackAfter := step.after_stack_eq
  unfold QueuedVerticesNodup
  rw [stackEq]
  exact step.mergeStep.queuedVertices_perm.symm.nodup targetNodup

private theorem queuedVerticesUnmarked
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyOneStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    QueuedVerticesUnmarked after := by
  have middleInvariant := step.prepared.schedulerInvariant invariant
  intro vertex membership
  have stackEq : after.stack = step.stackAfter := step.after_stack_eq
  have targetMembership :=
    step.mergeStep.queuedVertices_perm.mem_iff.mp (by
      simpa [stackEq] using membership)
  simp only [List.mem_cons] at targetMembership
  rw [step.core_marks_eq]
  rcases targetMembership with rfl | oldMembership
  · exact (UnificationState.unifyTokens?_success
      step.tensorStep.token_guard).1
  · exact middleInvariant.queued_vertices_unmarked vertex oldMembership

private theorem waitingConclusion_unmarked_middle
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyOneStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    step.prepared.coreMarked.marks[step.waitingConclusion]? = some none := by
  have middleInvariant := step.prepared.schedulerInvariant invariant
  rcases middleInvariant.waiting_span_exact
      (boundary := step.previousBoundary)
      (payload := [step.waitingConclusion])
      (conclusion := step.waitingConclusion)
      step.waiting_one (by simp) with
    ⟨_, _, _, _, _, _, _, _, _, _, unmarked, _⟩
  exact unmarked

private theorem waitingConclusion_mem_waiting_middle
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyOneStep certificate before after) :
    step.waitingConclusion ∈
      step.prepared.after.stack.waitingVertices := by
  unfold SequentialStackState.waitingVertices
  apply List.mem_flatMap.mpr
  refine ⟨.initialized [step.waitingConclusion], ?_, by simp
    [WaitingCell.vertices]⟩
  apply List.mem_of_getElem?
  change step.prepared.stackResult.after.waiting.toList[_]? =
    some (WaitingCell.initialized [step.waitingConclusion])
  rw [Array.getElem?_toList]
  exact step.waiting_one

private theorem waitingConclusion_not_mem_ready_middle
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyOneStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    step.waitingConclusion ∉
      step.prepared.after.stack.ready.flatten := by
  have middleInvariant := step.prepared.schedulerInvariant invariant
  have parts := List.nodup_append.mp
    middleInvariant.queued_vertices_nodup
  intro readyMembership
  exact parts.2.2 step.waitingConclusion readyMembership
    step.waitingConclusion step.waitingConclusion_mem_waiting_middle rfl

private theorem waitingConclusion_not_produced_middle
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyOneStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    ¬ Produced step.prepared.after step.waitingConclusion := by
  intro produced
  rcases produced with ⟨rawAge, marked⟩ | frontier
  · have unmarked := step.waitingConclusion_unmarked_middle invariant
    change step.prepared.coreMarked.marks[step.waitingConclusion]? =
      some none at unmarked
    change step.prepared.coreMarked.marks[step.waitingConclusion]? =
      some (some rawAge) at marked
    rw [unmarked] at marked
    simp at marked
  · have middleInvariant := step.prepared.schedulerInvariant invariant
    have readyMembership : step.waitingConclusion ∈
        step.prepared.after.stack.ready.flatten := by
      unfold UnificationState.liveFrontierVertices at frontier
      rcases List.mem_flatMap.mp frontier with
        ⟨cell, cellMembership, vertexMembership⟩
      cases cell with
      | none => simp at vertexMembership
      | some component =>
          simp only [Option.map_some, Option.getD_some] at vertexMembership
          rcases List.mem_iff_getElem.mp cellMembership with
            ⟨index, indexBound, indexEquation⟩
          have componentLookup :
              step.prepared.after.core.components[index]? =
                some (some component) := by
            rw [← Array.getElem?_toList]
            rw [List.getElem?_eq_getElem indexBound, indexEquation]
          have boundaryMembership :
              index ∈ step.prepared.after.stack.sigma :=
            (middleInvariant.component_domain_exact index).mp
              ⟨component, componentLookup⟩
          rcases List.mem_iff_getElem.mp boundaryMembership with
            ⟨position, positionBound, positionEquation⟩
          have sigmaLookup :
              step.prepared.after.stack.sigma[position]? = some index := by
            rw [List.getElem?_eq_getElem positionBound, positionEquation]
          have readyBound :
              position < step.prepared.after.stack.ready.length := by
            rw [middleInvariant.stack_wellShaped.ready_aligned]
            exact positionBound
          let bucket := step.prepared.after.stack.ready[position]
          have readyLookup :
              step.prepared.after.stack.ready[position]? = some bucket :=
            List.getElem?_eq_getElem readyBound
          rcases middleInvariant.ready_bucket_frontier_exact
              sigmaLookup readyLookup with
            ⟨actual, actualLookup, exactMembership⟩
          have actualEq : actual = component :=
            Option.some.inj
              (Option.some.inj (actualLookup.symm.trans componentLookup))
          subst actual
          apply List.mem_flatten.mpr
          exact ⟨bucket, List.mem_of_getElem? readyLookup,
            (exactMembership step.waitingConclusion).mpr
              ⟨vertexMembership,
                step.waitingConclusion_unmarked_middle invariant⟩⟩
    exact step.waitingConclusion_not_mem_ready_middle invariant
      readyMembership

private theorem activation_root
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyOneStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    step.coreTensor.representative
        step.activationStep.queueStep.outputToken =
      step.activationStep.queueStep.outputToken := by
  have middleInvariant := step.prepared.schedulerInvariant invariant
  have middleOrdered : step.prepared.coreMarked.OrderedParents := by
    intro token parent lookup
    exact middleInvariant.core_orderedParents lookup
  have tensorAbstractable : step.coreTensor.Abstractable certificate :=
    Certificate.queueTensor?_abstractable
      middleInvariant.core_abstractable middleOrdered step.tensor_queue_eq
  exact tensorAbstractable.tokenAt?_root
    (UnificationState.forwardToken?_success
      step.activationStep.queueStep.token_guard).2.1

private theorem activation_component_eq_tensor
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyOneStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    step.activationStep.queueStep.component = step.tensorComponent := by
  have rawLookup := UnificationState.componentAt?_some_raw
    step.activationStep.queueStep.component_lookup
  rw [step.activation_root invariant,
    step.activation_output_eq_previous invariant,
    step.tensor_components_eq] at rawLookup
  rw [Array.getElem?_setIfInBounds_ne
    (Nat.ne_of_gt step.previous_lt_active)] at rawLookup
  simp [step.previous_bound invariant] at rawLookup
  exact rawLookup.symm

private theorem tensor_produced_cases
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyOneStep certificate before after)
    (invariant : SchedulerInvariant certificate before)
    {vertex : Vertex}
    (produced :
      (∃ rawAge,
        step.coreTensor.marks[vertex]? = some (some rawAge)) ∨
      vertex ∈ step.coreTensor.liveFrontierVertices) :
    vertex = step.consumer.conclusion ∨
      Produced step.prepared.after vertex := by
  rcases produced with ⟨rawAge, marked⟩ | frontierMembership
  · apply Or.inr
    apply Or.inl
    refine ⟨rawAge, ?_⟩
    rw [step.tensorStep.after_eq] at marked
    exact marked
  · unfold UnificationState.liveFrontierVertices at frontierMembership
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
        · by_cases active :
              index = step.prepared.stackResult.rawAge
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

private theorem waitingConclusion_ne_tensorConclusion
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyOneStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    step.waitingConclusion ≠ step.consumer.conclusion := by
  intro same
  have parMembership :
      (.par step.activationStep.producer.storedLeft
        step.activationStep.producer.storedRight
        step.waitingConclusion : Link) ∈ certificate.links :=
    List.mem_of_getElem? step.submitted_waiting_par
  have tensorMembership :
      (.tensor step.consumer.storedLeft step.consumer.storedRight
        step.consumer.conclusion : Link) ∈ certificate.links :=
    List.mem_of_getElem? step.submitted_tensor
  have impossible :=
    UnificationState.StructurallyWellFormed.producerLink_unique
      invariant.structural
      (conclusion := step.waitingConclusion)
      parMembership (by simp [Link.produces])
      tensorMembership (by simp [same, Link.produces])
  cases impossible

private theorem waitingConclusion_not_produced_tensor
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyOneStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    ¬ ((∃ rawAge,
        step.coreTensor.marks[step.waitingConclusion]? =
          some (some rawAge)) ∨
      step.waitingConclusion ∈ step.coreTensor.liveFrontierVertices) := by
  intro produced
  rcases step.tensor_produced_cases invariant produced with
    same | producedMiddle
  · exact step.waitingConclusion_ne_tensorConclusion invariant same
  · exact step.waitingConclusion_not_produced_middle invariant
      producedMiddle

private theorem componentForestProvenance
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyOneStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    certificate.ComponentForestProvenance after.core := by
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
  have tensorForest :
      certificate.ComponentForestProvenance step.coreTensor :=
    middleInvariant.component_forest_provenance
      |>.queueTensorStep_of_roots_fresh
        middleInvariant.core_abstractable
        middleInvariant.core_orderedParents step.tensorStep
        step.consumer.linkIndex step.submitted_tensor tensorConclusionFresh
  have waitingFresh :
      ∀ {index component owned},
        step.coreTensor.components[index]? = some (some component) →
        Certificate.OwnedOccurrenceAccounted
            step.coreTensor index component owned →
        step.waitingConclusion ∉ owned := by
    intro index component owned componentLookup accounted conclusionOwned
    apply step.waitingConclusion_not_produced_tensor invariant
    rcases accounted step.waitingConclusion conclusionOwned with
      ⟨rawAge, marked, _⟩ | ⟨unmarked, frontier⟩
    · exact Or.inl ⟨rawAge, marked⟩
    · apply Or.inr
      unfold UnificationState.liveFrontierVertices
      apply List.mem_flatMap.mpr
      exact ⟨some component, List.mem_of_getElem? (by
          rw [Array.getElem?_toList]
          exact componentLookup),
        by simpa using frontier⟩
  have finalForest := tensorForest.queueParStep_of_root_fresh
    step.activationStep.queueStep (step.activation_root invariant)
    step.activationStep.producer.linkIndex
    step.submitted_waiting_par waitingFresh
  rw [step.after_core_eq]
  exact finalForest

private theorem liveFrontiersNodup
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyOneStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    LiveFrontiersNodup after := by
  unfold LiveFrontiersNodup
  simpa [UnificationState.liveFrontierVertices] using
    (step.componentForestProvenance invariant).liveFrontiers_nodup

private theorem tensorTopUnmarkedExact
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyOneStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    ∀ vertex,
      vertex ∈ step.consumer.conclusion ::
          (step.mergeStep.previousReady ++ step.mergeStep.activeReady) ↔
        vertex ∈ step.tensorComponent.frontier ∧
          step.coreTensor.marks[vertex]? = some none := by
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
  intro vertex
  rw [step.tensorStep.after_eq]
  rcases step.tokens_eq_adjacent with orientation | orientation
  · have rightRaw := step.right_component_raw invariant
    have leftRaw := step.left_component_raw invariant
    rw [orientation.2.2] at rightRaw
    rw [orientation.2.1] at leftRaw
    have previousComponentEq :
        previousComponent = step.tensorStep.rightComponent :=
      Option.some.inj
        (Option.some.inj (previousComponentLookup.symm.trans rightRaw))
    have activeComponentEq :
        activeComponent = step.tensorStep.leftComponent :=
      Option.some.inj
        (Option.some.inj (activeComponentLookup.symm.trans leftRaw))
    subst previousComponent
    subst activeComponent
    change vertex ∈ step.consumer.conclusion ::
        (step.mergeStep.previousReady ++ step.mergeStep.activeReady) ↔
      vertex ∈ step.consumer.conclusion ::
          (step.tensorStep.leftContext ++ step.tensorStep.rightContext) ∧
        step.prepared.coreMarked.marks[vertex]? = some none
    constructor
    · intro membership
      simp only [List.mem_cons, List.mem_append] at membership ⊢
      rcases membership with rfl | inPrevious | inActive
      · exact ⟨Or.inl rfl, tokenGuards.1⟩
      · have facts := (previousExact vertex).mp inPrevious
        exact ⟨Or.inr (Or.inr
          (right_context_of_frontier_unmarked facts.1 facts.2)), facts.2⟩
      · have facts := (activeExact vertex).mp inActive
        exact ⟨Or.inr (Or.inl
          (left_context_of_frontier_unmarked facts.1 facts.2)), facts.2⟩
    · rintro ⟨frontier, unmarked⟩
      simp only [List.mem_cons, List.mem_append] at frontier ⊢
      rcases frontier with rfl | inLeft | inRight
      · exact Or.inl rfl
      · exact Or.inr (Or.inr ((activeExact vertex).mpr
          ⟨left_frontier_of_context inLeft, unmarked⟩))
      · exact Or.inr (Or.inl ((previousExact vertex).mpr
          ⟨right_frontier_of_context inRight, unmarked⟩))
  · have leftRaw := step.left_component_raw invariant
    have rightRaw := step.right_component_raw invariant
    rw [orientation.2.1] at leftRaw
    rw [orientation.2.2] at rightRaw
    have previousComponentEq :
        previousComponent = step.tensorStep.leftComponent :=
      Option.some.inj
        (Option.some.inj (previousComponentLookup.symm.trans leftRaw))
    have activeComponentEq :
        activeComponent = step.tensorStep.rightComponent :=
      Option.some.inj
        (Option.some.inj (activeComponentLookup.symm.trans rightRaw))
    subst previousComponent
    subst activeComponent
    change vertex ∈ step.consumer.conclusion ::
        (step.mergeStep.previousReady ++ step.mergeStep.activeReady) ↔
      vertex ∈ step.consumer.conclusion ::
          (step.tensorStep.leftContext ++ step.tensorStep.rightContext) ∧
        step.prepared.coreMarked.marks[vertex]? = some none
    constructor
    · intro membership
      simp only [List.mem_cons, List.mem_append] at membership ⊢
      rcases membership with rfl | inPrevious | inActive
      · exact ⟨Or.inl rfl, tokenGuards.1⟩
      · have facts := (previousExact vertex).mp inPrevious
        exact ⟨Or.inr (Or.inl
          (left_context_of_frontier_unmarked facts.1 facts.2)), facts.2⟩
      · have facts := (activeExact vertex).mp inActive
        exact ⟨Or.inr (Or.inr
          (right_context_of_frontier_unmarked facts.1 facts.2)), facts.2⟩
    · rintro ⟨frontier, unmarked⟩
      simp only [List.mem_cons, List.mem_append] at frontier ⊢
      rcases frontier with rfl | inLeft | inRight
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ((previousExact vertex).mpr
          ⟨left_frontier_of_context inLeft, unmarked⟩))
      · exact Or.inr (Or.inr ((activeExact vertex).mpr
          ⟨right_frontier_of_context inRight, unmarked⟩))

private theorem readyBucketFrontierExact
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyOneStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    ReadyBucketFrontierExact after := by
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
  have activationComponentEq := step.activation_component_eq_tensor invariant
  have activationGuards :=
    UnificationState.forwardToken?_success
      step.activationStep.queueStep.token_guard
  have context_of_frontier_unmarked :
      ∀ {vertex},
        vertex ∈ step.tensorComponent.frontier →
        step.coreTensor.marks[vertex]? = some none →
        vertex ∈ step.activationStep.queueStep.context := by
    intro vertex frontier unmarked
    have vertexNeLeft :
        vertex ≠ step.activationStep.producer.storedLeft := by
      intro same
      subst vertex
      unfold UnificationState.tokenAt? at activationGuards
      rw [unmarked] at activationGuards
      simp at activationGuards
    have vertexNeRight :
        vertex ≠ step.activationStep.producer.storedRight := by
      intro same
      subst vertex
      unfold UnificationState.tokenAt? at activationGuards
      rw [unmarked] at activationGuards
      simp at activationGuards
    rw [← activationComponentEq] at frontier
    have afterLeft :=
      Certificate.FirstOccurrencePick.mem_remaining_of_ne
        step.activationStep.queueStep.left_pick vertexNeLeft frontier
    exact Certificate.FirstOccurrencePick.mem_remaining_of_ne
      step.activationStep.queueStep.right_pick vertexNeRight afterLeft
  have frontier_of_context :
      ∀ {vertex}, vertex ∈ step.activationStep.queueStep.context →
        vertex ∈ step.tensorComponent.frontier := by
    intro vertex contextMembership
    have afterLeft :
        vertex ∈ step.activationStep.queueStep.afterLeft :=
      (CutFreeDerivation.pick?_perm
        step.activationStep.queueStep.right_pick.positional).mem_iff.mpr
          (by simp [contextMembership])
    have oldFrontier :
        vertex ∈ step.activationStep.queueStep.component.frontier :=
      (CutFreeDerivation.pick?_perm
        step.activationStep.queueStep.left_pick.positional).mem_iff.mpr
          (by simp [afterLeft])
    simpa [activationComponentEq] using oldFrontier
  have finalMarksTensor : after.core.marks = step.coreTensor.marks := by
    calc
      after.core.marks = step.coreAfter.marks :=
        congrArg (fun core : UnificationState => core.marks)
          step.after_core_eq
      _ = step.coreTensor.marks := step.activationStep.exact.2.1
  unfold ReadyBucketFrontierExact
  intro position boundary bucket sigmaLookup readyLookup
  rw [step.after_sigma_eq] at sigmaLookup
  rw [step.after_ready_eq] at readyLookup
  have positionBound :
      position <
        (step.mergeStep.readyPrefix ++
          [step.consumer.conclusion ::
            (step.waitingConclusion :: step.mergeStep.previousReady ++
              step.mergeStep.activeReady)]).length :=
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
    · rw [step.core_components_expanded_eq invariant,
        Array.getElem?_setIfInBounds_ne previousNeBoundary,
        Array.getElem?_setIfInBounds_ne activeNeBoundary,
        Array.getElem?_setIfInBounds_ne previousNeBoundary]
      exact componentLookup
    · intro vertex
      rw [step.core_marks_eq]
      exact exactMembership vertex
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
          (step.waitingConclusion :: step.mergeStep.previousReady ++
            step.mergeStep.activeReady) := by
      simp at readyLookup
      exact readyLookup.symm
    subst boundary
    subst bucket
    refine ⟨step.activatedComponent, ?_, ?_⟩
    · rw [step.core_components_expanded_eq invariant]
      simp [step.previous_bound invariant]
    · intro vertex
      rw [finalMarksTensor]
      constructor
      · intro bucketMembership
        simp only [List.mem_cons, List.mem_append] at bucketMembership
        rcases bucketMembership with tensorConclusion | rest
        · subst vertex
          have tensorFacts :=
            (step.tensorTopUnmarkedExact invariant
              step.consumer.conclusion).mp (by simp)
          exact ⟨by
            simp [activatedComponent,
              context_of_frontier_unmarked tensorFacts.1 tensorFacts.2],
            tensorFacts.2⟩
        · rcases rest with prior | inActive
          · rcases prior with waitingConclusion | inPrevious
            · subst vertex
              refine ⟨by simp [activatedComponent], ?_⟩
              rw [step.tensorStep.after_eq]
              exact step.waitingConclusion_unmarked_middle invariant
            · have tensorFacts :=
                (step.tensorTopUnmarkedExact invariant vertex).mp
                  (by simp [inPrevious])
              exact ⟨by
                simp [activatedComponent,
                  context_of_frontier_unmarked tensorFacts.1 tensorFacts.2],
                tensorFacts.2⟩
          · have tensorFacts :=
              (step.tensorTopUnmarkedExact invariant vertex).mp
                (by simp [inActive])
            exact ⟨by
              simp [activatedComponent,
                context_of_frontier_unmarked tensorFacts.1 tensorFacts.2],
              tensorFacts.2⟩
      · rintro ⟨newFrontier, unmarked⟩
        rw [show step.activatedComponent.frontier =
            step.activationStep.queueStep.context ++
              [step.waitingConclusion] by rfl] at newFrontier
        rw [List.mem_append] at newFrontier
        rcases newFrontier with contextMembership | waitingMembership
        · have tensorFacts :=
            (step.tensorTopUnmarkedExact invariant vertex).mpr
              ⟨frontier_of_context contextMembership, unmarked⟩
          simp only [List.mem_cons, List.mem_append] at tensorFacts ⊢
          rcases tensorFacts with rfl | inPrevious | inActive
          · exact Or.inl rfl
          · simp [inPrevious]
          · simp [inActive]
        · have same : vertex = step.waitingConclusion := by
            simpa using waitingMembership
          simp [same]

private theorem tensorPremisesMarkedAfter
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyOneStep certificate before after) :
    (∃ leftAge,
      after.core.marks[step.consumer.storedLeft]? =
        some (some leftAge)) ∧
      ∃ rightAge,
        after.core.marks[step.consumer.storedRight]? =
          some (some rightAge) := by
  have selectedMarked :
      step.prepared.coreMarked.marks[
          step.prepared.stackResult.vertex]? =
        some (some step.prepared.stackResult.rawAge) :=
    (UnificationState.markReadyRaw?_exact
      step.prepared.core_mark_eq).2.2.2.2.2.2
  rcases step.premise_orientation with
    ⟨mateEq, selectedEq⟩ | ⟨mateEq, selectedEq⟩
  · constructor
    · exact ⟨step.mateRawAge, by
        rw [step.core_marks_eq, ← mateEq]
        exact step.mate_marked⟩
    · exact ⟨step.prepared.stackResult.rawAge, by
        rw [step.core_marks_eq, ← selectedEq]
        exact selectedMarked⟩
  · constructor
    · exact ⟨step.prepared.stackResult.rawAge, by
        rw [step.core_marks_eq, ← selectedEq]
        exact selectedMarked⟩
    · exact ⟨step.mateRawAge, by
        rw [step.core_marks_eq, ← mateEq]
        exact step.mate_marked⟩

private theorem waitingPremisesMarkedAfter
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyOneStep certificate before after) :
    (∃ leftAge,
      after.core.marks[step.activationStep.producer.storedLeft]? =
        some (some leftAge)) ∧
      ∃ rightAge,
        after.core.marks[step.activationStep.producer.storedRight]? =
          some (some rightAge) := by
  have guards := UnificationState.forwardToken?_success
    step.activationStep.queueStep.token_guard
  have leftToken :
      after.core.tokenAt? step.activationStep.producer.storedLeft =
        some step.activationStep.queueStep.outputToken := by
    rw [step.after_core_eq, step.activation_tokenAt_eq]
    exact guards.2.1
  have rightToken :
      after.core.tokenAt? step.activationStep.producer.storedRight =
        some step.activationStep.queueStep.outputToken := by
    rw [step.after_core_eq, step.activation_tokenAt_eq]
    exact guards.2.2
  rcases after.core.tokenAt?_some_witness leftToken with
    ⟨leftAge, leftAssigned, leftRepresentative⟩
  rcases after.core.tokenAt?_some_witness rightToken with
    ⟨rightAge, rightAssigned, rightRepresentative⟩
  exact ⟨⟨leftAge,
      UnificationState.assignedToken?_some_raw leftAssigned⟩,
    rightAge, UnificationState.assignedToken?_some_raw rightAssigned⟩

private theorem produced_after_cases
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyOneStep certificate before after)
    (invariant : SchedulerInvariant certificate before)
    {vertex : Vertex}
    (produced : Produced after vertex) :
    vertex = step.waitingConclusion ∨
      vertex = step.consumer.conclusion ∨
        Produced step.prepared.after vertex := by
  rcases produced with ⟨rawAge, marked⟩ | frontierMembership
  · apply Or.inr
    apply Or.inr
    apply Or.inl
    refine ⟨rawAge, ?_⟩
    rw [step.core_marks_eq] at marked
    exact marked
  · unfold UnificationState.liveFrontierVertices at frontierMembership
    rcases List.mem_flatMap.mp frontierMembership with
      ⟨cell, cellMembership, vertexFrontier⟩
    cases cell with
    | none => simp at vertexFrontier
    | some component =>
        simp only [Option.map_some, Option.getD_some] at vertexFrontier
        rcases List.mem_iff_getElem.mp cellMembership with
          ⟨index, indexBound, indexEquation⟩
        have afterLookup :
            after.core.components[index]? = some (some component) := by
          rw [← Array.getElem?_toList]
          rw [List.getElem?_eq_getElem indexBound, indexEquation]
        by_cases previous : index = step.previousBoundary
        · subst index
          rw [step.core_components_expanded_eq invariant] at afterLookup
          simp [step.previous_bound invariant] at afterLookup
          subst component
          simp only [activatedComponent, List.mem_append] at vertexFrontier
          rcases vertexFrontier with contextMembership | waitingMembership
          · apply Or.inr
            have tensorFrontier :
                vertex ∈ step.tensorComponent.frontier := by
              have afterLeft :
                  vertex ∈ step.activationStep.queueStep.afterLeft :=
                (CutFreeDerivation.pick?_perm
                  step.activationStep.queueStep.right_pick.positional)
                    |>.mem_iff.mpr (by simp [contextMembership])
              have oldFrontier :
                  vertex ∈
                    step.activationStep.queueStep.component.frontier :=
                (CutFreeDerivation.pick?_perm
                  step.activationStep.queueStep.left_pick.positional)
                    |>.mem_iff.mpr (by simp [afterLeft])
              simpa [step.activation_component_eq_tensor invariant] using
                oldFrontier
            have producedTensor :
                (∃ age,
                  step.coreTensor.marks[vertex]? = some (some age)) ∨
                vertex ∈ step.coreTensor.liveFrontierVertices := by
              apply Or.inr
              unfold UnificationState.liveFrontierVertices
              apply List.mem_flatMap.mpr
              refine ⟨some step.tensorComponent, ?_, tensorFrontier⟩
              have tensorLookup :
                  step.coreTensor.components[step.previousBoundary]? =
                    some (some step.tensorComponent) := by
                rw [step.tensor_components_eq]
                simp [step.previous_bound invariant,
                  Nat.ne_of_gt step.previous_lt_active]
              exact List.mem_of_getElem? (by
                rw [Array.getElem?_toList]
                exact tensorLookup)
            exact step.tensor_produced_cases invariant producedTensor
          · left
            simpa using waitingMembership
        · by_cases active :
              index = step.prepared.stackResult.rawAge
          · subst index
            rw [step.core_components_expanded_eq invariant] at afterLookup
            rw [Array.getElem?_setIfInBounds_ne
              (Nat.ne_of_lt step.previous_lt_active)] at afterLookup
            simp [step.active_bound invariant] at afterLookup
          · apply Or.inr
            have tensorLookup :
                step.coreTensor.components[index]? =
                  some (some component) := by
              rw [step.tensor_components_eq]
              have previousNe : step.previousBoundary ≠ index :=
                Ne.symm previous
              have activeNe :
                  step.prepared.stackResult.rawAge ≠ index :=
                Ne.symm active
              rw [Array.getElem?_setIfInBounds_ne activeNe,
                Array.getElem?_setIfInBounds_ne previousNe]
              rw [step.core_components_expanded_eq invariant] at afterLookup
              rw [Array.getElem?_setIfInBounds_ne previousNe,
                Array.getElem?_setIfInBounds_ne activeNe,
                Array.getElem?_setIfInBounds_ne previousNe] at afterLookup
              exact afterLookup
            have producedTensor :
                (∃ age,
                  step.coreTensor.marks[vertex]? = some (some age)) ∨
                vertex ∈ step.coreTensor.liveFrontierVertices := by
              apply Or.inr
              unfold UnificationState.liveFrontierVertices
              apply List.mem_flatMap.mpr
              exact ⟨some component, List.mem_of_getElem? (by
                  rw [Array.getElem?_toList]
                  exact tensorLookup), by simpa using vertexFrontier⟩
            exact step.tensor_produced_cases invariant producedTensor

private theorem producedPremisesMarked
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyOneStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    ProducedPremisesMarked certificate after := by
  have middleInvariant := step.prepared.schedulerInvariant invariant
  intro link linkMembership
  cases link with
  | «axiom» left right => trivial
  | «par» left right conclusion
  | tensor left right conclusion =>
      intro producedAfter
      rcases step.produced_after_cases invariant producedAfter with
        waitingEq | tensorEq | producedMiddle
      · subst conclusion
        have currentMembership :
            (.par step.activationStep.producer.storedLeft
              step.activationStep.producer.storedRight
              step.waitingConclusion : Link) ∈ certificate.links :=
          List.mem_of_getElem? step.submitted_waiting_par
        have producerEq :=
          UnificationState.StructurallyWellFormed.producerLink_unique
            invariant.structural
            (conclusion := step.waitingConclusion)
            linkMembership (by simp [Link.produces])
            currentMembership (by simp [Link.produces])
        cases producerEq <;>
          exact step.waitingPremisesMarkedAfter
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
          exact step.tensorPremisesMarkedAfter
      · rcases middleInvariant.produced_premises_marked
            linkMembership producedMiddle with
          ⟨⟨leftAge, leftMarked⟩, rightAge, rightMarked⟩
        refine ⟨⟨leftAge, ?_⟩, rightAge, ?_⟩
        · rw [step.core_marks_eq]
          exact leftMarked
        · rw [step.core_marks_eq]
          exact rightMarked

private theorem waitingSpanExact
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyOneStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    WaitingSpanExact certificate after := by
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
      (Array.getElem?_eq_some_iff.mp step.waiting_one).1
    rw [step.after_waiting_eq] at waitingLookup
    simp [previousWaitingBound] at waitingLookup
  have middleWaitingLookup :
      step.prepared.stackResult.after.waiting[boundary]? =
        some (.initialized payload) := by
    rw [step.after_waiting_eq,
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
      sigmaBoundary? after.stack.sigma olderAge = some boundary := by
    rw [step.after_sigma_eq]
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
    · rw [step.core_marks_eq]
      exact conclusionUnmarked
    · rw [step.core_marks_eq]
      exact olderMarked
    · rw [step.core_marks_eq]
      exact youngerMarked
    · rw [step.after_sigma_eq]
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
    · rw [step.core_marks_eq]
      exact conclusionUnmarked
    · rw [step.core_marks_eq]
      exact olderMarked
    · rw [step.core_marks_eq]
      exact youngerMarked
    · rw [step.after_sigma_eq]
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

private theorem representative_after
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyOneStep certificate before after)
    (invariant : SchedulerInvariant certificate before)
    {rawAge : RawTokenAge}
    (rawBound : rawAge < step.prepared.coreMarked.parents.size) :
    after.core.representative rawAge =
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
  calc
    after.core.representative rawAge =
        (step.prepared.coreMarked.setParent
          step.prepared.stackResult.rawAge
          step.previousBoundary).representative rawAge := by
      unfold UnificationState.representative
      rw [step.core_parents_eq]
      rfl
    _ = _ :=
      middleOrdered.setParent_representative
        previousParentBound activeParentBound
        step.previous_lt_active previousRoot activeRoot rawBound

private theorem activated_componentAt
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyOneStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    after.core.componentAt? step.previousBoundary =
      some step.activatedComponent := by
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
      after.core.representative step.previousBoundary =
        step.previousBoundary := by
    rw [step.representative_after invariant previousParentBound,
      previousRootMiddle]
    simp [Nat.ne_of_lt step.previous_lt_active]
  unfold UnificationState.componentAt?
  rw [previousRootAfter, step.core_components_expanded_eq invariant]
  simp [step.previous_bound invariant]

private theorem tensorConclusion_mem_ready_after
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyOneStep certificate before after) :
    step.consumer.conclusion ∈ after.stack.ready.flatten := by
  rw [step.after_ready_eq]
  apply List.mem_flatten.mpr
  exact ⟨step.consumer.conclusion ::
      (step.waitingConclusion :: step.mergeStep.previousReady ++
        step.mergeStep.activeReady), by simp, by simp⟩

private theorem waitingConclusion_mem_ready_after
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyOneStep certificate before after) :
    step.waitingConclusion ∈ after.stack.ready.flatten := by
  rw [step.after_ready_eq]
  apply List.mem_flatten.mpr
  exact ⟨step.consumer.conclusion ::
      (step.waitingConclusion :: step.mergeStep.previousReady ++
        step.mergeStep.activeReady), by simp, by simp⟩

private theorem oldReady_subset_after
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyOneStep certificate before after)
    {vertex : Vertex}
    (membership : vertex ∈ step.prepared.after.stack.ready.flatten) :
    vertex ∈ after.stack.ready.flatten := by
  change vertex ∈
    step.prepared.stackResult.after.ready.flatten at membership
  rw [step.mergeStep.ready_eq] at membership
  rw [step.after_ready_eq]
  simp only [List.flatten_append, List.flatten_cons,
    List.flatten_nil, List.append_nil, List.mem_append,
    List.mem_cons] at membership ⊢
  rcases membership with inPrefix | inPrevious | inActive
  · exact Or.inl inPrefix
  · simp [inPrevious]
  · simp [inActive]

private theorem activation_context_of_tensor_frontier
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyOneStep certificate before after)
    (invariant : SchedulerInvariant certificate before)
    {vertex : Vertex}
    (neLeft : vertex ≠ step.activationStep.producer.storedLeft)
    (neRight : vertex ≠ step.activationStep.producer.storedRight)
    (frontier : vertex ∈ step.tensorComponent.frontier) :
    vertex ∈ step.activationStep.queueStep.context := by
  have frontier' :
      vertex ∈ step.activationStep.queueStep.component.frontier := by
    simpa [step.activation_component_eq_tensor invariant] using frontier
  have afterLeft :=
    Certificate.FirstOccurrencePick.mem_remaining_of_ne
      step.activationStep.queueStep.left_pick neLeft frontier'
  exact Certificate.FirstOccurrencePick.mem_remaining_of_ne
    step.activationStep.queueStep.right_pick neRight afterLeft

private theorem pendingPremisesCoveredExceptReady
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyOneStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    PendingPremisesCoveredExceptReady certificate after := by
  have middleInvariant := step.prepared.schedulerInvariant invariant
  intro link linkMembership
  cases link with
  | «axiom» left right => trivial
  | tensor left right conclusion
  | «par» left right conclusion =>
      intro conclusionUnmarked conclusionNotReady premise token
        premiseMembership tokenAt
      have conclusionNeTensor :
          conclusion ≠ step.consumer.conclusion := by
        intro same
        subst conclusion
        exact conclusionNotReady step.tensorConclusion_mem_ready_after
      have conclusionNeWaiting :
          conclusion ≠ step.waitingConclusion := by
        intro same
        subst conclusion
        exact conclusionNotReady step.waitingConclusion_mem_ready_after
      have middleConclusionUnmarked :
          step.prepared.after.core.marks[conclusion]? = some none := by
        change step.prepared.coreMarked.marks[conclusion]? = some none
        rw [← step.core_marks_eq]
        exact conclusionUnmarked
      have middleConclusionNotReady :
          conclusion ∉ step.prepared.after.stack.ready.flatten := by
        intro membership
        exact conclusionNotReady (step.oldReady_subset_after membership)
      rcases after.core.tokenAt?_some_witness tokenAt with
        ⟨rawAge, assignedAfter, representativeAfter⟩
      have assignedMiddle :
          step.prepared.coreMarked.assignedToken? premise =
            some rawAge := by
        unfold UnificationState.assignedToken? at assignedAfter ⊢
        rw [step.core_marks_eq] at assignedAfter
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
        have transported := step.representative_after invariant rawBound
        rw [representativeAfter] at transported
        exact transported
      rcases middleInvariant.pending_premises_covered_except_ready
          linkMembership middleConclusionUnmarked
          middleConclusionNotReady premiseMembership middleTokenAt with
        ⟨component, componentLookup, premiseFrontier⟩
      change step.prepared.coreMarked.componentAt? oldToken =
        some component at componentLookup
      have premiseNeTensorLeft :
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
        cases sameLink <;> exact conclusionNeTensor rfl
      have premiseNeTensorRight :
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
        cases sameLink <;> exact conclusionNeTensor rfl
      have premiseNeWaitingLeft :
          premise ≠ step.activationStep.producer.storedLeft := by
        intro same
        subst premise
        have sameLink :=
          UnificationState.StructurallyWellFormed.parentLink_unique
            invariant.structural
            (premise := step.activationStep.producer.storedLeft)
            (first := .par step.activationStep.producer.storedLeft
              step.activationStep.producer.storedRight
              step.waitingConclusion)
            (List.mem_of_getElem? step.submitted_waiting_par)
            (by simp [Link.premises]) linkMembership
            (by simpa [Link.premises] using premiseMembership)
        cases sameLink <;> exact conclusionNeWaiting rfl
      have premiseNeWaitingRight :
          premise ≠ step.activationStep.producer.storedRight := by
        intro same
        subst premise
        have sameLink :=
          UnificationState.StructurallyWellFormed.parentLink_unique
            invariant.structural
            (premise := step.activationStep.producer.storedRight)
            (first := .par step.activationStep.producer.storedLeft
              step.activationStep.producer.storedRight
              step.waitingConclusion)
            (List.mem_of_getElem? step.submitted_waiting_par)
            (by simp [Link.premises]) linkMembership
            (by simpa [Link.premises] using premiseMembership)
        cases sameLink <;> exact conclusionNeWaiting rfl
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
        have inTensorContext :=
          Certificate.FirstOccurrencePick.mem_remaining_of_ne
            step.tensorStep.left_pick premiseNeTensorLeft premiseFrontier
        have tensorFrontier : premise ∈ step.tensorComponent.frontier := by
          simp [tensorComponent, inTensorContext]
        have inActivationContext :=
          step.activation_context_of_tensor_frontier invariant
            premiseNeWaitingLeft premiseNeWaitingRight tensorFrontier
        have tokenPrevious : token = step.previousBoundary := by
          rw [tokenTransport, oldIsLeft]
          rcases step.tokens_eq_adjacent with orientation | orientation
          · rw [orientation.2.1]
            simp
          · rw [orientation.2.1]
            simp [Nat.ne_of_lt step.previous_lt_active]
        refine ⟨step.activatedComponent, ?_, ?_⟩
        · rw [tokenPrevious]
          exact step.activated_componentAt invariant
        · simp [activatedComponent, inActivationContext]
      · by_cases oldIsRight : oldToken = step.tensorStep.rightToken
        · have rawLookup :=
            UnificationState.componentAt?_some_raw componentLookup
          rw [oldRoot, oldIsRight] at rawLookup
          have componentEq : component = step.tensorStep.rightComponent :=
            Option.some.inj (Option.some.inj
              (rawLookup.symm.trans (step.right_component_raw invariant)))
          subst component
          have inTensorContext :=
            Certificate.FirstOccurrencePick.mem_remaining_of_ne
              step.tensorStep.right_pick premiseNeTensorRight
                premiseFrontier
          have tensorFrontier : premise ∈ step.tensorComponent.frontier := by
            simp [tensorComponent, inTensorContext]
          have inActivationContext :=
            step.activation_context_of_tensor_frontier invariant
              premiseNeWaitingLeft premiseNeWaitingRight tensorFrontier
          have tokenPrevious : token = step.previousBoundary := by
            rw [tokenTransport, oldIsRight]
            rcases step.tokens_eq_adjacent with orientation | orientation
            · rw [orientation.2.2]
              simp [Nat.ne_of_lt step.previous_lt_active]
            · rw [orientation.2.2]
              simp
          refine ⟨step.activatedComponent, ?_, ?_⟩
          · rw [tokenPrevious]
            exact step.activated_componentAt invariant
          · simp [activatedComponent, inActivationContext]
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
              after.core.representative oldToken = oldToken := by
            rw [step.representative_after invariant oldParentBound,
              oldRoot]
            simp [oldNeActive]
          rw [tokenOld]
          unfold UnificationState.componentAt? at componentLookup ⊢
          rw [oldRoot] at componentLookup
          rw [afterOldRoot, step.core_components_expanded_eq invariant]
          rw [Array.getElem?_setIfInBounds_ne (Ne.symm oldNePrevious),
            Array.getElem?_setIfInBounds_ne (Ne.symm oldNeActive),
            Array.getElem?_setIfInBounds_ne (Ne.symm oldNePrevious)]
          exact componentLookup

private theorem foldl_add_weight_eq_one
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

private theorem map_sum_set_balance_one
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

private theorem map_sum_set_merge_clear_one
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
  have first := map_sum_set_balance_one weight survivorLookup
    (newValue := mergedValue)
  have second := map_sum_set_balance_one weight retiredAfter
    (newValue := clearedValue)
  rw [clearedWeight] at second
  omega

private theorem map_sum_set_add_one_one
    {alpha : Type} {values : List alpha} {index : Nat}
    {oldValue newValue : alpha} (weight : alpha → Nat)
    (lookup : values[index]? = some oldValue)
    (weightEq : weight newValue = weight oldValue + 1) :
    ((values.set index newValue).map weight).sum =
      (values.map weight).sum + 1 := by
  have balance := map_sum_set_balance_one weight lookup
    (newValue := newValue)
  rw [weightEq] at balance
  omega

private theorem firedCounterExact
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyOneStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    FiredCounterExact after := by
  let weight : Option UnificationComponent → Nat := fun cell =>
    (cell.map UnificationComponent.connectiveCount).getD 0
  let values := step.prepared.coreMarked.components.toList
  let tensorValues :=
    (values.set step.previousBoundary (some step.tensorComponent)).set
      step.prepared.stackResult.rawAge none
  have middleInvariant := step.prepared.schedulerInvariant invariant
  have leftLookup :
      values[step.tensorStep.leftToken]? =
        some (some step.tensorStep.leftComponent) := by
    simpa [values] using step.left_component_raw invariant
  have rightLookup :
      values[step.tensorStep.rightToken]? =
        some (some step.tensorStep.rightComponent) := by
    simpa [values] using step.right_component_raw invariant
  have tensorSumIncrease :
      (tensorValues.map weight).sum =
        (values.map weight).sum + 1 := by
    dsimp [tensorValues]
    rcases step.tokens_eq_adjacent with orientation | orientation
    · rw [orientation.2.1] at leftLookup
      rw [orientation.2.2] at rightLookup
      apply map_sum_set_merge_clear_one weight
        (Nat.ne_of_lt step.previous_lt_active)
        rightLookup leftLookup
      · simp [weight]
      · simp [weight, tensorComponent,
          UnificationComponent.connectiveCount,
          CutFreeDerivation.connectiveCount]
        omega
    · rw [orientation.2.1] at leftLookup
      rw [orientation.2.2] at rightLookup
      apply map_sum_set_merge_clear_one weight
        (Nat.ne_of_lt step.previous_lt_active)
        leftLookup rightLookup
      · simp [weight]
      · simp [weight, tensorComponent,
          UnificationComponent.connectiveCount,
          CutFreeDerivation.connectiveCount]
  have tensorPreviousLookup :
      tensorValues[step.previousBoundary]? =
        some (some step.tensorComponent) := by
    dsimp [tensorValues]
    rw [List.getElem?_set_ne (Nat.ne_of_gt step.previous_lt_active)]
    apply List.getElem?_set_self
    simpa [values] using step.previous_bound invariant
  have activationWeightIncrease :
      weight (some step.activatedComponent) =
        weight (some step.tensorComponent) + 1 := by
    rw [← step.activation_component_eq_tensor invariant]
    simp [weight, activatedComponent,
      UnificationComponent.connectiveCount,
      CutFreeDerivation.connectiveCount]
  have activationSumIncrease :
      ((tensorValues.set step.previousBoundary
          (some step.activatedComponent)).map weight).sum =
        (tensorValues.map weight).sum + 1 :=
    map_sum_set_add_one_one weight tensorPreviousLookup
      activationWeightIncrease
  have totalSumIncrease :
      ((tensorValues.set step.previousBoundary
          (some step.activatedComponent)).map weight).sum =
        (values.map weight).sum + 2 := by
    omega
  have totalIncrease :
      (tensorValues.set step.previousBoundary
          (some step.activatedComponent)).foldl
          (fun total cell => total + weight cell) 0 =
        values.foldl
          (fun total cell => total + weight cell) 0 + 2 := by
    rw [foldl_add_weight_eq_one, foldl_add_weight_eq_one]
    simpa using totalSumIncrease
  have middleCounter := middleInvariant.fired_counter_exact
  unfold FiredCounterExact UnificationState.liveConnectiveCount at middleCounter
  change step.prepared.coreMarked.firedConnectives =
    values.foldl (fun total cell => total + weight cell) 0
      at middleCounter
  have firedAfter :
      after.core.firedConnectives =
        step.prepared.coreMarked.firedConnectives + 2 := by
    rw [step.after_core_eq]
    exact step.firedConnectives_eq_add_two
  unfold FiredCounterExact
  rw [firedAfter]
  unfold UnificationState.liveConnectiveCount
  rw [step.core_components_expanded_eq invariant]
  rw [Array.toList_setIfInBounds, Array.toList_setIfInBounds,
    Array.toList_setIfInBounds]
  change step.prepared.coreMarked.firedConnectives + 2 =
    (tensorValues.set step.previousBoundary
      (some step.activatedComponent)).foldl
        (fun total cell => total + weight cell) 0
  rw [totalIncrease]
  exact congrArg (fun count => count + 2) middleCounter

/-- A successful strict-singleton tensor-plus-par unification preserves every
field of the occurrence-exact state-only scheduler invariant.  This is a
preservation theorem for the exact singleton branch only; it does not assert
applicability, dispatcher progress, arbitrary nonempty-payload iteration, or
full unification totality. -/
theorem schedulerInvariant
    {certificate : Certificate} {before after : ReservationState}
    (step : UnifyOneStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    SchedulerInvariant certificate after := by
  exact {
    toReservationInvariant := step.reservationInvariant
    structural := invariant.structural
    component_domain_exact := step.componentDomainExact invariant
    component_forest_provenance :=
      step.componentForestProvenance invariant
    live_frontiers_nodup := step.liveFrontiersNodup invariant
    ready_bucket_frontier_exact :=
      step.readyBucketFrontierExact invariant
    queued_vertices_nodup := step.queuedVerticesNodup invariant
    queued_vertices_unmarked := step.queuedVerticesUnmarked invariant
    produced_premises_marked :=
      step.producedPremisesMarked invariant
    waiting_span_exact := step.waitingSpanExact invariant
    pending_premises_covered_except_ready :=
      step.pendingPremisesCoveredExceptReady invariant
    fired_counter_exact := step.firedCounterExact invariant }

end UnifyOneStep

/-- Executable strict-singleton `unifyOne?` success preserves the complete
current scheduler invariant.  The theorem covers exactly one waiting par
conclusion and makes no arbitrary-payload or dispatcher-totality claim. -/
theorem unifyOne?_schedulerInvariant
    {certificate : Certificate} {before after : ReservationState}
    (invariant : SchedulerInvariant certificate before)
    (equation :
      unifyOne? certificate before invariant.toReservationInvariant =
        some after) :
    SchedulerInvariant certificate after := by
  rcases
      (unifyOne?_some_iff invariant.toReservationInvariant).mp equation with
    ⟨step⟩
  exact step.schedulerInvariant invariant


/-- Executable `wait?` success preserves the complete current scheduler
invariant.  Applicability, totality, and dispatcher progress remain separate
obligations. -/
theorem wait?_schedulerInvariant
    {certificate : Certificate} {before after : ReservationState}
    (invariant : SchedulerInvariant certificate before)
    (equation :
      wait? certificate before invariant.toReservationInvariant =
        some after) :
    SchedulerInvariant certificate after := by
  rcases (wait?_some_iff invariant.toReservationInvariant).mp equation with
    ⟨step⟩
  exact step.schedulerInvariant invariant

/-- Exact `concl` witnesses preserve the current state-based scheduler invariant
because their output is precisely the synchronized prepared state. -/
theorem ConclStep.schedulerInvariant
    {certificate : Certificate} {before after : ReservationState}
    (step : ConclStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    SchedulerInvariant certificate after := by
  rw [step.output_eq]
  exact step.prepared.schedulerInvariant invariant

/-- Executable `concl?` success preserves the current state-based scheduler
invariant. -/
theorem concl?_schedulerInvariant
    {certificate : Certificate} {before after : ReservationState}
    (invariant : SchedulerInvariant certificate before)
    (equation :
      concl? certificate before invariant.toReservationInvariant =
        some after) :
    SchedulerInvariant certificate after := by
  rcases
      (concl?_some_iff invariant.toReservationInvariant).mp equation with
    ⟨step⟩
  exact step.schedulerInvariant invariant

/-- Exact `nop` witnesses preserve the current state-based scheduler invariant
because their output is precisely the synchronized prepared state. -/
theorem NopStep.schedulerInvariant
    {certificate : Certificate} {before after : ReservationState}
    (step : NopStep certificate before after)
    (invariant : SchedulerInvariant certificate before) :
    SchedulerInvariant certificate after := by
  rw [step.output_eq]
  exact step.prepared.schedulerInvariant invariant

/-- Executable `nop?` success preserves the current state-based scheduler
invariant. -/
theorem nop?_schedulerInvariant
    {certificate : Certificate} {before after : ReservationState}
    (invariant : SchedulerInvariant certificate before)
    (equation :
      nop? certificate before invariant.toReservationInvariant =
        some after) :
    SchedulerInvariant certificate after := by
  rcases
      (nop?_some_iff invariant.toReservationInvariant).mp equation with
    ⟨step⟩
  exact step.schedulerInvariant invariant

end SequentialFigure7

end ProofNetIR
