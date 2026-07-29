import ProofNetIR.SequentialFigure7Rules

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
membership only.
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

end ProofNetIR
