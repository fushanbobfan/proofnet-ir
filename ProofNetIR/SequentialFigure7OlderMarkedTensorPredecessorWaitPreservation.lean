/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7ActiveRegionTouchSeparation
import ProofNetIR.SequentialFigure7OlderMarkedTensorPredecessorInvariant

/-!
# Wait preservation of the older marked-tensor predecessor invariant

A canonical successful `wait` preserves the indexed immediate-predecessor
invariant for every retained future-work occurrence and for the conclusion
inserted at the wait destination boundary.

The created-conclusion proof combines canonical reservation history, exact
waiting-queue geometry, reference-switching-tree uniqueness, commitment
interval target avoidance, and the history-local touch exclusion. Both par
orientations are covered. No raw-unmarked-mate hypothesis is used.

The public surface consists of a conditional child-anchor bridge and
`CanonicalTagHistory.wait_olderMarkedTensorPredecessorInvariant`. All lower
geometry and created-conclusion lemmas are implementation details. This module
does not claim preservation for `forward` or `unifyPayload`, full dispatcher
closure, scheduler progress, maximality, or sequentialization.
-/


namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge
open SequentialUnification

private theorem mem_liveFrontierVertices_of_raw_waitAnchor
    {state : UnificationState} {token : Nat}
    {component : UnificationComponent} {vertex : Vertex}
    (componentLookup : state.components[token]? = some (some component))
    (vertexMembership : vertex ∈ component.frontier) :
    vertex ∈ state.liveFrontierVertices := by
  unfold UnificationState.liveFrontierVertices
  apply List.mem_flatMap.mpr
  refine ⟨some component, ?_, ?_⟩
  · exact List.mem_of_getElem? (by simpa using componentLookup)
  · simpa using vertexMembership

private theorem tensorConclusion_not_produced_of_futureWork
    {certificate : Certificate} {state : ReservationState}
    (invariant : SchedulerInvariant certificate state)
    {candidateRawAge : RawTokenAge} {candidateVertex : Vertex}
    (work : FutureWorkAt state candidateRawAge candidateVertex)
    (outer : TensorBelow)
    (outerValid :
      outer.Valid certificate certificate.consumerIndex candidateVertex) :
    ¬ Produced state outer.conclusion := by
  intro produced
  have tensorMembership :
      Link.tensor outer.storedLeft outer.storedRight outer.conclusion ∈
        certificate.links :=
    List.mem_of_getElem? outerValid.2.1
  have premises :=
    invariant.produced_premises_marked tensorMembership produced
  have candidateUnmarked :
      state.core.marks[candidateVertex]? = some none :=
    invariant.queued_vertices_unmarked candidateVertex work.mem_queued
  have premise := outerValid.2.2.2
  cases sideEquation : outer.side with
  | storedLeft =>
      rcases premises.1 with ⟨rawAge, marked⟩
      have candidateEq : candidateVertex = outer.storedLeft := by
        simpa [TensorBelow.premise, TensorPremiseSide.premise,
          sideEquation] using premise
      rw [← candidateEq, candidateUnmarked] at marked
      simp at marked
  | storedRight =>
      rcases premises.2 with ⟨rawAge, marked⟩
      have candidateEq : candidateVertex = outer.storedRight := by
        simpa [TensorBelow.premise, TensorPremiseSide.premise,
          sideEquation] using premise
      rw [← candidateEq, candidateUnmarked] at marked
      simp at marked

private theorem tensorConclusion_not_owned_of_futureWork
    {certificate : Certificate} {state : ReservationState}
    (invariant : SchedulerInvariant certificate state)
    {candidateRawAge : RawTokenAge} {candidateVertex : Vertex}
    (work : FutureWorkAt state candidateRawAge candidateVertex)
    (outer : TensorBelow)
    (outerValid :
      outer.Valid certificate certificate.consumerIndex candidateVertex)
    {index : Nat} {component : UnificationComponent} {owned : List Vertex}
    (componentLookup :
      state.core.components[index]? = some (some component))
    (accounted :
      Certificate.OwnedOccurrenceAccounted state.core index component owned) :
    outer.conclusion ∉ owned := by
  intro conclusionOwned
  apply tensorConclusion_not_produced_of_futureWork invariant work outer
    outerValid
  rcases accounted outer.conclusion conclusionOwned with
    ⟨rawAge, marked, _representative⟩ | ⟨_unmarked, frontier⟩
  · exact Or.inl ⟨rawAge, marked⟩
  · exact Or.inr
      (mem_liveFrontierVertices_of_raw_waitAnchor componentLookup frontier)

private theorem parLeftEdge_mem_leftRetained_wait
    {links : List Link} {left right conclusion : Vertex}
    (membership : Link.par left right conclusion ∈ links) :
    ({ first := left, second := conclusion } : Edge) ∈
      Certificate.linkLeftRetainedEdges links := by
  induction links with
  | nil => simp at membership
  | cons head tail induction =>
      rcases List.mem_cons.mp membership with same | rest
      · subst head
        simp [Certificate.linkLeftRetainedEdges]
      · cases head with
        | «axiom» =>
            simp only [Certificate.linkLeftRetainedEdges, List.mem_cons]
            exact Or.inr (induction rest)
        | «par» =>
            simp only [Certificate.linkLeftRetainedEdges, List.mem_cons]
            exact Or.inr (induction rest)
        | tensor =>
            simp only [Certificate.linkLeftRetainedEdges, List.mem_cons]
            exact Or.inr (Or.inr (induction rest))

private theorem sourceLeftStep_referenceDirectedEdge_wait
    {certificate : Certificate} {source next : Vertex}
    (step : SourceLeftStep certificate source next) :
    ∃ directed : certificate.referenceSwitchingGraph.DirectedEdge,
      directed.source = source ∧ directed.target = next := by
  cases step with
  | @tensor linkIndex _ right _ exactLink =>
      have membership := List.mem_of_getElem? exactLink
      have edgeMembership :
          ({ first := next, second := source } : Edge) ∈
            certificate.referenceSwitchingGraph.edges :=
        (UnificationMarking.referenceSwitchingGraph_tensorEdges
          certificate membership).1
      rcases List.getElem?_of_mem edgeMembership with
        ⟨edgeIndex, edgeLookup⟩
      let directed : certificate.referenceSwitchingGraph.DirectedEdge := {
        index := edgeIndex
        edge := { first := next, second := source }
        lookup := edgeLookup
        forward := false }
      refine ⟨directed, ?_, ?_⟩ <;>
        simp [directed, Graph.DirectedEdge.source,
          Graph.DirectedEdge.target]
  | @par linkIndex _ right _ exactLink =>
      have membership := List.mem_of_getElem? exactLink
      have edgeMembership :
          ({ first := next, second := source } : Edge) ∈
            certificate.referenceSwitchingGraph.edges := by
        rw [UnificationMarking.referenceSwitchingGraph_edges_eq_leftRetained]
        exact parLeftEdge_mem_leftRetained_wait membership
      rcases List.getElem?_of_mem edgeMembership with
        ⟨edgeIndex, edgeLookup⟩
      let directed : certificate.referenceSwitchingGraph.DirectedEdge := {
        index := edgeIndex
        edge := { first := next, second := source }
        lookup := edgeLookup
        forward := false }
      refine ⟨directed, ?_, ?_⟩ <;>
        simp [directed, Graph.DirectedEdge.source,
          Graph.DirectedEdge.target]

private theorem sourceLeftChain_referencePath_within_trace_wait
    {certificate : Certificate} {trace : List Vertex}
    (chain : SourceLeftChain certificate trace)
    {source target : Vertex}
    (head : trace.head? = some source)
    (last : trace.getLast? = some target) :
    ∃ path : certificate.referenceSwitchingGraph.EdgeSimplePath,
      path.start = source ∧ path.finish = target ∧
        ∀ vertex ∈ path.vertices, vertex ∈ trace := by
  induction chain generalizing source target with
  | singleton vertex =>
      simp only [List.head?_cons, Option.some.injEq] at head
      simp only [List.getLast?_singleton, Option.some.injEq] at last
      subst source
      subst target
      let path : certificate.referenceSwitchingGraph.EdgeSimplePath := {
        start := vertex
        finish := vertex
        traversed := []
        walk := .refl vertex
        verticesNodup := by
          simp [Graph.EdgeWalk.visitedVertices] }
      refine ⟨path, rfl, rfl, ?_⟩
      intro current membership
      simpa [path, Graph.EdgeSimplePath.vertices,
        Graph.EdgeWalk.visitedVertices] using membership
  | @cons current next tail step rest induction =>
      simp only [List.head?_cons, Option.some.injEq] at head
      subst source
      have restHead : (next :: tail).head? = some next := by simp
      have restLast : (next :: tail).getLast? = some target := by
        simpa [List.getLast?_cons_of_ne_nil (by simp : next :: tail ≠ [])]
          using last
      rcases induction restHead restLast with
        ⟨tailPath, tailStarts, tailFinishes, tailWithin⟩
      rcases sourceLeftStep_referenceDirectedEdge_wait step with
        ⟨directed, directedStarts, directedFinishes⟩
      have tailChain :
          certificate.referenceSwitchingGraph.EdgeChain directed.target
            tailPath.traversed target := by
        rw [directedFinishes, ← tailStarts, ← tailFinishes]
        exact tailPath.walk.toChain
      have walk :
          certificate.referenceSwitchingGraph.EdgeWalk current
            (directed :: tailPath.traversed) target :=
        Graph.EdgeChain.toWalk
          (Graph.EdgeChain.cons directed directedStarts tailChain)
      rcases walk.toEdgeSimplePathWithVerticesSubset with
        ⟨path, pathStarts, pathFinishes, subset⟩
      refine ⟨path, pathStarts, pathFinishes, ?_⟩
      intro vertex membership
      have inWalk := subset vertex membership
      simp only [Graph.EdgeWalk.visitedVertices, List.map_cons,
        List.mem_cons] at inWalk
      rcases inWalk with rfl | atNextOrTail
      · simp
      · have inTailPath : vertex ∈ tailPath.vertices := by
          simpa [Graph.EdgeSimplePath.vertices,
            Graph.EdgeWalk.visitedVertices, directedFinishes,
            ← tailStarts] using atNextOrTail
        exact List.mem_cons.mpr (Or.inr (tailWithin vertex inTailPath))

private theorem tensorReferencePath_wait
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {left right conclusion : Vertex}
    (membership : Link.tensor left right conclusion ∈ certificate.links) :
    ∃ path : certificate.referenceSwitchingGraph.EdgeSimplePath,
      path.start = left ∧ path.finish = right ∧
        path.vertices = [left, conclusion, right] := by
  have wellFormed : certificate.LinkWellFormed (.tensor left right conclusion) :=
    structural.2.2.2.2.1 _ membership
  have edges := UnificationMarking.referenceSwitchingGraph_tensorEdges
    certificate membership
  let leftEdge : Edge := { first := left, second := conclusion }
  let rightEdge : Edge := { first := right, second := conclusion }
  rcases List.getElem?_of_mem (by simpa [leftEdge] using edges.1) with
    ⟨leftIndex, leftLookup⟩
  rcases List.getElem?_of_mem (by simpa [rightEdge] using edges.2) with
    ⟨rightIndex, rightLookup⟩
  let leftDirected : certificate.referenceSwitchingGraph.DirectedEdge := {
    index := leftIndex
    edge := leftEdge
    lookup := leftLookup
    forward := true }
  let rightDirected : certificate.referenceSwitchingGraph.DirectedEdge := {
    index := rightIndex
    edge := rightEdge
    lookup := rightLookup
    forward := false }
  let path : certificate.referenceSwitchingGraph.EdgeSimplePath := {
    start := left
    finish := right
    traversed := [leftDirected, rightDirected]
    walk := by
      simpa [leftDirected, rightDirected, leftEdge, rightEdge,
        Graph.DirectedEdge.source, Graph.DirectedEdge.target] using
        Graph.EdgeWalk.step
          (Graph.EdgeWalk.step
            (Graph.EdgeWalk.refl
              (graph := certificate.referenceSwitchingGraph) left)
            leftDirected rfl rfl)
          rightDirected rfl rfl
    verticesNodup := by
      simp [Graph.EdgeWalk.visitedVertices, leftDirected, rightDirected,
        leftEdge, rightEdge, Graph.DirectedEdge.target, wellFormed.2.1]
      exact ⟨wellFormed.1, fun same ↦ wellFormed.2.2.1 same.symm⟩ }
  refine ⟨path, rfl, rfl, ?_⟩
  simp [path, Graph.EdgeSimplePath.vertices,
    Graph.EdgeWalk.visitedVertices, leftDirected, rightDirected,
    leftEdge, rightEdge, Graph.DirectedEdge.target]

private theorem tensorBelow_referencePath_wait
    {certificate : Certificate} {vertex : Vertex} {tensor : TensorBelow}
    (structural : certificate.StructurallyWellFormed)
    (valid : tensor.Valid certificate certificate.consumerIndex vertex) :
    ∃ path : certificate.referenceSwitchingGraph.EdgeSimplePath,
      path.start = vertex ∧ path.finish = tensor.mate ∧
        path.vertices = [vertex, tensor.conclusion, tensor.mate] := by
  have membership :
      Link.tensor tensor.storedLeft tensor.storedRight tensor.conclusion ∈
        certificate.links :=
    List.mem_of_getElem? valid.2.1
  rcases tensorReferencePath_wait structural membership with
    ⟨path, pathStarts, pathFinishes, pathVertices⟩
  have premise := valid.2.2.2
  cases sideEquation : tensor.side with
  | storedLeft =>
      have vertexLeft : vertex = tensor.storedLeft := by
        simpa [TensorBelow.premise, TensorPremiseSide.premise,
          sideEquation] using premise
      refine ⟨path, pathStarts.trans vertexLeft.symm, ?_, ?_⟩
      · simpa [TensorBelow.mate, TensorPremiseSide.mate,
          sideEquation] using pathFinishes
      · simpa [TensorBelow.premise, TensorPremiseSide.premise,
          TensorBelow.mate, TensorPremiseSide.mate, sideEquation,
          premise] using pathVertices
  | storedRight =>
      have vertexRight : vertex = tensor.storedRight := by
        simpa [TensorBelow.premise, TensorPremiseSide.premise,
          sideEquation] using premise
      refine ⟨path.reverse, ?_, ?_, ?_⟩
      · exact pathFinishes.trans vertexRight.symm
      · simpa [Graph.EdgeSimplePath.reverse, TensorBelow.mate,
          TensorPremiseSide.mate, sideEquation] using pathStarts
      · rw [Graph.EdgeSimplePath.reverse_vertices, pathVertices]
        simp [TensorBelow.premise, TensorPremiseSide.premise,
          TensorBelow.mate, TensorPremiseSide.mate, sideEquation, premise]

private theorem selectedToReachedReferencePath_avoiding_wait
    {certificate : Certificate} {before after : ReservationState}
    (structural : certificate.StructurallyWellFormed)
    (step : NewStep certificate before after)
    {target : Vertex}
    (selectedNe : step.stackResult.vertex ≠ target)
    (conclusionNe : step.tensor.conclusion ≠ target)
    (untouched : ¬ (ReservationEvent.new step).Touched target) :
    ∃ path : certificate.referenceSwitchingGraph.EdgeSimplePath,
      path.start = step.stackResult.vertex ∧ path.finish = step.reached ∧
        target ∉ path.vertices := by
  rcases tensorBelow_referencePath_wait structural step.tensorValid with
    ⟨tensorPath, tensorStarts, tensorFinishes, tensorVertices⟩
  have targetNotTrace : target ∉ step.search.trace := by
    intro membership
    exact untouched (Or.inl membership)
  have mateInTrace : step.tensor.mate ∈ step.search.trace := by
    cases traceEquation : step.search.trace with
    | nil =>
        have traceHead := step.route.traceHead
        simp [traceEquation] at traceHead
    | cons head tail =>
        have headEq : head = step.tensor.mate := by
          simpa [traceEquation] using step.route.traceHead
        subst head
        simp
  have mateNe : step.tensor.mate ≠ target := by
    intro same
    apply targetNotTrace
    simpa [same] using mateInTrace
  have tensorAvoids : target ∉ tensorPath.vertices := by
    rw [tensorVertices]
    simp [Ne.symm selectedNe, Ne.symm conclusionNe, Ne.symm mateNe]
  rcases sourceLeftChain_referencePath_within_trace_wait step.route.chain
      step.route.traceHead step.route.traceLast with
    ⟨routePath, routeStarts, routeFinishes, routeWithin⟩
  have routeAvoids : target ∉ routePath.vertices := by
    intro membership
    exact targetNotTrace (routeWithin target membership)
  rcases Graph.EdgeSimplePath.connectEraseAvoiding tensorPath routePath
      (tensorFinishes.trans routeStarts.symm) tensorAvoids routeAvoids with
    ⟨path, pathStarts, pathFinishes, pathAvoids⟩
  exact ⟨path, pathStarts.trans tensorStarts,
    pathFinishes.trans routeFinishes, pathAvoids⟩

private theorem no_alternateEdgeWalk_wait {graph : Graph}
    (tree : graph.IsTree) (edge : graph.DirectedEdge)
    {traversed : List graph.DirectedEdge}
    (walk : graph.EdgeWalk edge.source traversed edge.target)
    (avoids : ∀ directed ∈ traversed,
      directed.index ≠ edge.index) :
    False := by
  have returning :
      graph.EdgeWalk edge.target [edge.reverse] edge.source := by
    simpa using
      Graph.EdgeWalk.step (.refl edge.target) edge.reverse
        (by simp) (by simp)
  have closed :
      graph.EdgeWalk edge.source (traversed ++ [edge.reverse]) edge.source :=
    walk.trans returning
  rcases closed.normalizeCyclicImmediateReversalsTraced with
    ⟨base, normalized, normalizedWalk, normalization, normalizedShape⟩
  by_cases normalizedEmpty : normalized = []
  · have reversePresent : edge.reverse ∈ traversed ++ [edge.reverse] := by
      simp
    have forwardPresent : edge.reverse.reverse ∈ traversed ++ [edge.reverse] :=
      normalization.reverse_mem_of_normalizes_to_nil normalizedEmpty
        edge.reverse reversePresent
    have edgePresent : edge ∈ traversed ++ [edge.reverse] := by
      simpa using forwardPresent
    rcases List.mem_append.mp edgePresent with inAlternate | atReturn
    · exact avoids edge inAlternate rfl
    · have same : edge = edge.reverse := by simpa using atReturn
      exact edge.ne_reverse same
  · have normalizedReduced :
        Graph.EdgeWalk.CyclicNoImmediateReverse normalized := by
      rcases normalizedShape with empty | reduced
      · exact False.elim (normalizedEmpty empty)
      · exact reduced
    exact tree.no_cyclicNoImmediateReverse
      normalizedEmpty normalizedWalk normalizedReduced

private theorem sourceLeftStep_referenceDirectedEdge_exact_wait
    {certificate : Certificate} {source next : Vertex}
    (step : SourceLeftStep certificate source next) :
    ∃ directed : certificate.referenceSwitchingGraph.DirectedEdge,
      directed.source = source ∧ directed.target = next ∧
        directed.edge = ({ first := next, second := source } : Edge) := by
  cases step with
  | @tensor linkIndex _ right _ exactLink =>
      have membership := List.mem_of_getElem? exactLink
      have edgeMembership :
          ({ first := next, second := source } : Edge) ∈
            certificate.referenceSwitchingGraph.edges :=
        (UnificationMarking.referenceSwitchingGraph_tensorEdges
          certificate membership).1
      rcases List.getElem?_of_mem edgeMembership with
        ⟨edgeIndex, edgeLookup⟩
      let directed : certificate.referenceSwitchingGraph.DirectedEdge := {
        index := edgeIndex
        edge := { first := next, second := source }
        lookup := edgeLookup
        forward := false }
      refine ⟨directed, ?_, ?_, rfl⟩ <;>
        simp [directed, Graph.DirectedEdge.source,
          Graph.DirectedEdge.target]
  | @par linkIndex _ right _ exactLink =>
      have membership := List.mem_of_getElem? exactLink
      have edgeMembership :
          ({ first := next, second := source } : Edge) ∈
            certificate.referenceSwitchingGraph.edges := by
        rw [UnificationMarking.referenceSwitchingGraph_edges_eq_leftRetained]
        exact parLeftEdge_mem_leftRetained_wait membership
      rcases List.getElem?_of_mem edgeMembership with
        ⟨edgeIndex, edgeLookup⟩
      let directed : certificate.referenceSwitchingGraph.DirectedEdge := {
        index := edgeIndex
        edge := { first := next, second := source }
        lookup := edgeLookup
        forward := false }
      refine ⟨directed, ?_, ?_, rfl⟩ <;>
        simp [directed, Graph.DirectedEdge.source,
          Graph.DirectedEdge.target]

private theorem sourceLeftReachable_referenceWalk_avoiding_upEdge_wait
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {source target lower : Vertex}
    (reachable : SourceLeftReachable certificate source target)
    (lowerBelowTarget :
      certificate.formulaComplexityAt lower <
        certificate.formulaComplexityAt target) :
    ∃ traversed :
        List certificate.referenceSwitchingGraph.DirectedEdge,
      certificate.referenceSwitchingGraph.EdgeWalk
          source traversed target ∧
        ∀ directed ∈ traversed,
          directed.edge ≠ ({ first := lower, second := target } : Edge) := by
  induction reachable with
  | refl =>
      exact ⟨[], .refl _, by simp⟩
  | @step source next target head tail induction =>
      rcases induction lowerBelowTarget with
        ⟨tailTraversal, tailWalk, tailAvoids⟩
      rcases sourceLeftStep_referenceDirectedEdge_exact_wait head with
        ⟨directed, directedStarts, directedFinishes, directedEdge⟩
      have headAvoids :
          directed.edge ≠ ({ first := lower, second := target } : Edge) := by
        intro edgeEq
        have firstEq := congrArg Edge.first edgeEq
        have nextEq : next = lower := by
          simpa [directedEdge] using firstEq
        have tailRanks := tail.formulaComplexity_le structural
        rw [nextEq] at tailRanks
        omega
      have firstWalk :
          certificate.referenceSwitchingGraph.EdgeWalk
            source [directed] next := by
        simpa [directedStarts, directedFinishes] using
          Graph.EdgeWalk.step (.refl source) directed
            directedStarts directedFinishes
      refine ⟨directed :: tailTraversal, ?_, ?_⟩
      · simpa using firstWalk.trans tailWalk
      · intro candidate candidateMembership
        rcases List.mem_cons.mp candidateMembership with rfl | inTail
        · exact headAvoids
        · exact tailAvoids candidate inTail

private theorem tensorBelow_referenceWalk_avoiding_conclusionEdge_wait
    {certificate : Certificate} {vertex : Vertex} {tensor : TensorBelow}
    (valid : tensor.Valid certificate certificate.consumerIndex vertex)
    {lower target : Vertex}
    (conclusionNe : tensor.conclusion ≠ target) :
    ∃ traversed :
        List certificate.referenceSwitchingGraph.DirectedEdge,
      certificate.referenceSwitchingGraph.EdgeWalk
          vertex traversed tensor.mate ∧
        ∀ directed ∈ traversed,
          directed.edge ≠ ({ first := lower, second := target } : Edge) := by
  have membership :
      Link.tensor tensor.storedLeft tensor.storedRight tensor.conclusion ∈
        certificate.links :=
    List.mem_of_getElem? valid.2.1
  have edges :=
    UnificationMarking.referenceSwitchingGraph_tensorEdges
      certificate membership
  let leftEdge : Edge :=
    { first := tensor.storedLeft, second := tensor.conclusion }
  let rightEdge : Edge :=
    { first := tensor.storedRight, second := tensor.conclusion }
  have leftMembership :
      leftEdge ∈ certificate.referenceSwitchingGraph.edges := by
    simpa [leftEdge] using edges.1
  have rightMembership :
      rightEdge ∈ certificate.referenceSwitchingGraph.edges := by
    simpa [rightEdge] using edges.2
  rcases List.getElem?_of_mem leftMembership with
    ⟨leftIndex, leftLookup⟩
  rcases List.getElem?_of_mem rightMembership with
    ⟨rightIndex, rightLookup⟩
  let leftForward : certificate.referenceSwitchingGraph.DirectedEdge := {
    index := leftIndex
    edge := leftEdge
    lookup := leftLookup
    forward := true }
  let leftBackward : certificate.referenceSwitchingGraph.DirectedEdge := {
    index := leftIndex
    edge := leftEdge
    lookup := leftLookup
    forward := false }
  let rightForward : certificate.referenceSwitchingGraph.DirectedEdge := {
    index := rightIndex
    edge := rightEdge
    lookup := rightLookup
    forward := true }
  let rightBackward : certificate.referenceSwitchingGraph.DirectedEdge := {
    index := rightIndex
    edge := rightEdge
    lookup := rightLookup
    forward := false }
  have leftAvoids :
      leftEdge ≠ ({ first := lower, second := target } : Edge) := by
    intro same
    apply conclusionNe
    exact congrArg Edge.second same
  have rightAvoids :
      rightEdge ≠ ({ first := lower, second := target } : Edge) := by
    intro same
    apply conclusionNe
    exact congrArg Edge.second same
  have premise := valid.2.2.2
  cases sideEquation : tensor.side with
  | storedLeft =>
      have selectedEq : vertex = tensor.storedLeft := by
        simpa [TensorBelow.premise, TensorPremiseSide.premise,
          sideEquation] using premise
      have mateEq : tensor.mate = tensor.storedRight := by
        simp [TensorBelow.mate, TensorPremiseSide.mate, sideEquation]
      refine ⟨[leftForward, rightBackward], ?_, ?_⟩
      · rw [selectedEq, mateEq]
        simpa [leftForward, leftBackward, rightForward, rightBackward,
          leftEdge, rightEdge, Graph.DirectedEdge.source,
          Graph.DirectedEdge.target] using
          Graph.EdgeWalk.step
            (Graph.EdgeWalk.step
              (Graph.EdgeWalk.refl
                (graph := certificate.referenceSwitchingGraph)
                tensor.storedLeft)
              leftForward rfl rfl)
            rightBackward rfl rfl
      · intro directed inWalk
        simp at inWalk
        rcases inWalk with rfl | rfl
        · exact leftAvoids
        · exact rightAvoids
  | storedRight =>
      have selectedEq : vertex = tensor.storedRight := by
        simpa [TensorBelow.premise, TensorPremiseSide.premise,
          sideEquation] using premise
      have mateEq : tensor.mate = tensor.storedLeft := by
        simp [TensorBelow.mate, TensorPremiseSide.mate, sideEquation]
      refine ⟨[rightForward, leftBackward], ?_, ?_⟩
      · rw [selectedEq, mateEq]
        simpa [leftForward, leftBackward, rightForward, rightBackward,
          leftEdge, rightEdge, Graph.DirectedEdge.source,
          Graph.DirectedEdge.target] using
          Graph.EdgeWalk.step
            (Graph.EdgeWalk.step
              (Graph.EdgeWalk.refl
                (graph := certificate.referenceSwitchingGraph)
                tensor.storedRight)
              rightForward rfl rfl)
            leftBackward rfl rfl
      · intro directed inWalk
        simp at inWalk
        rcases inWalk with rfl | rfl
        · exact rightAvoids
        · exact leftAvoids

private theorem edgeSimplePath_edgeValues_avoid_incident_forbidden_wait
    {graph : Graph} (path : graph.EdgeSimplePath)
    {other forbidden : Vertex}
    (forbiddenNotInPath : forbidden ∉ path.vertices) :
    ∀ directed ∈ path.traversed,
      directed.edge ≠ ({ first := other, second := forbidden } : Edge) := by
  intro directed membership sameEdge
  have endpoints := path.directed_endpoints_mem_vertices membership
  cases orientation : directed.forward with
  | false =>
      have sourceEq : directed.source = forbidden := by
        simp [Graph.DirectedEdge.source, orientation, sameEdge]
      exact forbiddenNotInPath (sourceEq ▸ endpoints.1)
  | true =>
      have targetEq : directed.target = forbidden := by
        simp [Graph.DirectedEdge.target, orientation, sameEdge]
      exact forbiddenNotInPath (targetEq ▸ endpoints.2)

private theorem edgeSimplePath_edgeValues_avoid_incident_first_wait
    {graph : Graph} (path : graph.EdgeSimplePath)
    {forbidden other : Vertex}
    (forbiddenNotInPath : forbidden ∉ path.vertices) :
    ∀ directed ∈ path.traversed,
      directed.edge ≠ ({ first := forbidden, second := other } : Edge) := by
  intro directed membership sameEdge
  have endpoints := path.directed_endpoints_mem_vertices membership
  cases orientation : directed.forward with
  | false =>
      have targetEq : directed.target = forbidden := by
        simp [Graph.DirectedEdge.target, orientation, sameEdge]
      exact forbiddenNotInPath (targetEq ▸ endpoints.2)
  | true =>
      have sourceEq : directed.source = forbidden := by
        simp [Graph.DirectedEdge.source, orientation, sameEdge]
      exact forbiddenNotInPath (sourceEq ▸ endpoints.1)

private theorem no_referenceAlternateToTensorConclusion_wait
    {certificate : Certificate}
    (correct : certificate.DeclarativelyCorrect)
    {left right conclusion : Vertex}
    (membership : Link.tensor left right conclusion ∈ certificate.links)
    {traversed :
      List certificate.referenceSwitchingGraph.DirectedEdge}
    (walk : certificate.referenceSwitchingGraph.EdgeWalk
      right traversed conclusion)
    (avoids : ∀ directed ∈ traversed,
      directed.edge ≠ ({ first := right, second := conclusion } : Edge)) :
    False := by
  have edges :=
    UnificationMarking.referenceSwitchingGraph_tensorEdges
      certificate membership
  let activeEdge : Edge := { first := right, second := conclusion }
  have activeMembership :
      activeEdge ∈ certificate.referenceSwitchingGraph.edges := by
    simpa [activeEdge] using edges.2
  rcases List.getElem?_of_mem activeMembership with
    ⟨activeIndex, activeLookup⟩
  let activeDirected :
      certificate.referenceSwitchingGraph.DirectedEdge := {
    index := activeIndex
    edge := activeEdge
    lookup := activeLookup
    forward := true }
  have activeStarts : activeDirected.source = right := by
    simp [activeDirected, activeEdge, Graph.DirectedEdge.source]
  have activeFinishes : activeDirected.target = conclusion := by
    simp [activeDirected, activeEdge, Graph.DirectedEdge.target]
  have exactWalk :
      certificate.referenceSwitchingGraph.EdgeWalk activeDirected.source
        traversed activeDirected.target := by
    simpa [activeStarts, activeFinishes] using walk
  apply no_alternateEdgeWalk_wait correct.referenceSwitchingTree
    activeDirected exactWalk
  intro directed inWalk sameIndex
  apply avoids directed inWalk
  apply Option.some.inj
  rw [← directed.lookup, ← activeLookup, sameIndex]

private theorem reservationLedger_lookup_of_mem_rawAge_wait
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    {event : ReservationEvent certificate} {rawAge : RawTokenAge}
    (membership : event ∈ tagHistory.reservationLedger)
    (eventAge : event.rawAge = rawAge) :
    tagHistory.reservationLedger[rawAge]? = some event := by
  rcases List.mem_iff_getElem.mp membership with
    ⟨position, positionBound, positionEquation⟩
  have positionStateBound : position < state.stack.nextAge := by
    rw [← tagHistory.reservationLedger_length]
    exact positionBound
  have rawAtPosition :=
    tagHistory.reservationLedger_getElem?_rawAge
      position positionStateBound
  have lookupAtPosition :
      tagHistory.reservationLedger[position]? = some event := by
    rw [List.getElem?_eq_getElem positionBound, positionEquation]
  have positionAge : event.rawAge = position := by
    simpa [lookupAtPosition] using rawAtPosition
  have positionEq : position = rawAge := positionAge.symm.trans eventAge
  simpa [positionEq] using lookupAtPosition

private theorem reservationEvent_rawAge_eq_of_lookup_wait
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    {rawAge : RawTokenAge} {event : ReservationEvent certificate}
    (lookup : tagHistory.reservationLedger[rawAge]? = some event) :
    event.rawAge = rawAge := by
  have bound : rawAge < state.stack.nextAge := by
    rw [← tagHistory.reservationLedger_length]
    exact (List.getElem?_eq_some_iff.mp lookup).1
  have exactRawAge :=
    tagHistory.reservationLedger_getElem?_rawAge rawAge bound
  simpa [lookup] using exactRawAge

private theorem sourceLeftReachable_trans_wait
    {certificate : Certificate} {first middle last : Vertex}
    (firstPath : SourceLeftReachable certificate first middle)
    (suffix : SourceLeftReachable certificate middle last) :
    SourceLeftReachable certificate first last := by
  induction firstPath with
  | refl => exact suffix
  | step head tail induction => exact .step head (induction suffix)

private theorem reservationEvent_touched_tensor_storedLeft_wait
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    (event : ReservationEvent certificate)
    {tensor : TensorBelow} {head : Vertex}
    (valid : tensor.Valid certificate certificate.consumerIndex head)
    (touched : event.Touched tensor.conclusion) :
    event.Touched tensor.storedLeft := by
  apply event.sourceLeftRegion_touched structural
  have conclusionRegion :
      SourceLeftRegionVertex certificate event.start tensor.conclusion :=
    event.touched_sourceLeftRegion touched
  cases conclusionRegion with
  | visited reachable =>
      have suffix : SourceLeftReachable certificate tensor.conclusion
          tensor.storedLeft :=
        .step (.tensor valid.2.1) (.refl tensor.storedLeft)
      exact .visited (sourceLeftReachable_trans_wait reachable suffix)
  | @terminalPartner reached _partner linkIndex reachable exactAxiom =>
      have tensorMembership :
          Link.tensor tensor.storedLeft tensor.storedRight tensor.conclusion ∈
            certificate.links :=
        List.mem_of_getElem? valid.2.1
      exfalso
      rcases exactAxiom with axiomEq | axiomEq
      · exact structural.axiomEndpoint_ne_connectiveConclusion
          (List.mem_of_getElem? axiomEq) (Or.inr rfl) tensorMembership
          (by simp [Link.produces])
      · exact structural.axiomEndpoint_ne_connectiveConclusion
          (List.mem_of_getElem? axiomEq) (Or.inl rfl) tensorMembership
          (by simp [Link.produces])

private theorem representative_eq_of_sigmaAt_wait
    {certificate : Certificate} {state : ReservationState}
    (invariant : SchedulerInvariant certificate state)
    {position : Nat} {rawAge : RawTokenAge}
    (sigmaAt : state.stack.sigma[position]? = some rawAge) :
    state.core.representative rawAge = rawAge := by
  have rawAgeMembership : rawAge ∈ state.stack.sigma :=
    List.mem_of_getElem? sigmaAt
  have rawAgeBound : rawAge < state.stack.nextAge :=
    invariant.stack_wellShaped.sigma_partition.boundary_lt rawAge
      rawAgeMembership
  rcases invariant.stack_wellShaped.sigma_partition.boundary_exists
      rawAgeBound with ⟨boundary, boundaryLookup⟩
  have boundaryLeRawAge : boundary ≤ rawAge :=
    sigmaBoundary?_le boundaryLookup
  have rawAgeLeBoundary : rawAge ≤ boundary :=
    sigmaBoundary?_greatest
      invariant.stack_wellShaped.sigma_partition.strictIncreasing
      boundaryLookup rawAge rawAgeMembership (Nat.le_refl _)
  have boundaryEq : boundary = rawAge :=
    Nat.le_antisymm boundaryLeRawAge rawAgeLeBoundary
  subst boundary
  have representativeLookup :=
    invariant.realizesSigma.representative_eq_boundary rawAgeBound
  exact Option.some.inj (representativeLookup.symm.trans boundaryLookup)

private theorem event_rawAge_lt_nextAge_wait
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    {event : ReservationEvent certificate}
    (membership : event ∈ tagHistory.reservationLedger) :
    event.rawAge < state.stack.nextAge := by
  have mapped :
      event.rawAge ∈
        tagHistory.reservationLedger.map ReservationEvent.rawAge :=
    List.mem_map.mpr ⟨event, membership, rfl⟩
  rw [tagHistory.reservationLedger_rawAges] at mapped
  simpa using mapped

/-- `strictOlderSigmaSplit` only uses the future-work portion of its public
candidate carrier.  This specialization makes that exact
dependency explicit and is valid even when the candidate tensor mate is
already marked. -/
private theorem strictOlderSigmaSplit_of_event_futureWork
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (invariant : SchedulerInvariant certificate state)
    {event : ReservationEvent certificate}
    (eventMembership : event ∈ tagHistory.reservationLedger)
    {candidateRawAge : RawTokenAge} {candidateVertex : Vertex}
    (work : FutureWorkAt state candidateRawAge candidateVertex)
    (older :
      state.core.representative event.rawAge <
        state.core.representative candidateRawAge) :
    StrictOlderSigmaSplit state
      (state.core.representative event.rawAge) candidateRawAge := by
  have eventBound :=
    event_rawAge_lt_nextAge_wait tagHistory eventMembership
  have eventLookup :=
    invariant.realizesSigma.representative_eq_boundary eventBound
  have eventMembershipSigma :
      state.core.representative event.rawAge ∈ state.stack.sigma :=
    sigmaBoundary?_mem eventLookup
  rcases List.getElem_of_mem eventMembershipSigma with
    ⟨eventPosition, eventPositionBound, eventAtValue⟩
  have eventAt :
      state.stack.sigma[eventPosition]? =
        some (state.core.representative event.rawAge) := by
    rw [List.getElem?_eq_getElem eventPositionBound, eventAtValue]
  have candidateMembership : candidateRawAge ∈ state.stack.sigma :=
    work.rawAge_mem_sigma invariant
  rcases List.getElem_of_mem candidateMembership with
    ⟨candidatePosition, candidatePositionBound, candidateAtValue⟩
  have candidateAtPosition :
      state.stack.sigma[candidatePosition]? = some candidateRawAge := by
    rw [List.getElem?_eq_getElem candidatePositionBound, candidateAtValue]
  have candidateRoot :
      state.core.representative candidateRawAge = candidateRawAge :=
    work.representative_eq_rawAge invariant
  have eventBeforeCandidate : eventPosition < candidatePosition := by
    by_cases candidateLeEvent : candidatePosition ≤ eventPosition
    · rcases Nat.eq_or_lt_of_le candidateLeEvent with same | before
      · have sameLookup :
            state.stack.sigma[eventPosition]? = some candidateRawAge := by
          simpa [same] using candidateAtPosition
        have agesEq :
            state.core.representative event.rawAge = candidateRawAge :=
          Option.some.inj (eventAt.symm.trans sameLookup)
        rw [candidateRoot, agesEq] at older
        exact (Nat.lt_irrefl _ older).elim
      · have ordered :=
          (List.pairwise_iff_getElem.mp
            invariant.stack_wellShaped.sigma_partition.strictIncreasing)
            candidatePosition eventPosition candidatePositionBound
            eventPositionBound before
        rw [candidateAtValue, eventAtValue] at ordered
        rw [candidateRoot] at older
        exact ((Nat.not_lt_of_ge (Nat.le_of_lt ordered)) older).elim
    · exact Nat.lt_of_not_ge candidateLeEvent
  let edgeCount := candidatePosition - eventPosition - 1
  have predecessorPositionBound :
      eventPosition + edgeCount < state.stack.sigma.length := by
    dsimp [edgeCount]
    omega
  let predecessor := state.stack.sigma[eventPosition + edgeCount]
  have predecessorAt :
      state.stack.sigma[eventPosition + edgeCount]? = some predecessor := by
    rw [List.getElem?_eq_getElem predecessorPositionBound]
  have candidateAt :
      state.stack.sigma[eventPosition + edgeCount + 1]? =
        some candidateRawAge := by
    have indexEq :
        eventPosition + edgeCount + 1 = candidatePosition := by
      dsimp [edgeCount]
      omega
    simpa [indexEq] using candidateAtPosition
  have predecessorRawOlder : predecessor < candidateRawAge := by
    rcases List.getElem?_eq_some_iff.mp predecessorAt with
      ⟨predecessorPositionBoundAgain, predecessorAtValue⟩
    have indexEq :
        eventPosition + edgeCount + 1 = candidatePosition := by
      dsimp [edgeCount]
      omega
    have ordered :=
      (List.pairwise_iff_getElem.mp
        invariant.stack_wellShaped.sigma_partition.strictIncreasing)
        (eventPosition + edgeCount) candidatePosition
        predecessorPositionBoundAgain candidatePositionBound (by omega)
    rw [predecessorAtValue, candidateAtValue] at ordered
    exact ordered
  have predecessorRoot :=
    representative_eq_of_sigmaAt_wait invariant predecessorAt
  have predecessorOlder :
      state.core.representative predecessor <
        state.core.representative candidateRawAge := by
    rw [predecessorRoot, candidateRoot]
    exact predecessorRawOlder
  exact ⟨eventPosition, edgeCount, predecessor, eventAt, predecessorAt,
    candidateAt, predecessorOlder⟩

namespace WaitStep

/-- Minimal history/geometry carrier missing for the retained-right Wait
orientation.  It says only that the exact event at the created work boundary
can reach that work occurrence without crossing the supplied outer target. -/
private def CreatedConclusionTensorChildAnchor
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate after}
    (step : WaitStep certificate before after)
    (tagHistory : CanonicalTagHistory certificate history)
    (outer : TensorBelow) : Prop :=
  ∀ childEvent : ReservationEvent certificate,
    tagHistory.reservationLedger[step.destination.boundary]? =
        some childEvent →
      ∃ path : certificate.referenceSwitchingGraph.EdgeSimplePath,
        path.start = childEvent.search.result.left ∧
          path.finish = step.consumer.conclusion ∧
            outer.conclusion ∉ path.vertices

/-- Both orientations of the submitted Wait par connect its marked mate to
the created conclusion while avoiding any outer tensor conclusion consuming
that created occurrence.  For the omitted-right orientation, the proof uses
the one-par switching-flip path between the par premises and reference-tree
uniqueness of the outer tensor incidence. -/
private theorem consumerMate_to_createdConclusion_referencePath_avoiding_outer
    {certificate : Certificate} {before after : ReservationState}
    (step : WaitStep certificate before after)
    (correct : certificate.DeclarativelyCorrect)
    (outer : TensorBelow)
    (outerValid : outer.Valid certificate certificate.consumerIndex
      step.consumer.conclusion) :
    ∃ path : certificate.referenceSwitchingGraph.EdgeSimplePath,
      path.start = step.consumer.mate ∧
        path.finish = step.consumer.conclusion ∧
          outer.conclusion ∉ path.vertices := by
  have candidateBelowOuter :
      certificate.formulaComplexityAt step.consumer.conclusion <
        certificate.formulaComplexityAt outer.conclusion := by
    simpa [Certificate.linkConclusionComplexity] using
      outerValid.2.2.1.premise_complexity_lt_conclusion
        (premise := step.consumer.conclusion) (by
          cases sideEquation : outer.side <;>
            simp [Link.premises, TensorBelow.premise,
              TensorPremiseSide.premise, sideEquation, outerValid.2.2.2])
  have parStep : SourceLeftStep certificate step.consumer.conclusion
      step.consumer.storedLeft :=
    .par step.submitted_par
  have leftBelowCandidate :
      certificate.formulaComplexityAt step.consumer.storedLeft <
        certificate.formulaComplexityAt step.consumer.conclusion :=
    parStep.formulaComplexity_lt correct.1
  have leftNeOuterConclusion :
      step.consumer.storedLeft ≠ outer.conclusion := by
    intro same
    rw [same] at leftBelowCandidate
    omega
  have parRegion : SourceLeftRegionVertex certificate
      step.consumer.conclusion step.consumer.storedLeft :=
    .visited (.step parStep (.refl _))
  rcases sourceLeftRegionVertex_referencePath_avoiding correct.1 parRegion
      candidateBelowOuter leftNeOuterConclusion with
    ⟨leftPath, leftPathStarts, leftPathFinishes, leftPathAvoids⟩
  have innerMembership :
      Link.par step.consumer.storedLeft step.consumer.storedRight
          step.consumer.conclusion ∈ certificate.links :=
    List.mem_of_getElem? step.submitted_par
  rcases correct.parPremises_referencePath_avoids_conclusion
      innerMembership with
    ⟨premisesPath, premisesStarts, premisesFinishes,
      premisesAvoidsCandidate⟩
  have premisesAvoidsOuter : outer.conclusion ∉ premisesPath.vertices := by
    intro outerInPremises
    have outerNePremisesStart :
        outer.conclusion ≠ premisesPath.start := by
      rw [premisesStarts]
      exact leftNeOuterConclusion.symm
    have outerInTail : outer.conclusion ∈ premisesPath.vertices.tail := by
      have casesMembership :
          outer.conclusion = premisesPath.start ∨
            outer.conclusion ∈ premisesPath.vertices.tail := by
        simpa [Graph.EdgeSimplePath.vertices,
          Graph.EdgeWalk.visitedVertices] using outerInPremises
      exact casesMembership.resolve_left outerNePremisesStart
    rcases premisesPath.prefixToTailVertex outerInTail with
      ⟨prefixPath, prefixBefore, prefixAfter, prefixLast,
        premisesTraversal, prefixStarts, prefixFinishes, prefixTraversal,
        _prefixLastTarget⟩
    have outerMembership :
        Link.tensor outer.storedLeft outer.storedRight outer.conclusion ∈
          certificate.links :=
      List.mem_of_getElem? outerValid.2.1
    have outerEdges :=
      UnificationMarking.referenceSwitchingGraph_tensorEdges certificate
        outerMembership
    let activeEdge : Edge :=
      { first := step.consumer.conclusion, second := outer.conclusion }
    have activeMembership :
        activeEdge ∈ certificate.referenceSwitchingGraph.edges := by
      cases outerSide : outer.side with
      | storedLeft =>
          have candidateEq :
              step.consumer.conclusion = outer.storedLeft := by
            simpa [TensorBelow.premise, TensorPremiseSide.premise,
              outerSide] using outerValid.2.2.2
          simpa [activeEdge, candidateEq] using outerEdges.1
      | storedRight =>
          have candidateEq :
              step.consumer.conclusion = outer.storedRight := by
            simpa [TensorBelow.premise, TensorPremiseSide.premise,
              outerSide] using outerValid.2.2.2
          simpa [activeEdge, candidateEq] using outerEdges.2
    rcases List.getElem?_of_mem activeMembership with
      ⟨activeIndex, activeLookup⟩
    let activeDirected :
        certificate.referenceSwitchingGraph.DirectedEdge := {
      index := activeIndex
      edge := activeEdge
      lookup := activeLookup
      forward := true }
    have activeStarts :
        activeDirected.source = step.consumer.conclusion := by
      simp [activeDirected, activeEdge, Graph.DirectedEdge.source]
    have activeFinishes :
        activeDirected.target = outer.conclusion := by
      simp [activeDirected, activeEdge, Graph.DirectedEdge.target]
    have leftWalk :
        certificate.referenceSwitchingGraph.EdgeWalk
          step.consumer.conclusion leftPath.traversed
            step.consumer.storedLeft := by
      simpa [leftPathStarts, leftPathFinishes] using leftPath.walk
    have prefixWalk :
        certificate.referenceSwitchingGraph.EdgeWalk
          step.consumer.storedLeft prefixPath.traversed outer.conclusion := by
      simpa [prefixStarts, prefixFinishes, premisesStarts] using
        prefixPath.walk
    have alternateWalk :
        certificate.referenceSwitchingGraph.EdgeWalk
          step.consumer.conclusion
          (leftPath.traversed ++ prefixPath.traversed)
          outer.conclusion :=
      leftWalk.trans prefixWalk
    have exactAlternate :
        certificate.referenceSwitchingGraph.EdgeWalk activeDirected.source
          (leftPath.traversed ++ prefixPath.traversed)
          activeDirected.target := by
      simpa [activeStarts, activeFinishes] using alternateWalk
    apply no_alternateEdgeWalk_wait correct.referenceSwitchingTree
      activeDirected exactAlternate
    intro directed inAlternate sameIndex
    have sameEdge : directed.edge = activeDirected.edge := by
      apply Option.some.inj
      rw [← directed.lookup, ← activeDirected.lookup, sameIndex]
    have sameActiveEdge : directed.edge = activeEdge := by
      simpa [activeDirected] using sameEdge
    rcases List.mem_append.mp inAlternate with inLeft | inPrefix
    · exact
        (edgeSimplePath_edgeValues_avoid_incident_forbidden_wait leftPath
          leftPathAvoids directed inLeft) sameActiveEdge
    · have inPremises : directed ∈ premisesPath.traversed := by
        rw [prefixTraversal] at inPrefix
        rw [premisesTraversal]
        rcases List.mem_append.mp inPrefix with inBefore | atLast
        · exact List.mem_append_left _ inBefore
        · simp only [List.mem_singleton] at atLast
          subst directed
          exact List.mem_append_right _ (by simp)
      exact
        (edgeSimplePath_edgeValues_avoid_incident_first_wait premisesPath
          premisesAvoidsCandidate directed inPremises) sameActiveEdge
  cases sideEquation : step.consumer.side with
  | storedRight =>
      have mateEq : step.consumer.mate = step.consumer.storedLeft := by
        simp [ConnectiveBelow.mate, TensorPremiseSide.mate, sideEquation]
      refine ⟨leftPath.reverse, ?_, ?_, ?_⟩
      · exact (by
          change leftPath.finish = step.consumer.mate
          exact leftPathFinishes.trans mateEq.symm)
      · exact (by
          change leftPath.start = step.consumer.conclusion
          exact leftPathStarts)
      · simpa using leftPathAvoids
  | storedLeft =>
      have mateEq : step.consumer.mate = step.consumer.storedRight := by
        simp [ConnectiveBelow.mate, TensorPremiseSide.mate, sideEquation]
      rcases premisesPath.reverse.connectEraseAvoiding leftPath.reverse
          (by
            change premisesPath.start = leftPath.finish
            exact premisesStarts.trans leftPathFinishes.symm)
          (by simpa using premisesAvoidsOuter)
          (by simpa using leftPathAvoids) with
        ⟨path, pathStarts, pathFinishes, pathAvoids⟩
      refine ⟨path, ?_, ?_, pathAvoids⟩
      · exact pathStarts.trans (by
          change premisesPath.finish = step.consumer.mate
          exact premisesFinishes.trans mateEq.symm)
      · exact pathFinishes.trans (by
          change leftPath.start = step.consumer.conclusion
          exact leftPathStarts)

/-- Same-target classifier for a marked-mate future tensor.  Equal premise
orientations contradict queued-head unmarkedness; cross orientations identify
the historical selection with the current mate. -/
private theorem sameTensorConclusion_selected_eq_markedMate
    {certificate : Certificate}
    {state edgeBefore edgeAfter : ReservationState}
    (invariant : SchedulerInvariant certificate state)
    (edgeStep : NewStep certificate edgeBefore edgeAfter)
    {candidateRawAge : RawTokenAge} {candidateVertex : Vertex}
    (work : FutureWorkAt state candidateRawAge candidateVertex)
    (outer : TensorBelow)
    (outerValid :
      outer.Valid certificate certificate.consumerIndex candidateVertex)
    {selectedRawAge mateRawAge : RawTokenAge}
    (selectedMarked :
      state.core.marks[edgeStep.stackResult.vertex]? =
        some (some selectedRawAge))
    (mateMarked :
      state.core.marks[outer.mate]? = some (some mateRawAge))
    (sameConclusion : edgeStep.tensor.conclusion = outer.conclusion) :
    edgeStep.stackResult.vertex = outer.mate ∧
      edgeStep.tensor.mate = candidateVertex ∧
        selectedRawAge = mateRawAge := by
  have currentMembership :
      Link.tensor edgeStep.tensor.storedLeft edgeStep.tensor.storedRight
          edgeStep.tensor.conclusion ∈ certificate.links :=
    List.mem_of_getElem? edgeStep.tensorValid.2.1
  have outerMembership :
      Link.tensor outer.storedLeft outer.storedRight outer.conclusion ∈
        certificate.links :=
    List.mem_of_getElem? outerValid.2.1
  have sameLink :=
    UnificationState.StructurallyWellFormed.producerLink_unique
      (conclusion := edgeStep.tensor.conclusion) invariant.structural
      currentMembership (by simp [Link.produces])
      outerMembership (by simp [Link.produces, sameConclusion])
  injection sameLink with leftEq rightEq _conclusionEq
  have candidateUnmarked :
      state.core.marks[candidateVertex]? = some none :=
    invariant.queued_vertices_unmarked candidateVertex work.mem_queued
  have currentPremise := edgeStep.tensorValid.2.2.2
  have outerPremise := outerValid.2.2.2
  cases currentSide : edgeStep.tensor.side <;>
      cases outerSide : outer.side
  · have candidateEqSelected :
        candidateVertex = edgeStep.stackResult.vertex := by
      simp [TensorBelow.premise, TensorPremiseSide.premise,
        currentSide] at currentPremise
      simp [TensorBelow.premise, TensorPremiseSide.premise,
        outerSide] at outerPremise
      exact outerPremise.trans (leftEq.symm.trans currentPremise.symm)
    rw [candidateEqSelected, selectedMarked] at candidateUnmarked
    simp at candidateUnmarked
  · have mateEq : outer.mate = edgeStep.stackResult.vertex := by
      simp [TensorBelow.mate, TensorPremiseSide.mate, outerSide]
      simp [TensorBelow.premise, TensorPremiseSide.premise,
        currentSide] at currentPremise
      exact leftEq.symm.trans currentPremise.symm
    simp [TensorBelow.premise, TensorPremiseSide.premise,
      outerSide] at outerPremise
    constructor
    · exact mateEq.symm
    · constructor
      · simp [TensorBelow.mate, TensorPremiseSide.mate, currentSide]
        exact rightEq.trans outerPremise.symm
      · rw [mateEq] at mateMarked
        exact Option.some.inj
          (Option.some.inj (selectedMarked.symm.trans mateMarked))
  · have mateEq : outer.mate = edgeStep.stackResult.vertex := by
      simp [TensorBelow.mate, TensorPremiseSide.mate, outerSide]
      simp [TensorBelow.premise, TensorPremiseSide.premise,
        currentSide] at currentPremise
      exact rightEq.symm.trans currentPremise.symm
    simp [TensorBelow.premise, TensorPremiseSide.premise,
      outerSide] at outerPremise
    constructor
    · exact mateEq.symm
    · constructor
      · simp [TensorBelow.mate, TensorPremiseSide.mate, currentSide]
        exact leftEq.trans outerPremise.symm
      · rw [mateEq] at mateMarked
        exact Option.some.inj
          (Option.some.inj (selectedMarked.symm.trans mateMarked))
  · have candidateEqSelected :
        candidateVertex = edgeStep.stackResult.vertex := by
      simp [TensorBelow.premise, TensorPremiseSide.premise,
        currentSide] at currentPremise
      simp [TensorBelow.premise, TensorPremiseSide.premise,
        outerSide] at outerPremise
      exact outerPremise.trans (rightEq.symm.trans currentPremise.symm)
    rw [candidateEqSelected, selectedMarked] at candidateUnmarked
    simp at candidateUnmarked

/-- The reservation event at a Wait destination boundary has an exact path
to the created conclusion avoiding the conclusion of any outer tensor
candidate.  The omitted-right par orientation is discharged by the
one-occurrence switching-flip theorem above. -/
private theorem createdConclusion_destinationAnchor
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate after}
    (step : WaitStep certificate before after)
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate after)
    (outer : TensorBelow)
    (outerValid : outer.Valid certificate certificate.consumerIndex
      step.consumer.conclusion) :
    ∃ (event : ReservationEvent certificate)
        (path : certificate.referenceSwitchingGraph.EdgeSimplePath),
      tagHistory.reservationLedger[step.destination.boundary]? = some event ∧
        path.start = event.search.result.left ∧
        path.finish = step.consumer.conclusion ∧
        outer.conclusion ∉ path.vertices := by
  rcases step.destination.exact with
    ⟨payload, _initialized, updated, _marks, _nextAge, sigmaEq, _ready,
      coreEq, _tags⟩
  have work : FutureWorkAt after step.destination.boundary
      step.consumer.conclusion :=
    FutureWorkAt.waiting updated (by simp)
  have boundaryBound :
      step.destination.boundary < after.stack.nextAge :=
    work.rawAge_lt_nextAge invariant
  rcases tagHistory.reservationLedger_eventAtRawAge
      step.destination.boundary boundaryBound with
    ⟨event, eventLookup, eventRawAge⟩
  have eventMembership : event ∈ tagHistory.reservationLedger :=
    List.mem_of_getElem? eventLookup
  rcases tagHistory.reservationLedger_axiomEndpoints_accounted
      correct.1 eventMembership with
    ⟨eventComponent, _eventUsed, _eventForest, eventOwned,
      eventComponentLookup, eventDerivation, _eventLink, eventWitness,
      eventAccounted, eventLeftOwned, _eventRightOwned⟩
  have mateMarkedMiddle :
      step.prepared.after.core.marks[step.consumer.mate]? =
        some (some step.mateRawAge) :=
    step.mate_marked
  have mateMarked :
      after.core.marks[step.consumer.mate]? =
        some (some step.mateRawAge) := by
    rw [coreEq]
    exact mateMarkedMiddle
  rcases SchedulerInvariant.exactMarkedOccurrenceOwner invariant mateMarked with
    ⟨ownerRawAge, ownerIndex, ownerComponent, _ownerUsed, ownerOwned,
      ownerMarked, ownerRepresentative, ownerLookup, ownerWitness,
      ownerAccounted, mateOwned⟩
  have ownerRawAgeEq : ownerRawAge = step.mateRawAge := by
    exact Option.some.inj
      (Option.some.inj (ownerMarked.symm.trans mateMarked))
  subst ownerRawAge
  have afterBoundaryLookup :
      sigmaBoundary? after.stack.sigma step.mateRawAge =
        some step.destination.boundary := by
    rw [sigmaEq]
    exact step.destination.boundary_eq
  have mateAgeBound : step.mateRawAge < after.stack.nextAge := by
    have stackMarked :
        after.stack.marks[step.consumer.mate]? =
          some (some step.mateRawAge) := by
      rw [← invariant.realizesSigma.marks_eq]
      exact mateMarked
    exact invariant.stack_wellShaped.assigned_age_bound
      step.consumer.mate step.mateRawAge stackMarked
  have mateRepresentative :
      after.core.representative step.mateRawAge =
        step.destination.boundary := by
    have realized :=
      invariant.realizesSigma.representative_eq_boundary mateAgeBound
    exact Option.some.inj (realized.symm.trans afterBoundaryLookup)
  have ownerIndexEq : ownerIndex = step.destination.boundary :=
    ownerRepresentative.symm.trans mateRepresentative
  have boundaryRoot :
      after.core.representative step.destination.boundary =
        step.destination.boundary :=
    work.representative_eq_rawAge invariant
  have eventComponentLookupAtBoundary :
      after.core.components[step.destination.boundary]? =
        some (some eventComponent) := by
    simpa [eventRawAge, boundaryRoot] using eventComponentLookup
  have ownerLookupAtBoundary :
      after.core.components[step.destination.boundary]? =
        some (some ownerComponent) := by
    simpa [ownerIndexEq] using ownerLookup
  have componentEq : ownerComponent = eventComponent := by
    exact Option.some.inj
      (Option.some.inj
        (ownerLookupAtBoundary.symm.trans eventComponentLookupAtBoundary))
  subst ownerComponent
  have ownedEq : ownerOwned = eventOwned :=
    Certificate.OccurrenceDerivation.owned_unique correct.1
      ownerWitness.derivation eventDerivation
  have mateEventOwned : step.consumer.mate ∈ eventOwned := by
    rw [← ownedEq]
    exact mateOwned
  rcases eventWitness.referencePath_within_owned eventLeftOwned mateEventOwned with
    ⟨componentPath, componentStarts, componentFinishes, componentWithin⟩
  have outerNotEventOwned : outer.conclusion ∉ eventOwned :=
    tensorConclusion_not_owned_of_futureWork invariant work outer outerValid
      eventComponentLookupAtBoundary (by
        simpa [eventRawAge, boundaryRoot] using eventAccounted)
  have componentAvoids : outer.conclusion ∉ componentPath.vertices := by
    intro inPath
    exact outerNotEventOwned (componentWithin outer.conclusion inPath)
  rcases step.consumerMate_to_createdConclusion_referencePath_avoiding_outer
      correct outer outerValid with
    ⟨parPath, parStarts, parFinishes, parAvoids⟩
  rcases componentPath.connectEraseAvoiding parPath
      (componentFinishes.trans parStarts.symm)
      componentAvoids parAvoids with
    ⟨path, pathStarts, pathFinishes, pathAvoids⟩
  exact ⟨event, path, eventLookup,
    pathStarts.trans componentStarts,
    pathFinishes.trans parFinishes, pathAvoids⟩

/-- Every Wait orientation satisfies the exact child-anchor carrier. -/
private theorem createdConclusionTensorChildAnchor
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate after}
    (step : WaitStep certificate before after)
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate after)
    (outer : TensorBelow)
    (outerValid : outer.Valid certificate certificate.consumerIndex
      step.consumer.conclusion) :
    CreatedConclusionTensorChildAnchor step tagHistory outer := by
  rcases step.createdConclusion_destinationAnchor tagHistory
      correct invariant outer outerValid with
    ⟨anchorEvent, anchorPath, anchorLookup, anchorStarts, anchorFinishes,
      anchorAvoids⟩
  intro childEvent childLookup
  have childEq : childEvent = anchorEvent := by
    exact Option.some.inj (childLookup.symm.trans anchorLookup)
  subst childEvent
  exact ⟨anchorPath, anchorStarts, anchorFinishes, anchorAvoids⟩

/-- Generic adjacent commitment avoidance for a future tensor whose mate may
already be marked.  The historical tensor-target inequality is explicit, so
no raw-unmarked-mate premise is involved. -/
private theorem commitmentEdge_referencePath_avoiding_futureTensor_of_different
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (invariant : SchedulerInvariant certificate state)
    {candidateRawAge : RawTokenAge} {candidateVertex : Vertex}
    (work : FutureWorkAt state candidateRawAge candidateVertex)
    (outer : TensorBelow)
    (outerValid :
      outer.Valid certificate certificate.consumerIndex candidateVertex)
    {position parent child : RawTokenAge}
    (parentAt : state.stack.sigma[position]? = some parent)
    (childAt : state.stack.sigma[position + 1]? = some child)
    (different : ∀ {edgeBefore edgeAfter : ReservationState}
      (edgeStep : NewStep certificate edgeBefore edgeAfter),
      tagHistory.reservationLedger[child]? =
          some (ReservationEvent.new edgeStep) →
        edgeStep.tensor.conclusion ≠ outer.conclusion)
    (childUntouched : ∀ {event : ReservationEvent certificate},
      event ∈ tagHistory.reservationLedger → event.rawAge = child →
        ¬ event.Touched outer.conclusion) :
    tagHistory.CommitmentEdgeTargetAvoidingPath parent child
      outer.conclusion := by
  rcases tagHistory.commitmentEdge_referencePath invariant parentAt childAt with
    ⟨edgeBefore, edgeAfter, edgeStep, parentEvent, parentComponent,
      childComponent, parentEventUsed, parentForestUsed, parentOwned,
      childEventUsed, childForestUsed, childOwned, parentAnchor,
      _oldCommittedPath, childAnchor, _oldCanonicalPath, parentLookup,
      edgeChildLookup, _parentRawAge, _parentEq, childEq, _selectedMarked,
      parentComponentLookup, _parentDerivation, _parentLink, _parentWitness,
      parentAccounted, selectedOwned, _parentLeftOwned, childComponentLookup,
      _childDerivation, _childLink, _childWitness, childAccounted, _reachedOwned,
      parentAnchorStarts, parentAnchorFinishes, parentAnchorWithin,
      _oldCommittedStarts, _oldCommittedFinishes, childAnchorStarts,
      childAnchorFinishes, childAnchorWithin, _oldCanonicalStarts,
      _oldCanonicalFinishes, _reachedEndpoint⟩
  have targetNotParentOwned : outer.conclusion ∉ parentOwned :=
    tensorConclusion_not_owned_of_futureWork invariant work outer outerValid
      parentComponentLookup parentAccounted
  have targetNotChildOwned : outer.conclusion ∉ childOwned :=
    tensorConclusion_not_owned_of_futureWork invariant work outer outerValid
      childComponentLookup childAccounted
  have selectedNe : edgeStep.stackResult.vertex ≠ outer.conclusion := by
    intro same
    apply targetNotParentOwned
    simpa [same] using selectedOwned
  have ownConclusionNe :
      edgeStep.tensor.conclusion ≠ outer.conclusion :=
    different edgeStep edgeChildLookup
  have parentAvoids : outer.conclusion ∉ parentAnchor.vertices := by
    intro membership
    exact targetNotParentOwned
      (parentAnchorWithin outer.conclusion membership)
  have reversedParentAvoids :
      outer.conclusion ∉ parentAnchor.reverse.vertices := by
    simpa using parentAvoids
  have childAvoids : outer.conclusion ∉ childAnchor.vertices := by
    intro membership
    exact targetNotChildOwned
      (childAnchorWithin outer.conclusion membership)
  rcases selectedToReachedReferencePath_avoiding_wait invariant.structural
      edgeStep selectedNe ownConclusionNe
        (childUntouched (List.mem_of_getElem? edgeChildLookup)
          childEq.symm) with
    ⟨middlePath, middleStarts, middleFinishes, middleAvoids⟩
  rcases Graph.EdgeSimplePath.connectEraseAvoiding parentAnchor.reverse
      middlePath (by
        change parentAnchor.start = middlePath.start
        rw [parentAnchorStarts, middleStarts])
      reversedParentAvoids middleAvoids with
    ⟨prefixPath, prefixStarts, prefixFinishes, prefixAvoids⟩
  rcases Graph.EdgeSimplePath.connectEraseAvoiding prefixPath childAnchor
      (prefixFinishes.trans
        (middleFinishes.trans childAnchorStarts.symm))
      prefixAvoids childAvoids with
    ⟨path, pathStarts, pathFinishes, pathAvoids⟩
  refine ⟨parentEvent, ReservationEvent.new edgeStep, path, parentLookup,
    edgeChildLookup, ?_, ?_, pathAvoids⟩
  · exact pathStarts.trans (prefixStarts.trans (by
      change parentAnchor.finish = parentEvent.search.result.left
      exact parentAnchorFinishes))
  · exact pathFinishes.trans childAnchorFinishes

/-- An event and the event at its current representative are joined inside one
final owned component, avoiding any unproduced future tensor conclusion. -/
private theorem eventLeft_to_representativeEvent_referencePath_avoiding_futureTensor
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate state)
    {candidateRawAge : RawTokenAge} {candidateVertex : Vertex}
    (work : FutureWorkAt state candidateRawAge candidateVertex)
    (outer : TensorBelow)
    (outerValid :
      outer.Valid certificate certificate.consumerIndex candidateVertex)
    {event representativeEvent : ReservationEvent certificate}
    (eventMembership : event ∈ tagHistory.reservationLedger)
    (representativeLookup :
      tagHistory.reservationLedger[state.core.representative event.rawAge]? =
        some representativeEvent) :
    ∃ path : certificate.referenceSwitchingGraph.EdgeSimplePath,
      path.start = event.search.result.left ∧
        path.finish = representativeEvent.search.result.left ∧
          outer.conclusion ∉ path.vertices := by
  have eventRawAgeBound : event.rawAge < state.core.parents.size := by
    rw [invariant.realizesSigma.horizon_eq]
    have mapped :
        event.rawAge ∈
          tagHistory.reservationLedger.map ReservationEvent.rawAge :=
      List.mem_map.mpr ⟨event, eventMembership, rfl⟩
    rw [tagHistory.reservationLedger_rawAges] at mapped
    simpa using mapped
  have representativeRoot :
      state.core.representative
          (state.core.representative event.rawAge) =
        state.core.representative event.rawAge :=
    UnificationState.OrderedParents.representative_idempotent
      invariant.core_orderedParents eventRawAgeBound
  have representativeMembership :
      representativeEvent ∈ tagHistory.reservationLedger :=
    List.mem_of_getElem? representativeLookup
  have representativeRawAge :
      representativeEvent.rawAge =
        state.core.representative event.rawAge :=
    reservationEvent_rawAge_eq_of_lookup_wait tagHistory
      representativeLookup
  rcases tagHistory.reservationLedger_axiomEndpoints_accounted
      correct.1 eventMembership with
    ⟨eventComponent, _eventUsed, _eventForest, eventOwned,
      eventComponentLookup, eventDerivation, _eventLink, eventWitness,
      eventAccounted, eventLeftOwned, _eventRightOwned⟩
  rcases tagHistory.reservationLedger_axiomEndpoints_accounted
      correct.1 representativeMembership with
    ⟨representativeComponent, _representativeUsed,
      _representativeForest, representativeOwned,
      representativeComponentLookup, representativeDerivation,
      _representativeLink, _representativeWitness,
      _representativeAccounted, representativeLeftOwned,
      _representativeRightOwned⟩
  have representativeComponentLookupAtEvent :
      state.core.components[state.core.representative event.rawAge]? =
        some (some representativeComponent) := by
    simpa [representativeRawAge, representativeRoot] using
      representativeComponentLookup
  have componentEq : representativeComponent = eventComponent := by
    exact Option.some.inj
      (Option.some.inj
        (representativeComponentLookupAtEvent.symm.trans
          eventComponentLookup))
  subst representativeComponent
  have ownedEq : representativeOwned = eventOwned :=
    Certificate.OccurrenceDerivation.owned_unique correct.1
      representativeDerivation eventDerivation
  have representativeLeftEventOwned :
      representativeEvent.search.result.left ∈ eventOwned := by
    rw [← ownedEq]
    exact representativeLeftOwned
  rcases eventWitness.referencePath_within_owned eventLeftOwned
      representativeLeftEventOwned with
    ⟨path, pathStarts, pathFinishes, pathWithin⟩
  have conclusionNotEventOwned : outer.conclusion ∉ eventOwned :=
    tensorConclusion_not_owned_of_futureWork invariant work outer outerValid
      eventComponentLookup eventAccounted
  refine ⟨path, pathStarts, pathFinishes, ?_⟩
  intro inPath
  exact conclusionNotEventOwned
    (pathWithin outer.conclusion inPath)

/-- In the stored-right orientation, touching the outer conclusion puts the
event's left endpoint in the source-left region of the marked mate. -/
private theorem touchedEvent_mateAnchor_of_outerStoredRight
    {certificate : Certificate}
    (correct : certificate.DeclarativelyCorrect)
    (outer : TensorBelow) {candidateVertex : Vertex}
    (outerValid :
      outer.Valid certificate certificate.consumerIndex candidateVertex)
    (event : ReservationEvent certificate)
    (touched : event.Touched outer.conclusion)
    (outerStoredRight : outer.side = .storedRight) :
    ∃ path : certificate.referenceSwitchingGraph.EdgeSimplePath,
      path.start = outer.mate ∧
        path.finish = event.search.result.left ∧
          outer.conclusion ∉ path.vertices := by
  have storedLeftTouched : event.Touched outer.storedLeft :=
    reservationEvent_touched_tensor_storedLeft_wait correct.1 event
      outerValid touched
  have mateTouched : event.Touched outer.mate := by
    simpa [TensorBelow.mate, TensorPremiseSide.mate, outerStoredRight] using
      storedLeftTouched
  have mateRegion :
      SourceLeftRegionVertex certificate outer.mate
        event.search.result.left :=
    event.leftEndpoint_sourceLeftRegion_of_touched mateTouched
  have mateBelowConclusion :
      certificate.formulaComplexityAt outer.mate <
        certificate.formulaComplexityAt outer.conclusion := by
    simpa [Certificate.linkConclusionComplexity] using
      outerValid.2.2.1.premise_complexity_lt_conclusion
        (premise := outer.mate) (by
          simp [Link.premises, TensorBelow.mate, TensorPremiseSide.mate,
            outerStoredRight])
  have eventLeftNeConclusion :
      event.search.result.left ≠ outer.conclusion := by
    intro same
    exact correct.1.axiomEndpoint_ne_connectiveConclusion
      (List.mem_of_getElem? event.search.result.exactLink) (Or.inl rfl)
      (List.mem_of_getElem? outerValid.2.1)
      (by simpa [Link.produces] using same.symm)
  exact sourceLeftRegionVertex_referencePath_avoiding correct.1 mateRegion
    mateBelowConclusion eventLeftNeConclusion

/-- If the equal-boundary child actually touches a stored-left outer target,
the callback trace itself contradicts a mate-to-parent prefix.  The historical
target inequality is explicit; no candidate-mate unmarkedness is used. -/
private theorem touchedFinalChild_conflicts_of_outerStoredLeft_different
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate state)
    {candidateRawAge : RawTokenAge} {candidateVertex : Vertex}
    (work : FutureWorkAt state candidateRawAge candidateVertex)
    (outer : TensorBelow)
    (outerValid :
      outer.Valid certificate certificate.consumerIndex candidateVertex)
    {position parentAge : RawTokenAge}
    (parentAt : state.stack.sigma[position]? = some parentAge)
    (childAt :
      state.stack.sigma[position + 1]? = some candidateRawAge)
    {parentEvent childEvent : ReservationEvent certificate}
    (parentLookup :
      tagHistory.reservationLedger[parentAge]? = some parentEvent)
    (prefixPath : certificate.referenceSwitchingGraph.EdgeSimplePath)
    (prefixStarts : prefixPath.start = outer.mate)
    (prefixFinishes :
      prefixPath.finish = parentEvent.search.result.left)
    (prefixAvoids : outer.conclusion ∉ prefixPath.vertices)
    (childMembership : childEvent ∈ tagHistory.reservationLedger)
    (childAge : childEvent.rawAge = candidateRawAge)
    (childTouched : childEvent.Touched outer.conclusion)
    (outerStoredLeft : outer.side = .storedLeft)
    (different : ∀ {edgeBefore edgeAfter : ReservationState}
      (edgeStep : NewStep certificate edgeBefore edgeAfter),
      tagHistory.reservationLedger[candidateRawAge]? =
          some (ReservationEvent.new edgeStep) →
        edgeStep.tensor.conclusion ≠ outer.conclusion) :
    False := by
  rcases tagHistory.commitmentEdge_referencePath invariant parentAt childAt with
    ⟨edgeBefore, edgeAfter, edgeStep, edgeParentEvent, parentComponent,
      childComponent, parentEventUsed, parentForestUsed, parentOwned,
      childEventUsed, childForestUsed, childOwned, parentAnchor,
      _oldCommittedPath, childAnchor, _oldCanonicalPath, edgeParentLookup,
      edgeChildLookup, _parentRawAge, _parentEq, _childEq, _selectedMarked,
      parentComponentLookup, _parentDerivation, _parentLink, _parentWitness,
      parentAccounted, _selectedOwned, _parentLeftOwned,
      _childComponentLookup, _childDerivation, _childLink, _childWitness,
      _childAccounted, _reachedOwned, parentAnchorStarts,
      parentAnchorFinishes, parentAnchorWithin, _oldCommittedStarts,
      _oldCommittedFinishes, _childAnchorStarts, _childAnchorFinishes,
      _childAnchorWithin, _oldCanonicalStarts, _oldCanonicalFinishes,
      _reachedEndpoint⟩
  have edgeParentEq : edgeParentEvent = parentEvent := by
    exact Option.some.inj (edgeParentLookup.symm.trans parentLookup)
  subst edgeParentEvent
  have callbackLookup :
      tagHistory.reservationLedger[candidateRawAge]? = some childEvent :=
    reservationLedger_lookup_of_mem_rawAge_wait tagHistory
      childMembership childAge
  have callbackEventEq : childEvent = ReservationEvent.new edgeStep := by
    exact Option.some.inj (callbackLookup.symm.trans edgeChildLookup)
  subst childEvent
  have conclusionInTrace : outer.conclusion ∈ edgeStep.search.trace := by
    change edgeStep.search.Touched outer.conclusion at childTouched
    rcases childTouched with inTrace | leftEq | rightEq
    · exact inTrace
    · exact False.elim
        (invariant.structural.axiomEndpoint_ne_connectiveConclusion
          (List.mem_of_getElem? edgeStep.search.exactLink) (Or.inl rfl)
          (List.mem_of_getElem? outerValid.2.1)
          (by simpa [Link.produces] using leftEq))
    · exact False.elim
        (invariant.structural.axiomEndpoint_ne_connectiveConclusion
          (List.mem_of_getElem? edgeStep.search.exactLink) (Or.inr rfl)
          (List.mem_of_getElem? outerValid.2.1)
          (by simpa [Link.produces] using rightEq))
  have callbackReachable :
      SourceLeftReachable certificate edgeStep.tensor.mate
        outer.conclusion :=
    edgeStep.route.chain.reachable_of_head_mem
      edgeStep.route.traceHead conclusionInTrace
  have mateBelowConclusion :
      certificate.formulaComplexityAt outer.mate <
        certificate.formulaComplexityAt outer.conclusion := by
    simpa [Certificate.linkConclusionComplexity] using
      outerValid.2.2.1.premise_complexity_lt_conclusion
        (premise := outer.mate) (by
          simp [Link.premises, TensorBelow.mate, TensorPremiseSide.mate,
            outerStoredLeft])
  rcases sourceLeftReachable_referenceWalk_avoiding_upEdge_wait
      correct.1 callbackReachable mateBelowConclusion with
    ⟨callbackTraversal, callbackWalk, callbackAvoids⟩
  have conclusionNotParentOwned : outer.conclusion ∉ parentOwned :=
    tensorConclusion_not_owned_of_futureWork invariant work outer outerValid
      parentComponentLookup parentAccounted
  have parentAnchorAvoids :
      outer.conclusion ∉ parentAnchor.vertices := by
    intro inAnchor
    exact conclusionNotParentOwned
      (parentAnchorWithin outer.conclusion inAnchor)
  have reversedParentAnchorAvoids :
      outer.conclusion ∉ parentAnchor.reverse.vertices := by
    simpa using parentAnchorAvoids
  have ownConclusionNe :
      edgeStep.tensor.conclusion ≠ outer.conclusion :=
    different edgeStep edgeChildLookup
  rcases tensorBelow_referenceWalk_avoiding_conclusionEdge_wait
      edgeStep.tensorValid (lower := outer.mate) ownConclusionNe with
    ⟨tensorTraversal, tensorWalk, tensorAvoids⟩
  have prefixWalk :
      certificate.referenceSwitchingGraph.EdgeWalk outer.mate
        prefixPath.traversed parentEvent.search.result.left := by
    simpa [prefixStarts, prefixFinishes] using prefixPath.walk
  have parentWalk :
      certificate.referenceSwitchingGraph.EdgeWalk
        parentEvent.search.result.left parentAnchor.reverse.traversed
          edgeStep.stackResult.vertex := by
    have reversedWalk := parentAnchor.reverse.walk
    change certificate.referenceSwitchingGraph.EdgeWalk
      parentAnchor.finish parentAnchor.reverse.traversed parentAnchor.start
        at reversedWalk
    rw [parentAnchorFinishes, parentAnchorStarts] at reversedWalk
    exact reversedWalk
  have alternateWalk :=
    (((prefixWalk.trans parentWalk).trans tensorWalk).trans
      callbackWalk)
  have tensorMembership :
      Link.tensor outer.storedLeft outer.storedRight outer.conclusion ∈
        certificate.links :=
    List.mem_of_getElem? outerValid.2.1
  have mateIsRight : outer.mate = outer.storedRight := by
    simp [TensorBelow.mate, TensorPremiseSide.mate, outerStoredLeft]
  apply no_referenceAlternateToTensorConclusion_wait correct tensorMembership
    (by simpa [mateIsRight] using alternateWalk)
  intro directed directedMembership
  rcases List.mem_append.mp directedMembership with inPrefix | afterPrefix
  · exact edgeSimplePath_edgeValues_avoid_incident_forbidden_wait
      prefixPath prefixAvoids directed inPrefix
  · rcases List.mem_append.mp afterPrefix with inParent | afterParent
    · exact edgeSimplePath_edgeValues_avoid_incident_forbidden_wait
        parentAnchor.reverse reversedParentAnchorAvoids directed inParent
    · rcases List.mem_append.mp afterParent with inTensor | inCallback
      · simpa [mateIsRight] using tensorAvoids directed inTensor
      · simpa [mateIsRight] using callbackAvoids directed inCallback

/-- In the stored-right outer orientation, an equal-boundary child touch gives
a mate-to-child path.  Any supplied child-to-candidate anchor then forms the
forbidden tensor bypass. -/
private theorem touchedFinalChild_conflicts_of_outerStoredRight_childAnchor
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    {candidateRawAge : RawTokenAge} {candidateVertex : Vertex}
    (outer : TensorBelow)
    (outerValid :
      outer.Valid certificate certificate.consumerIndex candidateVertex)
    {childEvent : ReservationEvent certificate}
    (childLookup :
      tagHistory.reservationLedger[candidateRawAge]? = some childEvent)
    (childTouched : childEvent.Touched outer.conclusion)
    (outerStoredRight : outer.side = .storedRight)
    (childAnchor : ∀ event : ReservationEvent certificate,
      tagHistory.reservationLedger[candidateRawAge]? = some event →
        ∃ path : certificate.referenceSwitchingGraph.EdgeSimplePath,
          path.start = event.search.result.left ∧
            path.finish = candidateVertex ∧
              outer.conclusion ∉ path.vertices) :
    False := by
  have storedLeftTouched : childEvent.Touched outer.storedLeft :=
    reservationEvent_touched_tensor_storedLeft_wait correct.1 childEvent
      outerValid childTouched
  have mateTouched : childEvent.Touched outer.mate := by
    simpa [TensorBelow.mate, TensorPremiseSide.mate, outerStoredRight] using
      storedLeftTouched
  have mateRegion :
      SourceLeftRegionVertex certificate outer.mate
        childEvent.search.result.left :=
    childEvent.leftEndpoint_sourceLeftRegion_of_touched mateTouched
  have mateBelowConclusion :
      certificate.formulaComplexityAt outer.mate <
        certificate.formulaComplexityAt outer.conclusion := by
    simpa [Certificate.linkConclusionComplexity] using
      outerValid.2.2.1.premise_complexity_lt_conclusion
        (premise := outer.mate) (by
          simp [Link.premises, TensorBelow.mate, TensorPremiseSide.mate,
            outerStoredRight])
  have eventLeftNeConclusion :
      childEvent.search.result.left ≠ outer.conclusion := by
    intro same
    exact correct.1.axiomEndpoint_ne_connectiveConclusion
      (List.mem_of_getElem? childEvent.search.result.exactLink) (Or.inl rfl)
      (List.mem_of_getElem? outerValid.2.1)
      (by simpa [Link.produces] using same.symm)
  rcases sourceLeftRegionVertex_referencePath_avoiding correct.1 mateRegion
      mateBelowConclusion eventLeftNeConclusion with
    ⟨matePath, mateStarts, mateFinishes, mateAvoids⟩
  rcases childAnchor childEvent childLookup with
    ⟨anchorPath, anchorStarts, anchorFinishes, anchorAvoids⟩
  rcases matePath.connectEraseAvoiding anchorPath
      (mateFinishes.trans anchorStarts.symm) mateAvoids anchorAvoids with
    ⟨bypass, bypassStarts, bypassFinishes, bypassAvoids⟩
  have tensorMembership :
      Link.tensor outer.storedLeft outer.storedRight outer.conclusion ∈
        certificate.links :=
    List.mem_of_getElem? outerValid.2.1
  have candidateIsRight : candidateVertex = outer.storedRight := by
    simpa [TensorBelow.premise, TensorPremiseSide.premise,
      outerStoredRight] using outerValid.2.2.2
  have mateIsLeft : outer.mate = outer.storedLeft := by
    simp [TensorBelow.mate, TensorPremiseSide.mate, outerStoredRight]
  apply referenceAcyclic_no_tensorBypass correct.1
    correct.referenceSwitchingTree.acyclic tensorMembership bypass
  · exact bypassStarts.trans (mateStarts.trans mateIsLeft)
  · exact bypassFinishes.trans (anchorFinishes.trans candidateIsRight)
  · exact bypassAvoids

private theorem commitmentPath_conflict_early
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    {candidateRawAge : RawTokenAge} {candidateVertex : Vertex}
    (outer : TensorBelow)
    (outerValid :
      outer.Valid certificate certificate.consumerIndex candidateVertex)
    {parentEvent : ReservationEvent certificate}
    {parentAge : RawTokenAge}
    (parentLookup :
      tagHistory.reservationLedger[parentAge]? = some parentEvent)
    (prefixPath : certificate.referenceSwitchingGraph.EdgeSimplePath)
    (prefixStarts : prefixPath.start = outer.mate)
    (prefixFinishes :
      prefixPath.finish = parentEvent.search.result.left)
    (prefixAvoids : outer.conclusion ∉ prefixPath.vertices)
    (suffix : tagHistory.CommitmentEdgeTargetAvoidingPath
      parentAge candidateRawAge outer.conclusion)
    (childAnchor : ∀ childEvent : ReservationEvent certificate,
      tagHistory.reservationLedger[candidateRawAge]? = some childEvent →
        ∃ path : certificate.referenceSwitchingGraph.EdgeSimplePath,
          path.start = childEvent.search.result.left ∧
            path.finish = candidateVertex ∧
              outer.conclusion ∉ path.vertices) :
    False := by
  rcases suffix with
    ⟨suffixParent, childEvent, suffixPath, suffixParentLookup,
      childLookup, suffixStarts, suffixFinishes, suffixAvoids⟩
  have suffixParentEq : suffixParent = parentEvent := by
    exact Option.some.inj (suffixParentLookup.symm.trans parentLookup)
  subst suffixParent
  rcases childAnchor childEvent childLookup with
    ⟨anchorPath, anchorStarts, anchorFinishes, anchorAvoids⟩
  rcases prefixPath.connectEraseAvoiding suffixPath
      (prefixFinishes.trans suffixStarts.symm)
      prefixAvoids suffixAvoids with
    ⟨first, firstStarts, firstFinishes, firstAvoids⟩
  rcases first.connectEraseAvoiding anchorPath
      (firstFinishes.trans (suffixFinishes.trans anchorStarts.symm))
      firstAvoids anchorAvoids with
    ⟨bypass, bypassStarts, bypassFinishes, bypassAvoids⟩
  have tensorMembership :
      Link.tensor outer.storedLeft outer.storedRight outer.conclusion ∈
        certificate.links :=
    List.mem_of_getElem? outerValid.2.1
  have combinedStarts : bypass.start = outer.mate :=
    bypassStarts.trans (firstStarts.trans prefixStarts)
  have combinedFinishes : bypass.finish = candidateVertex :=
    bypassFinishes.trans anchorFinishes
  have premise := outerValid.2.2.2
  cases sideEquation : outer.side with
  | storedLeft =>
      have candidateIsLeft : candidateVertex = outer.storedLeft := by
        simpa [TensorBelow.premise, TensorPremiseSide.premise,
          sideEquation] using premise
      have mateIsRight : outer.mate = outer.storedRight := by
        simp [TensorBelow.mate, TensorPremiseSide.mate, sideEquation]
      apply referenceAcyclic_no_tensorBypass correct.1
        correct.referenceSwitchingTree.acyclic tensorMembership bypass.reverse
      · exact combinedFinishes.trans candidateIsLeft
      · exact combinedStarts.trans mateIsRight
      · simpa using bypassAvoids
  | storedRight =>
      have candidateIsRight : candidateVertex = outer.storedRight := by
        simpa [TensorBelow.premise, TensorPremiseSide.premise,
          sideEquation] using premise
      have mateIsLeft : outer.mate = outer.storedLeft := by
        simp [TensorBelow.mate, TensorPremiseSide.mate, sideEquation]
      apply referenceAcyclic_no_tensorBypass correct.1
        correct.referenceSwitchingTree.acyclic tensorMembership bypass
      · exact combinedStarts.trans mateIsLeft
      · exact combinedFinishes.trans candidateIsRight
      · exact bypassAvoids

/-- Complete classification of the final adjacent commitment once a child
anchor is supplied.  Same target identifies the parent with the marked mate;
different target closes through either an avoiding path or the exact callback
touch geometry. -/
private theorem finalCommitment_parent_eq_mateRawAge_of_childAnchor
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate state)
    {candidateRawAge : RawTokenAge} {candidateVertex : Vertex}
    (work : FutureWorkAt state candidateRawAge candidateVertex)
    (outer : TensorBelow)
    (outerValid :
      outer.Valid certificate certificate.consumerIndex candidateVertex)
    {mateRawAge : RawTokenAge}
    (mateMarked :
      state.core.marks[outer.mate]? = some (some mateRawAge))
    {position parent : RawTokenAge}
    (parentAt : state.stack.sigma[position]? = some parent)
    (childAt :
      state.stack.sigma[position + 1]? = some candidateRawAge)
    {parentEvent : ReservationEvent certificate}
    (parentLookup :
      tagHistory.reservationLedger[parent]? = some parentEvent)
    (prefixPath : certificate.referenceSwitchingGraph.EdgeSimplePath)
    (prefixStarts : prefixPath.start = outer.mate)
    (prefixFinishes :
      prefixPath.finish = parentEvent.search.result.left)
    (prefixAvoids : outer.conclusion ∉ prefixPath.vertices)
    (childAnchor : ∀ childEvent : ReservationEvent certificate,
      tagHistory.reservationLedger[candidateRawAge]? = some childEvent →
        ∃ path : certificate.referenceSwitchingGraph.EdgeSimplePath,
          path.start = childEvent.search.result.left ∧
            path.finish = candidateVertex ∧
              outer.conclusion ∉ path.vertices) :
    parent = mateRawAge := by
  classical
  rcases tagHistory.commitmentEdge_referencePath invariant parentAt childAt with
    ⟨edgeBefore, edgeAfter, edgeStep, edgeParentEvent, parentComponent,
      childComponent, parentEventUsed, parentForestUsed, parentOwned,
      childEventUsed, childForestUsed, childOwned, parentAnchor,
      _oldCommittedPath, childEventAnchor, _oldCanonicalPath, edgeParentLookup,
      edgeChildLookup, _parentRawAge, _parentEq, _childEq, selectedMarked,
      _parentComponentLookup, _parentDerivation, _parentLink, _parentWitness,
      _parentAccounted, _selectedOwned, _parentLeftOwned,
      _childComponentLookup, _childDerivation, _childLink, _childWitness,
      _childAccounted, _reachedOwned, _parentAnchorStarts,
      _parentAnchorFinishes, _parentAnchorWithin, _oldCommittedStarts,
      _oldCommittedFinishes, _childAnchorStarts, _childAnchorFinishes,
      _childAnchorWithin, _oldCanonicalStarts, _oldCanonicalFinishes,
      _reachedEndpoint⟩
  by_cases sameConclusion : edgeStep.tensor.conclusion = outer.conclusion
  · exact (sameTensorConclusion_selected_eq_markedMate invariant edgeStep
      work outer outerValid selectedMarked mateMarked sameConclusion).2.2
  have different : ∀ {otherBefore otherAfter : ReservationState}
      (otherStep : NewStep certificate otherBefore otherAfter),
      tagHistory.reservationLedger[candidateRawAge]? =
          some (ReservationEvent.new otherStep) →
        otherStep.tensor.conclusion ≠ outer.conclusion := by
    intro otherBefore otherAfter otherStep otherLookup
    have sameEvent :
        ReservationEvent.new otherStep = ReservationEvent.new edgeStep :=
      Option.some.inj (otherLookup.symm.trans edgeChildLookup)
    cases sameEvent
    exact sameConclusion
  by_cases childUntouched : ∀ {event : ReservationEvent certificate},
      event ∈ tagHistory.reservationLedger →
        event.rawAge = candidateRawAge →
          ¬ event.Touched outer.conclusion
  · have suffix :=
      commitmentEdge_referencePath_avoiding_futureTensor_of_different
        tagHistory invariant work outer outerValid parentAt childAt
        different childUntouched
    exact False.elim
      (commitmentPath_conflict_early tagHistory correct
        outer outerValid parentLookup prefixPath prefixStarts prefixFinishes
        prefixAvoids suffix childAnchor)
  · rcases Classical.not_forall.mp childUntouched with ⟨childEvent, missing⟩
    rcases Classical.not_imp.mp missing with ⟨childMembership, missing⟩
    rcases Classical.not_imp.mp missing with ⟨childAge, missing⟩
    have childTouched : childEvent.Touched outer.conclusion :=
      Classical.not_not.mp missing
    cases outerSide : outer.side with
    | storedLeft =>
        exact False.elim
          (touchedFinalChild_conflicts_of_outerStoredLeft_different
            tagHistory correct invariant work outer outerValid parentAt childAt
            parentLookup prefixPath prefixStarts prefixFinishes prefixAvoids
            childMembership childAge childTouched outerSide different)
    | storedRight =>
        have childLookup :
            tagHistory.reservationLedger[candidateRawAge]? = some childEvent :=
          reservationLedger_lookup_of_mem_rawAge_wait tagHistory
            childMembership childAge
        exact False.elim
          (touchedFinalChild_conflicts_of_outerStoredRight_childAnchor
            tagHistory correct outer outerValid childLookup childTouched
            outerSide childAnchor)

/-- A maximal strictly older mate anchor extends to the event at the immediate
predecessor of arbitrary future tensor work.  The only touch-separation input
is separation from the future-work vertex; no mate-unmarked premise occurs. -/
private theorem maximal_tensorAnchor_bridge
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate state)
    {candidateRawAge : RawTokenAge} {candidateVertex : Vertex}
    (work : FutureWorkAt state candidateRawAge candidateVertex)
    (outer : TensorBelow)
    (outerValid :
      outer.Valid certificate certificate.consumerIndex candidateVertex)
    {mateRawAge : RawTokenAge}
    (mateMarked :
      state.core.marks[outer.mate]? = some (some mateRawAge))
    {event : ReservationEvent certificate}
    (eventMembership : event ∈ tagHistory.reservationLedger)
    (eventOlder :
      state.core.representative event.rawAge <
        state.core.representative candidateRawAge)
    (eventAnchor : certificate.referenceSwitchingGraph.EdgeSimplePath)
    (eventAnchorStarts : eventAnchor.start = outer.mate)
    (eventAnchorFinishes :
      eventAnchor.finish = event.search.result.left)
    (eventAnchorAvoids : outer.conclusion ∉ eventAnchor.vertices)
    (headSeparated : ∀ candidateEvent : ReservationEvent certificate,
      candidateEvent ∈ tagHistory.reservationLedger →
      state.core.representative candidateEvent.rawAge <
          state.core.representative candidateRawAge →
      ¬ candidateEvent.Touched candidateVertex)
    (maximal : ∀ candidateEvent : ReservationEvent certificate,
      candidateEvent ∈ tagHistory.reservationLedger →
      state.core.representative candidateEvent.rawAge <
          state.core.representative candidateRawAge →
      (∃ path : certificate.referenceSwitchingGraph.EdgeSimplePath,
        path.start = outer.mate ∧
          path.finish = candidateEvent.search.result.left ∧
            outer.conclusion ∉ path.vertices) →
      state.core.representative candidateEvent.rawAge ≤
        state.core.representative event.rawAge) :
    ∃ (position parent : RawTokenAge)
        (parentEvent : ReservationEvent certificate)
        (path : certificate.referenceSwitchingGraph.EdgeSimplePath),
      state.stack.sigma[position]? = some parent ∧
        state.stack.sigma[position + 1]? = some candidateRawAge ∧
        tagHistory.reservationLedger[parent]? = some parentEvent ∧
        path.start = outer.mate ∧
        path.finish = parentEvent.search.result.left ∧
        outer.conclusion ∉ path.vertices := by
  rcases strictOlderSigmaSplit_of_event_futureWork tagHistory invariant
      eventMembership work eventOlder with
    ⟨startPosition, edgeCount, predecessor, firstAt, predecessorAt,
      childAt, predecessorOlder⟩
  change
    state.stack.sigma[startPosition + edgeCount + 1]? =
      some candidateRawAge at childAt
  have firstBound :
      state.core.representative event.rawAge < state.stack.nextAge :=
    invariant.stack_wellShaped.sigma_partition.boundary_lt _
      (List.mem_of_getElem? firstAt)
  rcases tagHistory.reservationLedger_eventAtRawAge
      (state.core.representative event.rawAge) firstBound with
    ⟨firstEvent, firstLookup, _firstEventAge⟩
  rcases eventLeft_to_representativeEvent_referencePath_avoiding_futureTensor
      tagHistory correct invariant work outer outerValid eventMembership
      firstLookup with
    ⟨componentPath, componentStarts, componentFinishes, componentAvoids⟩
  rcases eventAnchor.connectEraseAvoiding componentPath
      (eventAnchorFinishes.trans componentStarts.symm)
      eventAnchorAvoids componentAvoids with
    ⟨anchorPath, anchorStarts, anchorFinishes, anchorAvoids⟩
  by_cases zero : edgeCount = 0
  · subst edgeCount
    have predecessorEq :
        predecessor = state.core.representative event.rawAge := by
      apply Option.some.inj
      have predecessorAtStart :
          state.stack.sigma[startPosition]? = some predecessor := by
        simpa using predecessorAt
      exact predecessorAtStart.symm.trans firstAt
    subst predecessor
    refine ⟨startPosition, state.core.representative event.rawAge,
      firstEvent, anchorPath, firstAt, ?_, firstLookup, ?_, ?_,
      anchorAvoids⟩
    · simpa using childAt
    · exact anchorStarts.trans eventAnchorStarts
    · exact anchorFinishes.trans componentFinishes
  · have positive : 0 < edgeCount := Nat.zero_lt_of_ne_zero zero
    have intervalPath :
        tagHistory.CommitmentEdgeTargetAvoidingPath
          (state.core.representative event.rawAge) predecessor
          outer.conclusion := by
      apply tagHistory.commitmentInterval_referencePath_avoiding positive
        firstAt predecessorAt
      intro offset parent child offsetLt parentAt childAtLocal
      rcases tagHistory.commitmentEdge_referencePath invariant parentAt
          childAtLocal with
        ⟨edgeBefore, edgeAfter, edgeStep, edgeParentEvent,
          parentComponent, childComponent, parentEventUsed, parentForestUsed,
          parentOwned, childEventUsed, childForestUsed, childOwned,
          parentEventAnchor, _oldCommittedPath, childEventAnchor,
          _oldCanonicalPath, edgeParentLookup, edgeChildLookup,
          _parentRawAge, _parentEq, childEq, selectedMarked,
          _parentComponentLookup, _parentDerivation, _parentLink,
          _parentWitness, _parentAccounted, _selectedOwned,
          _parentLeftOwned, _childComponentLookup, _childDerivation,
          _childLink, _childWitness, _childAccounted, _reachedOwned,
          _parentAnchorStarts, _parentAnchorFinishes, _parentAnchorWithin,
          _oldCommittedStarts, _oldCommittedFinishes, _childAnchorStarts,
          _childAnchorFinishes, _childAnchorWithin, _oldCanonicalStarts,
          _oldCanonicalFinishes, _reachedEndpoint⟩
      have childMembership :
          ReservationEvent.new edgeStep ∈ tagHistory.reservationLedger :=
        List.mem_of_getElem? edgeChildLookup
      have childRoot :=
        representative_eq_of_sigmaAt_wait invariant childAtLocal
      have predecessorRoot :=
        representative_eq_of_sigmaAt_wait invariant predecessorAt
      rcases List.getElem?_eq_some_iff.mp firstAt with
        ⟨firstPositionBound, firstValue⟩
      rcases List.getElem?_eq_some_iff.mp childAtLocal with
        ⟨childPositionBound, childValue⟩
      have firstBeforeChildRaw :
          state.core.representative event.rawAge < child := by
        have ordered :=
          (List.pairwise_iff_getElem.mp
            invariant.stack_wellShaped.sigma_partition.strictIncreasing)
            startPosition (startPosition + offset + 1)
            firstPositionBound childPositionBound (by omega)
        simpa [firstValue, childValue] using ordered
      have firstBeforeChild :
          state.core.representative event.rawAge <
            state.core.representative
              (ReservationEvent.new edgeStep).rawAge := by
        rw [← childEq, childRoot]
        exact firstBeforeChildRaw
      have childLePredecessor : child ≤ predecessor := by
        by_cases samePosition :
            startPosition + offset + 1 = startPosition + edgeCount
        · have sameLookup :
              state.stack.sigma[startPosition + offset + 1]? =
                some predecessor := by
            simpa [samePosition] using predecessorAt
          exact Nat.le_of_eq
            (Option.some.inj (childAtLocal.symm.trans sameLookup))
        · rcases List.getElem?_eq_some_iff.mp predecessorAt with
            ⟨predecessorPositionBound, predecessorValue⟩
          have positionLt :
              startPosition + offset + 1 <
                startPosition + edgeCount := by
            omega
          have ordered :=
            (List.pairwise_iff_getElem.mp
              invariant.stack_wellShaped.sigma_partition.strictIncreasing)
              (startPosition + offset + 1) (startPosition + edgeCount)
              childPositionBound predecessorPositionBound positionLt
          rw [childValue, predecessorValue] at ordered
          exact Nat.le_of_lt ordered
      have childOlder :
          state.core.representative
              (ReservationEvent.new edgeStep).rawAge <
            state.core.representative candidateRawAge := by
        rw [← childEq, childRoot]
        rw [predecessorRoot] at predecessorOlder
        exact Nat.lt_of_le_of_lt childLePredecessor predecessorOlder
      by_cases sameConclusion :
          edgeStep.tensor.conclusion = outer.conclusion
      · have sameFacts :=
          sameTensorConclusion_selected_eq_markedMate invariant edgeStep
            work outer outerValid selectedMarked mateMarked sameConclusion
        have mateInTrace :
            edgeStep.tensor.mate ∈ edgeStep.search.trace := by
          cases traceEquation : edgeStep.search.trace with
          | nil =>
              have traceHead := edgeStep.route.traceHead
              simp [traceEquation] at traceHead
          | cons head tail =>
              have headEq : head = edgeStep.tensor.mate := by
                simpa [traceEquation] using edgeStep.route.traceHead
              subst head
              simp
        have childTouched :
            (ReservationEvent.new edgeStep).Touched candidateVertex := by
          change edgeStep.search.Touched candidateVertex
          exact Or.inl (by simpa [sameFacts.2.1] using mateInTrace)
        exact False.elim
          (headSeparated (ReservationEvent.new edgeStep) childMembership
            childOlder childTouched)
      · have different : ∀ {otherBefore otherAfter : ReservationState}
            (otherStep : NewStep certificate otherBefore otherAfter),
            tagHistory.reservationLedger[child]? =
                some (ReservationEvent.new otherStep) →
              otherStep.tensor.conclusion ≠ outer.conclusion := by
          intro otherBefore otherAfter otherStep otherLookup
          have sameEvent :
              ReservationEvent.new otherStep =
                ReservationEvent.new edgeStep :=
            Option.some.inj (otherLookup.symm.trans edgeChildLookup)
          cases sameEvent
          exact sameConclusion
        by_cases childUntouched :
            ¬ (ReservationEvent.new edgeStep).Touched outer.conclusion
        · apply
            commitmentEdge_referencePath_avoiding_futureTensor_of_different
              tagHistory invariant work outer outerValid parentAt
              childAtLocal different
          intro otherEvent otherMembership otherAge
          have otherLookup :
              tagHistory.reservationLedger[child]? = some otherEvent :=
            reservationLedger_lookup_of_mem_rawAge_wait tagHistory
              otherMembership otherAge
          have otherEq :
              otherEvent = ReservationEvent.new edgeStep :=
            Option.some.inj (otherLookup.symm.trans edgeChildLookup)
          subst otherEvent
          exact childUntouched
        · have childTouched :
              (ReservationEvent.new edgeStep).Touched outer.conclusion :=
            Classical.not_not.mp childUntouched
          cases outerSide : outer.side with
          | storedLeft =>
              have storedLeftTouched :
                  (ReservationEvent.new edgeStep).Touched outer.storedLeft :=
                reservationEvent_touched_tensor_storedLeft_wait correct.1
                  (ReservationEvent.new edgeStep) outerValid childTouched
              have candidateIsLeft : candidateVertex = outer.storedLeft := by
                simpa [TensorBelow.premise, TensorPremiseSide.premise,
                  outerSide] using outerValid.2.2.2
              have candidateTouched :
                  (ReservationEvent.new edgeStep).Touched candidateVertex := by
                simpa [candidateIsLeft] using storedLeftTouched
              exact False.elim
                (headSeparated (ReservationEvent.new edgeStep)
                  childMembership childOlder candidateTouched)
          | storedRight =>
              rcases touchedEvent_mateAnchor_of_outerStoredRight correct
                  outer outerValid (ReservationEvent.new edgeStep)
                  childTouched outerSide with
                ⟨childAnchorPath, childAnchorStarts, childAnchorFinishes,
                  childAnchorAvoids⟩
              have upper := maximal (ReservationEvent.new edgeStep)
                childMembership childOlder
                ⟨childAnchorPath, childAnchorStarts, childAnchorFinishes,
                  childAnchorAvoids⟩
              exact False.elim
                (Nat.not_lt_of_ge upper firstBeforeChild)
    rcases intervalPath with
      ⟨intervalFirstEvent, predecessorEvent, intervalWitness,
        intervalFirstLookup, predecessorLookup, intervalStarts,
        intervalFinishes, intervalAvoids⟩
    have firstEventEq : firstEvent = intervalFirstEvent :=
      Option.some.inj (firstLookup.symm.trans intervalFirstLookup)
    subst intervalFirstEvent
    rcases anchorPath.connectEraseAvoiding intervalWitness
        (anchorFinishes.trans
          (componentFinishes.trans intervalStarts.symm))
        anchorAvoids intervalAvoids with
      ⟨path, pathStarts, pathFinishes, pathAvoids⟩
    refine ⟨startPosition + edgeCount, predecessor, predecessorEvent,
      path, predecessorAt, ?_, predecessorLookup, ?_, ?_, pathAvoids⟩
    · simpa [Nat.add_assoc] using childAt
    · exact pathStarts.trans (anchorStarts.trans eventAnchorStarts)
    · exact pathFinishes.trans intervalFinishes

/-- Conditional end-to-end predecessor theorem for arbitrary future tensor
work.  It packages the maximal-anchor argument and isolates exactly two
external facts: older-event separation from the candidate vertex and an exact
child-event anchor at the candidate boundary. -/
private theorem markedMate_sigmaImmediatePredecessor_of_childAnchor_core
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate state)
    {candidateRawAge : RawTokenAge} {candidateVertex : Vertex}
    (work : FutureWorkAt state candidateRawAge candidateVertex)
    (outer : TensorBelow)
    (outerValid :
      outer.Valid certificate certificate.consumerIndex candidateVertex)
    {mateRawAge : RawTokenAge}
    (mateMarked :
      state.core.marks[outer.mate]? = some (some mateRawAge))
    (older :
      state.core.representative mateRawAge <
        state.core.representative candidateRawAge)
    (headSeparated : ∀ event : ReservationEvent certificate,
      event ∈ tagHistory.reservationLedger →
      state.core.representative event.rawAge <
          state.core.representative candidateRawAge →
      ¬ event.Touched candidateVertex)
    (childAnchor : ∀ childEvent : ReservationEvent certificate,
      tagHistory.reservationLedger[candidateRawAge]? = some childEvent →
        ∃ path : certificate.referenceSwitchingGraph.EdgeSimplePath,
          path.start = childEvent.search.result.left ∧
            path.finish = candidateVertex ∧
              outer.conclusion ∉ path.vertices) :
    ∃ position,
      state.stack.sigma[position]? = some mateRawAge ∧
        state.stack.sigma[position + 1]? = some candidateRawAge ∧
          sigmaBoundary? state.stack.sigma mateRawAge = some mateRawAge := by
  classical
  rcases tagHistory.rawMarked_reservationEvent_referenceAnchors invariant
      mateMarked with
    ⟨mateEvent, mateComponent, mateEventUsed, mateForestUsed, mateOwned,
      matePath, _rightPath, mateLookup, mateEventAge,
      mateComponentLookup, _mateDerivation, _mateLink, _mateWitness,
      mateAccounted, _mateOwned, _mateLeftOwned, _mateRightOwned,
      matePathStarts, matePathFinishes, matePathWithin,
      _rightPathStarts, _rightPathFinishes, _rightPathWithin⟩
  have mateMembership : mateEvent ∈ tagHistory.reservationLedger :=
    List.mem_of_getElem? mateLookup
  have mateEventOlder :
      state.core.representative mateEvent.rawAge <
        state.core.representative candidateRawAge := by
    rw [mateEventAge]
    exact older
  have conclusionNotMateOwned : outer.conclusion ∉ mateOwned :=
    tensorConclusion_not_owned_of_futureWork invariant work outer outerValid
      mateComponentLookup mateAccounted
  have matePathAvoids : outer.conclusion ∉ matePath.vertices := by
    intro inPath
    exact conclusionNotMateOwned
      (matePathWithin outer.conclusion inPath)
  let blockers := tagHistory.reservationLedger.filter fun event ↦
    state.core.representative event.rawAge <
        state.core.representative candidateRawAge ∧
      ∃ path : certificate.referenceSwitchingGraph.EdgeSimplePath,
        path.start = outer.mate ∧
          path.finish = event.search.result.left ∧
            outer.conclusion ∉ path.vertices
  let blockerRepresentatives := blockers.map fun event ↦
    state.core.representative event.rawAge
  have mateInBlockers : mateEvent ∈ blockers := by
    simp [blockers, mateMembership, mateEventOlder]
    exact ⟨matePath, matePathStarts, matePathFinishes, matePathAvoids⟩
  have mateRepresentativeIn :
      state.core.representative mateEvent.rawAge ∈ blockerRepresentatives :=
    List.mem_map.mpr ⟨mateEvent, mateInBlockers, rfl⟩
  cases maxEquation : blockerRepresentatives.max? with
  | none =>
      have empty : blockerRepresentatives = [] :=
        List.max?_eq_none_iff.mp maxEquation
      rw [empty] at mateRepresentativeIn
      contradiction
  | some maxRepresentative =>
      have maxFacts := List.max?_eq_some_iff.mp maxEquation
      rcases List.mem_map.mp maxFacts.1 with
        ⟨maxEvent, maxInBlockers, maxRepresentativeEquation⟩
      subst maxRepresentative
      have maxData :
          maxEvent ∈ tagHistory.reservationLedger ∧
            state.core.representative maxEvent.rawAge <
              state.core.representative candidateRawAge ∧
            ∃ path : certificate.referenceSwitchingGraph.EdgeSimplePath,
              path.start = outer.mate ∧
                path.finish = maxEvent.search.result.left ∧
                  outer.conclusion ∉ path.vertices := by
        simpa [blockers] using maxInBlockers
      rcases maxData with
        ⟨maxMembership, maxOlder, maxPath, maxPathStarts,
          maxPathFinishes, maxPathAvoids⟩
      have maximal : ∀ candidateEvent : ReservationEvent certificate,
          candidateEvent ∈ tagHistory.reservationLedger →
          state.core.representative candidateEvent.rawAge <
              state.core.representative candidateRawAge →
          (∃ path : certificate.referenceSwitchingGraph.EdgeSimplePath,
            path.start = outer.mate ∧
              path.finish = candidateEvent.search.result.left ∧
                outer.conclusion ∉ path.vertices) →
          state.core.representative candidateEvent.rawAge ≤
            state.core.representative maxEvent.rawAge := by
        intro candidateEvent candidateMembership candidateOlder
          candidateAnchor
        have candidateInBlockers : candidateEvent ∈ blockers := by
          simp [blockers, candidateMembership, candidateOlder,
            candidateAnchor]
        have candidateRepresentativeIn :
            state.core.representative candidateEvent.rawAge ∈
              blockerRepresentatives :=
          List.mem_map.mpr ⟨candidateEvent, candidateInBlockers, rfl⟩
        exact maxFacts.2 _ candidateRepresentativeIn
      rcases maximal_tensorAnchor_bridge tagHistory correct invariant work
          outer outerValid mateMarked maxMembership maxOlder maxPath
          maxPathStarts maxPathFinishes maxPathAvoids headSeparated maximal with
        ⟨position, parent, parentEvent, prefixPath, parentAt, candidateAt,
          parentLookup, prefixStarts, prefixFinishes, prefixAvoids⟩
      have parentEq : parent = mateRawAge :=
        finalCommitment_parent_eq_mateRawAge_of_childAnchor tagHistory
          correct invariant work outer outerValid mateMarked parentAt
          candidateAt parentLookup prefixPath prefixStarts prefixFinishes
          prefixAvoids childAnchor
      subst parent
      have mateRoot : state.core.representative mateRawAge = mateRawAge :=
        representative_eq_of_sigmaAt_wait invariant parentAt
      have stackMateMarked :
          state.stack.marks[outer.mate]? = some (some mateRawAge) := by
        rw [← invariant.realizesSigma.marks_eq]
        exact mateMarked
      have mateAgeBound : mateRawAge < state.stack.nextAge :=
        invariant.stack_wellShaped.assigned_age_bound outer.mate mateRawAge
          stackMateMarked
      have mateBoundary :=
        invariant.realizesSigma.representative_eq_boundary mateAgeBound
      refine ⟨position, parentAt, candidateAt, ?_⟩
      simpa [mateRoot] using mateBoundary

end WaitStep

namespace CanonicalTagHistory

/-- Converts canonical history, strict older-event separation, and an exact
child-event anchor into the marked tensor mate's immediate sigma predecessor.

This bridge does not establish its separation or anchor premises. It proves no
rule applicability, dispatcher progress or totality, global raw seam, fallback
removal, sequentialization, or complexity bound. -/
theorem markedMate_sigmaImmediatePredecessor_of_childAnchor
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate state)
    {candidateRawAge : RawTokenAge} {candidateVertex : Vertex}
    (work : FutureWorkAt state candidateRawAge candidateVertex)
    (outer : TensorBelow)
    (outerValid :
      outer.Valid certificate certificate.consumerIndex candidateVertex)
    {mateRawAge : RawTokenAge}
    (mateMarked :
      state.core.marks[outer.mate]? = some (some mateRawAge))
    (older :
      state.core.representative mateRawAge <
        state.core.representative candidateRawAge)
    (headSeparated : ∀ event : ReservationEvent certificate,
      event ∈ tagHistory.reservationLedger →
      state.core.representative event.rawAge <
          state.core.representative candidateRawAge →
      ¬ event.Touched candidateVertex)
    (childAnchor : ∀ childEvent : ReservationEvent certificate,
      tagHistory.reservationLedger[candidateRawAge]? = some childEvent →
      ∃ path : certificate.referenceSwitchingGraph.EdgeSimplePath,
        path.start = childEvent.search.result.left ∧
        path.finish = candidateVertex ∧
        outer.conclusion ∉ path.vertices) :
    Nonempty
      (SigmaImmediatePredecessorAt state.stack.sigma
        candidateRawAge mateRawAge mateRawAge) := by
  rcases WaitStep.markedMate_sigmaImmediatePredecessor_of_childAnchor_core
      tagHistory correct invariant work outer outerValid mateMarked older
      headSeparated childAnchor with
    ⟨position, previousAt, candidateAt, mateBoundary⟩
  exact ⟨{
    position
    previous_at := previousAt
    candidate_at := candidateAt
    mate_boundary := mateBoundary }⟩

end CanonicalTagHistory

namespace WaitStep

/-- Wait specialization after the history-local created-head separation fact
has been supplied.  All destination/mate reference geometry is now derived
for both submitted-par orientations. -/
private theorem createdConclusion_markedMate_sigmaImmediatePredecessor
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate after}
    (step : WaitStep certificate before after)
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate after)
    (outer : ConnectiveBelow certificate step.consumer.conclusion)
    (outerTensor : outer.kind = .tensor)
    {mateRawAge : RawTokenAge}
    (mateMarked :
      after.core.marks[outer.mate]? = some (some mateRawAge))
    (older :
      after.core.representative mateRawAge <
        after.core.representative step.destination.boundary)
    (headSeparated : ∀ event : ReservationEvent certificate,
      event ∈ tagHistory.reservationLedger →
      after.core.representative event.rawAge <
          after.core.representative step.destination.boundary →
      ¬ event.Touched step.consumer.conclusion) :
    ∃ position,
      after.stack.sigma[position]? = some mateRawAge ∧
        after.stack.sigma[position + 1]? =
          some step.destination.boundary ∧
        sigmaBoundary? after.stack.sigma mateRawAge = some mateRawAge := by
  rcases step.destination.exact with
    ⟨payload, _initialized, updated, _marks, _nextAge, _sigma, _ready,
      _core, _tags⟩
  have work : FutureWorkAt after step.destination.boundary
      step.consumer.conclusion :=
    FutureWorkAt.waiting updated (by simp)
  let tensor : TensorBelow := connectiveBelowToTensor outer outerTensor
  have tensorValid :
      tensor.Valid certificate certificate.consumerIndex
        step.consumer.conclusion := by
    refine ⟨outer.consumer_eq, ?_, ?_, ?_⟩
    · simpa [tensor, connectiveBelowToTensor, outerTensor,
        SequentialConnectiveKind.asLink] using outer.link_eq
    · simpa [tensor, connectiveBelowToTensor, outerTensor,
        SequentialConnectiveKind.asLink] using outer.wellFormed
    · simpa [tensor, connectiveBelowToTensor, TensorBelow.premise] using
        outer.premise_eq
  have tensorMateMarked :
      after.core.marks[tensor.mate]? = some (some mateRawAge) := by
    simpa [tensor, connectiveBelowToTensor, TensorBelow.mate,
      ConnectiveBelow.mate] using mateMarked
  have childAnchor : CreatedConclusionTensorChildAnchor step tagHistory tensor :=
    step.createdConclusionTensorChildAnchor tagHistory correct invariant
      tensor tensorValid
  rcases tagHistory.markedMate_sigmaImmediatePredecessor_of_childAnchor
      correct invariant work tensor tensorValid tensorMateMarked older
      headSeparated childAnchor with
    ⟨predecessor⟩
  exact ⟨predecessor.position, predecessor.previous_at,
    predecessor.candidate_at, predecessor.mate_boundary⟩

end WaitStep
end SequentialFigure7
end ProofNetIR

namespace ProofNetIR

namespace SequentialUnification
namespace SourceLeftRegionVertex

private theorem dropParForWaitPredecessorAudit
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {linkIndex : Nat} {left right conclusion vertex : Vertex}
    (exactPar :
      certificate.links[linkIndex]? = some (.par left right conclusion))
    (region : SourceLeftRegionVertex certificate conclusion vertex)
    (ne : vertex ≠ conclusion) :
    SourceLeftRegionVertex certificate left vertex := by
  cases region with
  | visited reachable =>
      cases reachable with
      | refl => exact False.elim (ne rfl)
      | step head tail =>
          cases head with
          | tensor exactOther =>
              have same :=
                UnificationState.StructurallyWellFormed.producerLink_unique
                  (conclusion := conclusion) structural
                  (List.mem_of_getElem? exactPar) (by simp [Link.produces])
                  (List.mem_of_getElem? exactOther) (by simp [Link.produces])
              cases same
          | par exactOther =>
              have same :=
                UnificationState.StructurallyWellFormed.producerLink_unique
                  (conclusion := conclusion) structural
                  (List.mem_of_getElem? exactPar) (by simp [Link.produces])
                  (List.mem_of_getElem? exactOther) (by simp [Link.produces])
              cases same
              exact .visited tail
  | @terminalPartner reached partner axiomIndex reachable exactAxiom =>
      cases reachable with
      | refl =>
          exfalso
          have parMembership :
              Link.par left right conclusion ∈ certificate.links :=
            List.mem_of_getElem? exactPar
          rcases exactAxiom with axiomEq | axiomEq
          · exact structural.axiomEndpoint_ne_connectiveConclusion
              (List.mem_of_getElem? axiomEq) (Or.inl rfl) parMembership
              (by simp [Link.produces])
          · exact structural.axiomEndpoint_ne_connectiveConclusion
              (List.mem_of_getElem? axiomEq) (Or.inr rfl) parMembership
              (by simp [Link.produces])
      | step head tail =>
          cases head with
          | tensor exactOther =>
              have same :=
                UnificationState.StructurallyWellFormed.producerLink_unique
                  (conclusion := conclusion) structural
                  (List.mem_of_getElem? exactPar) (by simp [Link.produces])
                  (List.mem_of_getElem? exactOther) (by simp [Link.produces])
              cases same
          | par exactOther =>
              have same :=
                UnificationState.StructurallyWellFormed.producerLink_unique
                  (conclusion := conclusion) structural
                  (List.mem_of_getElem? exactPar) (by simp [Link.produces])
                  (List.mem_of_getElem? exactOther) (by simp [Link.produces])
              cases same
              exact .terminalPartner tail exactAxiom

end SourceLeftRegionVertex
end SequentialUnification

namespace SequentialFigure7

open SequentialUnification
open SequentialSchedulerBridge
open SequentialSchedulerState

namespace WaitStep

/-- Head-only version of the current Wait-created touch theorem.

Unlike `createdHeadTouchSeparated`, this theorem does not require a
`WaitCreatedCandidate`, so it remains usable when an outer tensor mate is
marked rather than raw-unmarked. -/
private theorem createdConclusionTouchSeparated
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    (step : WaitStep certificate before after)
    (prior : CanonicalTagHistory certificate history)
    (structural : certificate.StructurallyWellFormed)
    {event : ReservationEvent certificate}
    (eventMembership : event ∈ prior.reservationLedger)
    (older :
      step.prepared.after.core.representative event.rawAge <
        step.prepared.after.core.representative
          step.destination.boundary) :
    ¬ event.Touched step.consumer.conclusion := by
  have invariant : SchedulerInvariant certificate before :=
    history.schedulerInvariant structural
  have middleInvariant := step.prepared.schedulerInvariant invariant
  intro touched
  rcases prior.reservationLedger_axiomEndpoints_accounted
      structural eventMembership with
    ⟨eventComponent, eventUsed, eventForestUsed, eventOwned,
      eventLookup, eventDerivation, eventLink, eventWitness,
      eventAccounted, eventLeftOwned, eventRightOwned⟩
  rcases middleInvariant.component_forest_provenance with
    ⟨usedAt, ownedAt, live, separated, markedOwned⟩
  have componentsEq :
      step.prepared.after.core.components = before.core.components :=
    (UnificationState.markReadyRaw?_exact
      step.prepared.core_mark_eq).2.2.2.1
  have eventMiddleLookup :
      step.prepared.after.core.components[
        step.prepared.after.core.representative event.rawAge]? =
          some (some eventComponent) := by
    rw [step.prepared.after_representative_eq_before event.rawAge,
      componentsEq]
    exact eventLookup
  have eventFacts := live eventMiddleLookup
  have eventOwnedEq :
      eventOwned =
        ownedAt (step.prepared.after.core.representative event.rawAge) :=
    Certificate.OccurrenceDerivation.owned_unique structural
      eventDerivation eventFacts.1.derivation
  have eventLeftForestOwned :
      event.search.result.left ∈
        ownedAt (step.prepared.after.core.representative event.rawAge) := by
    rw [← eventOwnedEq]
    exact eventLeftOwned
  have eventLeftRegionFromConclusion :
      SourceLeftRegionVertex certificate step.consumer.conclusion
        event.search.result.left :=
    event.leftEndpoint_sourceLeftRegion_of_touched touched
  have eventLeftNeConclusion :
      event.search.result.left ≠ step.consumer.conclusion := by
    intro same
    have eventAxiomMembership :
        Link.axiom event.search.result.left event.search.result.right ∈
          certificate.links :=
      List.mem_of_getElem? event.search.result.exactLink
    have waitParMembership :
        Link.par step.consumer.storedLeft step.consumer.storedRight
            step.consumer.conclusion ∈ certificate.links :=
      List.mem_of_getElem? step.submitted_par
    exact structural.axiomEndpoint_ne_connectiveConclusion
      eventAxiomMembership (Or.inl rfl) waitParMembership
      (by simpa [Link.produces] using same.symm)
  have eventLeftRegion :
      SourceLeftRegionVertex certificate step.consumer.storedLeft
        event.search.result.left :=
    SourceLeftRegionVertex.dropParForWaitPredecessorAudit structural
      step.submitted_par eventLeftRegionFromConclusion eventLeftNeConclusion
  have selectedMarked :
      step.prepared.after.core.marks[step.prepared.stackResult.vertex]? =
        some (some step.prepared.stackResult.rawAge) :=
    (UnificationState.markReadyRaw?_exact
      step.prepared.core_mark_eq).2.2.2.2.2.2
  have mateMarked :
      step.prepared.after.core.marks[step.consumer.mate]? =
        some (some step.mateRawAge) :=
    step.mate_marked
  rcases markedOwned selectedMarked with
    ⟨selectedIndex, selectedComponent, selectedRep,
      selectedLookup, selectedOwned⟩
  rcases markedOwned mateMarked with
    ⟨mateIndex, mateComponent, mateRep, mateLookup, mateOwned⟩
  have selectedFacts := live selectedLookup
  have mateFacts := live mateLookup
  have selectedAgeBound :
      step.prepared.stackResult.rawAge <
        step.prepared.after.stack.nextAge := by
    have stackMarked :
        step.prepared.after.stack.marks[
            step.prepared.stackResult.vertex]? =
          some (some step.prepared.stackResult.rawAge) := by
      rw [← middleInvariant.realizesSigma.marks_eq]
      exact selectedMarked
    exact middleInvariant.stack_wellShaped.assigned_age_bound
      step.prepared.stackResult.vertex
      step.prepared.stackResult.rawAge stackMarked
  have selectedSigmaTop :
      step.prepared.after.stack.sigma.getLast? =
        some step.prepared.stackResult.rawAge := by
    rcases SequentialStackState.popReadyMark?_exact
        step.prepared.stack_eq with
      ⟨_topReady, sigmaTop, _unmarked, _marks, _nextAge, sigmaEq,
        _ready, _waiting, _marked⟩
    change step.prepared.stackResult.after.sigma.getLast? =
      some step.prepared.stackResult.rawAge
    rw [sigmaEq]
    exact sigmaTop
  have selectedBoundaryLookup :
      sigmaBoundary? step.prepared.after.stack.sigma
          step.prepared.stackResult.rawAge =
        some step.prepared.stackResult.rawAge :=
    middleInvariant.stack_wellShaped.sigma_partition
      |>.sigmaBoundary?_eq_top selectedSigmaTop
  have selectedRoot :
      step.prepared.after.core.representative
          step.prepared.stackResult.rawAge =
        step.prepared.stackResult.rawAge := by
    have realized :=
      middleInvariant.realizesSigma.representative_eq_boundary
        selectedAgeBound
    exact Option.some.inj (realized.symm.trans selectedBoundaryLookup)
  have mateAgeBound :
      step.mateRawAge < step.prepared.after.stack.nextAge := by
    have stackMarked :
        step.prepared.after.stack.marks[step.consumer.mate]? =
          some (some step.mateRawAge) := by
      rw [← middleInvariant.realizesSigma.marks_eq]
      exact mateMarked
    exact middleInvariant.stack_wellShaped.assigned_age_bound
      step.consumer.mate step.mateRawAge stackMarked
  have mateRootAtBoundary :
      step.prepared.after.core.representative step.mateRawAge =
        step.destination.boundary := by
    have realized :=
      middleInvariant.realizesSigma.representative_eq_boundary mateAgeBound
    exact Option.some.inj
      (realized.symm.trans step.destination.boundary_eq)
  have mateParentBound :
      step.mateRawAge < step.prepared.after.core.parents.size := by
    rw [middleInvariant.realizesSigma.horizon_eq]
    exact mateAgeBound
  have destinationRoot :
      step.prepared.after.core.representative step.destination.boundary =
        step.destination.boundary := by
    have idempotent :=
      middleInvariant.core_abstractable.representativeIdempotent
        mateParentBound
    rw [mateRootAtBoundary] at idempotent
    exact idempotent
  have olderAtBoundary :
      step.prepared.after.core.representative event.rawAge <
        step.destination.boundary := by
    rw [destinationRoot] at older
    exact older
  have boundaryLtSelected :
      step.destination.boundary < step.prepared.stackResult.rawAge :=
    Nat.lt_of_le_of_lt (sigmaBoundary?_le step.destination.boundary_eq)
      step.younger
  have eventNeSelected :
      step.prepared.after.core.representative event.rawAge ≠
        selectedIndex := by
    intro same
    rw [← selectedRep, selectedRoot] at same
    rw [same] at olderAtBoundary
    exact (Nat.not_lt_of_ge (Nat.le_of_lt boundaryLtSelected))
      olderAtBoundary
  have mateIndexEq : mateIndex = step.destination.boundary :=
    mateRep.symm.trans mateRootAtBoundary
  have eventNeMate :
      step.prepared.after.core.representative event.rawAge ≠ mateIndex := by
    intro same
    rw [mateIndexEq] at same
    exact (Nat.ne_of_lt olderAtBoundary) same
  cases sideEquation : step.consumer.side with
  | storedLeft =>
      have storedLeftEq :
          step.consumer.storedLeft =
            step.prepared.stackResult.vertex := by
        have selectedEq :
            step.prepared.stackResult.vertex =
              step.consumer.storedLeft := by
          simpa [TensorPremiseSide.premise, sideEquation] using
            step.consumer.premise_eq
        exact selectedEq.symm
      have eventLeftSelectedOwned :
          event.search.result.left ∈ ownedAt selectedIndex :=
        selectedFacts.1.derivation.sourceLeftRegion_owned structural
          selectedOwned (by simpa [storedLeftEq] using eventLeftRegion)
      have disjoint :=
        (separated eventMiddleLookup selectedLookup eventNeSelected).2
      exact disjoint event.search.result.left eventLeftForestOwned
        eventLeftSelectedOwned
  | storedRight =>
      have storedLeftEq :
          step.consumer.storedLeft = step.consumer.mate := by
        simp [ConnectiveBelow.mate, TensorPremiseSide.mate, sideEquation]
      have eventLeftMateOwned :
          event.search.result.left ∈ ownedAt mateIndex :=
        mateFacts.1.derivation.sourceLeftRegion_owned structural mateOwned
          (by simpa [storedLeftEq] using eventLeftRegion)
      have disjoint :=
        (separated eventMiddleLookup mateLookup eventNeMate).2
      exact disjoint event.search.result.left eventLeftForestOwned
        eventLeftMateOwned

end WaitStep
end SequentialFigure7
end ProofNetIR

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerBridge
open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialUnification

namespace WaitStep

/-- A canonical dispatcher Wait extension establishes the exact predecessor
for its newly created conclusion, with no orientation restriction and without
assuming that the marked outer mate is raw-unmarked. -/
private theorem createdConclusion_olderMarkedTensorPredecessor
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    {invariant : SchedulerInvariant certificate before}
    {dispatch : DispatchStep certificate before invariant ⟨.wait, after⟩}
    (step : WaitStep certificate before after)
    (prior : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (outer : ConnectiveBelow certificate step.consumer.conclusion)
    (outerTensor : outer.kind = .tensor)
    {mateRawAge : RawTokenAge}
    (mateMarked :
      after.core.marks[outer.mate]? = some (some mateRawAge))
    (older :
      after.core.representative mateRawAge <
        after.core.representative step.destination.boundary) :
    ∃ previousBoundary,
      Nonempty
        (SigmaImmediatePredecessorAt after.stack.sigma
          step.destination.boundary mateRawAge previousBoundary) := by
  let afterHistory : ExecutedHistory certificate after :=
    ExecutedHistory.later history invariant dispatch
  let afterTags : CanonicalTagHistory certificate afterHistory :=
    CanonicalTagHistory.later prior (DispatchTagEvidence.wait step)
  have afterInvariant : SchedulerInvariant certificate after :=
    step.schedulerInvariant invariant
  have headSeparated : ∀ event : ReservationEvent certificate,
      event ∈ afterTags.reservationLedger →
      after.core.representative event.rawAge <
          after.core.representative step.destination.boundary →
      ¬ event.Touched step.consumer.conclusion := by
    intro event eventMembership eventOlder
    have priorMembership : event ∈ prior.reservationLedger := by
      simpa [afterTags, CanonicalTagHistory.reservationLedger,
        DispatchTagEvidence.reservationEvents] using eventMembership
    rcases step.destination.exact with
      ⟨_payload, _initialized, _updated, _marks, _nextAge, _sigma, _ready,
        coreEq, _tags⟩
    rw [coreEq] at eventOlder
    exact step.createdConclusionTouchSeparated prior correct.1
      priorMembership eventOlder
  rcases step.createdConclusion_markedMate_sigmaImmediatePredecessor
      afterTags correct afterInvariant outer outerTensor mateMarked older
      headSeparated with
    ⟨position, previousAt, candidateAt, mateBoundary⟩
  exact ⟨mateRawAge, ⟨{
    position
    previous_at := previousAt
    candidate_at := candidateAt
    mate_boundary := mateBoundary }⟩⟩

end WaitStep

namespace CanonicalTagHistory

/-- A canonical dispatcher `wait` preserves the all-future-work predecessor
invariant.  Retained work is transported through the prepared prefix and the
sigma-preserving destination update; the inserted conclusion is discharged
by private Wait-specific geometry internal to this module. -/
theorem wait_olderMarkedTensorPredecessorInvariant
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    {invariant : SchedulerInvariant certificate before}
    {dispatch : DispatchStep certificate before invariant ⟨.wait, after⟩}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (step : WaitStep certificate before after)
    (prior : OlderMarkedTensorPredecessorInvariant certificate before) :
    OlderMarkedTensorPredecessorInvariant certificate after := by
  intro candidateRawAge candidateVertex work consumer tensorKind
    mateRawAge mateMarkedAfter representativeLtAfter
  rcases work.beforeWaitOrInserted step with
    oldWork | ⟨candidateAge, candidateHead⟩
  · have middleInvariant :
        OlderMarkedTensorPredecessorInvariant certificate
          step.prepared.after :=
      step.prepared.olderMarkedTensorPredecessorInvariant invariant prior
    rcases step.destination.exact with
      ⟨_payload, _initialized, _updated, _marks, _nextAge, sigmaEq,
        _ready, coreEq, _tags⟩
    have mateMarkedMiddle :
        step.prepared.after.core.marks[consumer.mate]? =
          some (some mateRawAge) := by
      rw [coreEq] at mateMarkedAfter
      exact mateMarkedAfter
    have representativeLtMiddle :
        step.prepared.after.core.representative mateRawAge <
          step.prepared.after.core.representative candidateRawAge := by
      rw [coreEq] at representativeLtAfter
      exact representativeLtAfter
    rcases middleInvariant oldWork consumer tensorKind mateMarkedMiddle
        representativeLtMiddle with
      ⟨previousBoundary, ⟨predecessor⟩⟩
    refine ⟨previousBoundary, ⟨?_⟩⟩
    simpa [sigmaEq] using predecessor
  · subst candidateRawAge
    subst candidateVertex
    exact step.createdConclusion_olderMarkedTensorPredecessor
      (invariant := invariant) (dispatch := dispatch) tagHistory correct
      consumer tensorKind mateMarkedAfter representativeLtAfter

end CanonicalTagHistory
end SequentialFigure7
end ProofNetIR
