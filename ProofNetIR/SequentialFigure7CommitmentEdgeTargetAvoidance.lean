/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7CommitmentEdgeReferencePath
import ProofNetIR.SequentialFigure7CrossRepresentativeInvariant

/-!
# Figure-7 commitment-edge target avoidance

Constructs one exact reference-switching path across adjacent retained sigma
commitments while avoiding a supplied future candidate tensor conclusion.
The child-event untouched law is an explicit premise; this module does not
derive its global availability, any raw-seam invariant, or scheduler progress.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerBridge
open SequentialSchedulerState
open SequentialUnification

private theorem mem_liveFrontierVertices_of_raw
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

namespace FutureNewCandidateAt

private theorem tensorConclusion_not_produced
    {certificate : Certificate} {state : ReservationState}
    (candidate : FutureNewCandidateAt certificate state)
    (invariant : SchedulerInvariant certificate state) :
    ¬ Produced state candidate.tensor.conclusion := by
  intro produced
  have tensorMembership :
      Link.tensor candidate.tensor.storedLeft candidate.tensor.storedRight
          candidate.tensor.conclusion ∈ certificate.links :=
    List.mem_of_getElem? candidate.tensor_valid.2.1
  have premises :=
    invariant.produced_premises_marked tensorMembership produced
  cases sideEquation : candidate.tensor.side with
  | storedLeft =>
      rcases premises.2 with ⟨mateAge, mateMarked⟩
      have mateIsRight :
          candidate.tensor.mate = candidate.tensor.storedRight := by
        simp [TensorBelow.mate, TensorPremiseSide.mate, sideEquation]
      rw [← mateIsRight, candidate.mate_unmarked] at mateMarked
      simp at mateMarked
  | storedRight =>
      rcases premises.1 with ⟨mateAge, mateMarked⟩
      have mateIsLeft :
          candidate.tensor.mate = candidate.tensor.storedLeft := by
        simp [TensorBelow.mate, TensorPremiseSide.mate, sideEquation]
      rw [← mateIsLeft, candidate.mate_unmarked] at mateMarked
      simp at mateMarked

private theorem tensorConclusion_not_owned
    {certificate : Certificate} {state : ReservationState}
    (candidate : FutureNewCandidateAt certificate state)
    (invariant : SchedulerInvariant certificate state)
    {index : Nat} {component : UnificationComponent} {owned : List Vertex}
    (componentLookup :
      state.core.components[index]? = some (some component))
    (accounted :
      Certificate.OwnedOccurrenceAccounted state.core index component owned) :
    candidate.tensor.conclusion ∉ owned := by
  intro conclusionOwned
  apply candidate.tensorConclusion_not_produced invariant
  rcases accounted candidate.tensor.conclusion conclusionOwned with
    ⟨rawAge, marked, _representative⟩ | ⟨_unmarked, frontier⟩
  · exact Or.inl ⟨rawAge, marked⟩
  · exact Or.inr
      (mem_liveFrontierVertices_of_raw componentLookup frontier)

end FutureNewCandidateAt

private theorem parLeftEdge_mem_leftRetained
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

private theorem sourceLeftStep_referenceDirectedEdge
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
        exact parLeftEdge_mem_leftRetained membership
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

private theorem SourceLeftChain.referencePath_within_trace
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
      rcases sourceLeftStep_referenceDirectedEdge step with
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

private theorem tensorReferencePath
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

private theorem TensorBelow.referencePath
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
  rcases tensorReferencePath structural membership with
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

private theorem NewStep.selectedToReachedReferencePath_avoiding
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
  rcases TensorBelow.referencePath structural step.tensorValid with
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
  rcases SourceLeftChain.referencePath_within_trace step.route.chain
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

namespace CanonicalTagHistory

private theorem NewStep.tensorConclusion_ne_futureCandidate
    {certificate : Certificate} {state before after : ReservationState}
    (invariant : SchedulerInvariant certificate state)
    (step : NewStep certificate before after)
    (candidate : FutureNewCandidateAt certificate state)
    {rawAge : RawTokenAge}
    (selectedMarked :
      state.core.marks[step.stackResult.vertex]? = some (some rawAge)) :
    step.tensor.conclusion ≠ candidate.tensor.conclusion := by
  intro sameConclusion
  have currentMembership :
      Link.tensor step.tensor.storedLeft step.tensor.storedRight
          step.tensor.conclusion ∈ certificate.links :=
    List.mem_of_getElem? step.tensorValid.2.1
  have candidateMembership :
      Link.tensor candidate.tensor.storedLeft candidate.tensor.storedRight
          candidate.tensor.conclusion ∈ certificate.links :=
    List.mem_of_getElem? candidate.tensor_valid.2.1
  have sameLink :=
    UnificationState.StructurallyWellFormed.producerLink_unique
      (conclusion := step.tensor.conclusion) invariant.structural
      currentMembership (by simp [Link.produces])
      candidateMembership (by simp [Link.produces, sameConclusion])
  injection sameLink with leftEq rightEq _conclusionEq
  have candidateHeadUnmarked :
      state.core.marks[candidate.head]? = some none :=
    invariant.queued_vertices_unmarked candidate.head candidate.work.mem_queued
  have currentPremise := step.tensorValid.2.2.2
  have candidatePremise := candidate.tensor_valid.2.2.2
  cases currentSide : step.tensor.side <;>
      cases candidateSide : candidate.tensor.side
  · have headEq : candidate.head = step.stackResult.vertex := by
      simp [TensorBelow.premise, TensorPremiseSide.premise,
        currentSide] at currentPremise
      simp [TensorBelow.premise, TensorPremiseSide.premise,
        candidateSide] at candidatePremise
      exact candidatePremise.trans (leftEq.symm.trans currentPremise.symm)
    rw [headEq, selectedMarked] at candidateHeadUnmarked
    simp at candidateHeadUnmarked
  · have mateEq : candidate.tensor.mate = step.stackResult.vertex := by
      simp [TensorBelow.mate, TensorPremiseSide.mate, candidateSide]
      simp [TensorBelow.premise, TensorPremiseSide.premise,
        currentSide] at currentPremise
      exact leftEq.symm.trans currentPremise.symm
    have candidateMateUnmarked := candidate.mate_unmarked
    rw [mateEq, selectedMarked] at candidateMateUnmarked
    simp at candidateMateUnmarked
  · have mateEq : candidate.tensor.mate = step.stackResult.vertex := by
      simp [TensorBelow.mate, TensorPremiseSide.mate, candidateSide]
      simp [TensorBelow.premise, TensorPremiseSide.premise,
        currentSide] at currentPremise
      exact rightEq.symm.trans currentPremise.symm
    have candidateMateUnmarked := candidate.mate_unmarked
    rw [mateEq, selectedMarked] at candidateMateUnmarked
    simp at candidateMateUnmarked
  · have headEq : candidate.head = step.stackResult.vertex := by
      simp [TensorBelow.premise, TensorPremiseSide.premise,
        currentSide] at currentPremise
      simp [TensorBelow.premise, TensorPremiseSide.premise,
        candidateSide] at candidatePremise
      exact candidatePremise.trans (rightEq.symm.trans currentPremise.symm)
    rw [headEq, selectedMarked] at candidateHeadUnmarked
    simp at candidateHeadUnmarked

/-- One exact reference-switching path from the parent reservation's stored
left endpoint to the child reservation's stored left endpoint that omits the
specified target vertex. -/
def CommitmentEdgeTargetAvoidingPath
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (parent child : RawTokenAge) (target : Vertex) : Prop :=
  ∃ (parentEvent childEvent : ReservationEvent certificate)
      (path : certificate.referenceSwitchingGraph.EdgeSimplePath),
    tagHistory.reservationLedger[parent]? = some parentEvent ∧
      tagHistory.reservationLedger[child]? = some childEvent ∧
      path.start = parentEvent.search.result.left ∧
      path.finish = childEvent.search.result.left ∧
      target ∉ path.vertices

/-- An adjacent retained sigma commitment admits a reference-switching path
that avoids the conclusion of any supplied future `new` candidate, provided
the exact child ledger event does not touch that conclusion.

The `childUntouched` ledger-child law is an explicit input.  This module does
not derive that law or its global availability from history invariants. This
is one adjacent-edge result, not arbitrary whole-spine composition, a global
raw-seam discharge, or scheduler progress. -/
theorem commitmentEdge_referencePath_avoiding
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (invariant : SchedulerInvariant certificate state)
    (candidate : FutureNewCandidateAt certificate state)
    {position parent child : RawTokenAge}
    (parentAt : state.stack.sigma[position]? = some parent)
    (childAt : state.stack.sigma[position + 1]? = some child)
    (childUntouched : ∀ {event : ReservationEvent certificate},
      event ∈ tagHistory.reservationLedger → event.rawAge = child →
        ¬ event.Touched candidate.tensor.conclusion) :
    tagHistory.CommitmentEdgeTargetAvoidingPath parent child
      candidate.tensor.conclusion := by
  rcases tagHistory.commitmentEdge_referencePath invariant parentAt childAt with
    ⟨edgeBefore, edgeAfter, edgeStep, parentEvent, parentComponent,
      childComponent, parentEventUsed, parentForestUsed, parentOwned,
      childEventUsed, childForestUsed, childOwned, parentAnchor,
      _oldCommittedPath, childAnchor, _oldCanonicalPath, parentLookup,
      edgeChildLookup, _parentRawAge, _parentEq, childEq, selectedMarked,
      parentComponentLookup, _parentDerivation, _parentLink, _parentWitness,
      parentAccounted, selectedOwned, _parentLeftOwned, childComponentLookup,
      _childDerivation, _childLink, _childWitness, childAccounted, reachedOwned,
      parentAnchorStarts, parentAnchorFinishes, parentAnchorWithin,
      _oldCommittedStarts, _oldCommittedFinishes, childAnchorStarts,
      childAnchorFinishes, childAnchorWithin, _oldCanonicalStarts,
      _oldCanonicalFinishes, _reachedEndpoint⟩
  have targetNotParentOwned :
      candidate.tensor.conclusion ∉ parentOwned :=
    candidate.tensorConclusion_not_owned invariant
      parentComponentLookup parentAccounted
  have targetNotChildOwned :
      candidate.tensor.conclusion ∉ childOwned :=
    candidate.tensorConclusion_not_owned invariant
      childComponentLookup childAccounted
  have selectedNe :
      edgeStep.stackResult.vertex ≠ candidate.tensor.conclusion := by
    intro same
    apply targetNotParentOwned
    simpa [same] using selectedOwned
  have ownConclusionNe :
      edgeStep.tensor.conclusion ≠ candidate.tensor.conclusion :=
    NewStep.tensorConclusion_ne_futureCandidate invariant edgeStep candidate
      selectedMarked
  have parentAvoids :
      candidate.tensor.conclusion ∉ parentAnchor.vertices := by
    intro membership
    exact targetNotParentOwned
      (parentAnchorWithin candidate.tensor.conclusion membership)
  have reversedParentAvoids :
      candidate.tensor.conclusion ∉ parentAnchor.reverse.vertices := by
    simpa using parentAvoids
  have childAvoids :
      candidate.tensor.conclusion ∉ childAnchor.vertices := by
    intro membership
    exact targetNotChildOwned
      (childAnchorWithin candidate.tensor.conclusion membership)
  rcases edgeStep.selectedToReachedReferencePath_avoiding
      invariant.structural selectedNe ownConclusionNe
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

end CanonicalTagHistory

end SequentialFigure7
end ProofNetIR
