/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7CommitmentSpine
import ProofNetIR.SequentialFigure7RawMarkReservationAnchor
import ProofNetIR.SequentialFigure7RawMarkHistory
import ProofNetIR.SequentialFigure7TerminalPartnerGeometry

namespace ProofNetIR

/-!
# Figure-7 commitment-edge reference paths

Every adjacent pair of raw ages retained in a canonical scheduler state's
`sigma` stack determines one exact historical `new` step.  The parent
reservation anchor, the step's tensor/NEXTAXIOM path, and the child
reservation anchor compose into an occurrence-aware simple path between the
canonical left endpoints of the two reservation events.  The result retains
the exact final component, owned-occurrence, and accounting evidence for both
endpoints.

This module proves only a path for one adjacent retained sigma edge.  It does
not prove that the path avoids a future tensor conclusion, discharge any raw
seam, establish enabledness or progress, prove pure-worklist completeness,
remove the recursive fallback, or derive a complexity bound.
-/

namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge
open SequentialUnification

namespace CanonicalTagHistory

private theorem commit_selected_finalRawMarked
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    {event : ReservationEvent certificate}
    {parent child : RawTokenAge}
    (membership : event ∈ tagHistory.reservationLedger)
    (commits : event.Commits parent child) :
    ∃ (before after : ReservationState)
        (step : NewStep certificate before after),
      event = .new step ∧
        parent = step.stackResult.rawAge ∧
        child = (ReservationEvent.new step).rawAge ∧
        state.core.marks[step.stackResult.vertex]? = some (some parent) := by
  cases commits with
  | @new before after step =>
      refine ⟨before, after, step, rfl, rfl, rfl, ?_⟩
      apply tagHistory.final_rawMarked_iff.mpr
      induction tagHistory with
      | empty =>
          simp [CanonicalTagHistory.reservationLedger] at membership
      | init initial =>
          simp [CanonicalTagHistory.reservationLedger] at membership
      | @later priorState result priorHistory invariant dispatch prior
          evidence induction =>
          simp only [CanonicalTagHistory.reservationLedger,
            List.mem_append] at membership
          rcases membership with old | current
          · exact Or.inl (induction old)
          · cases evidence with
            | concl conclStep =>
                simp [DispatchTagEvidence.reservationEvents] at current
            | nop nopStep =>
                simp [DispatchTagEvidence.reservationEvents] at current
            | new newStep =>
                have same : ReservationEvent.new step =
                    ReservationEvent.new newStep := by
                  simpa [DispatchTagEvidence.reservationEvents] using current
                cases same
                exact Or.inr ⟨rfl, rfl⟩
            | wait waitStep =>
                simp [DispatchTagEvidence.reservationEvents] at current
            | forward forwardStep =>
                simp [DispatchTagEvidence.reservationEvents] at current
            | unifyPayload unifyStep =>
                simp [DispatchTagEvidence.reservationEvents] at current

private theorem tensorReferencePath
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {left right conclusion : Vertex}
    (membership : Link.tensor left right conclusion ∈ certificate.links) :
    ∃ path : certificate.referenceSwitchingGraph.EdgeSimplePath,
      path.start = left ∧ path.finish = right ∧
        path.vertices = [left, conclusion, right] := by
  have wellFormed :
      certificate.LinkWellFormed (.tensor left right conclusion) :=
    structural.2.2.2.2.1 _ membership
  have referenceTensorEdges :=
    UnificationMarking.referenceSwitchingGraph_tensorEdges
      certificate membership
  let leftEdge : Edge := { first := left, second := conclusion }
  let rightEdge : Edge := { first := right, second := conclusion }
  have leftEdgeMembership :
      leftEdge ∈ certificate.referenceSwitchingGraph.edges := by
    simpa [leftEdge] using referenceTensorEdges.1
  have rightEdgeMembership :
      rightEdge ∈ certificate.referenceSwitchingGraph.edges := by
    simpa [rightEdge] using referenceTensorEdges.2
  rcases List.getElem?_of_mem leftEdgeMembership with
    ⟨leftIndex, leftEdgeLookup⟩
  rcases List.getElem?_of_mem rightEdgeMembership with
    ⟨rightIndex, rightEdgeLookup⟩
  let leftDirected : certificate.referenceSwitchingGraph.DirectedEdge := {
    index := leftIndex
    edge := leftEdge
    lookup := leftEdgeLookup
    forward := true }
  let rightDirected : certificate.referenceSwitchingGraph.DirectedEdge := {
    index := rightIndex
    edge := rightEdge
    lookup := rightEdgeLookup
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

private theorem tensorBelowReferencePath
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
      refine ⟨path, ?_, ?_, ?_⟩
      · exact pathStarts.trans vertexLeft.symm
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
      · change path.finish = vertex
        exact pathFinishes.trans vertexRight.symm
      · simpa [Graph.EdgeSimplePath.reverse, TensorBelow.mate,
          TensorPremiseSide.mate, sideEquation] using pathStarts
      · rw [Graph.EdgeSimplePath.reverse_vertices, pathVertices]
        simp [TensorBelow.premise, TensorPremiseSide.premise,
          TensorBelow.mate, TensorPremiseSide.mate, sideEquation,
          premise]

private theorem tensorBelowMateComplexityLtConclusion
    {certificate : Certificate} {vertex : Vertex} {tensor : TensorBelow}
    (valid : tensor.Valid certificate certificate.consumerIndex vertex) :
    certificate.formulaComplexityAt tensor.mate <
      certificate.formulaComplexityAt tensor.conclusion := by
  simpa [Certificate.linkConclusionComplexity] using
    valid.2.2.1.premise_complexity_lt_conclusion
      (premise := tensor.mate) (by
        cases sideEquation : tensor.side <;>
          simp [Link.premises, TensorBelow.mate,
            TensorPremiseSide.mate, sideEquation])

private theorem newStepSelectedToReachedReferencePath
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {before after : ReservationState}
    (step : NewStep certificate before after) :
    ∃ path : certificate.referenceSwitchingGraph.EdgeSimplePath,
      path.start = step.stackResult.vertex ∧
        path.finish = step.reached := by
  rcases tensorBelowReferencePath structural step.tensorValid with
    ⟨tensorPath, tensorStarts, tensorFinishes, _tensorVertices⟩
  have mateBelow := tensorBelowMateComplexityLtConclusion step.tensorValid
  have reachedRank := step.route.reachable.formulaComplexity_le structural
  have reachedNe : step.reached ≠ step.tensor.conclusion := by
    intro same
    rw [same] at reachedRank
    omega
  rcases sourceLeftRegionVertex_referencePath_avoiding structural
      (.visited step.route.reachable) mateBelow reachedNe with
    ⟨routePath, routeStarts, routeFinishes, _routeAvoids⟩
  have meeting : tensorPath.finish = routePath.start := by
    rw [tensorFinishes, routeStarts]
  have routeWalk :
      certificate.referenceSwitchingGraph.EdgeWalk tensorPath.finish
        routePath.traversed routePath.finish := by
    rw [meeting]
    exact routePath.walk
  have combined :
      certificate.referenceSwitchingGraph.EdgeWalk tensorPath.start
        (tensorPath.traversed ++ routePath.traversed) routePath.finish :=
    tensorPath.walk.trans routeWalk
  rcases combined.toEdgeSimplePathWithVerticesSubset with
    ⟨path, pathStarts, pathFinishes, _subset⟩
  exact ⟨path, pathStarts.trans tensorStarts,
    pathFinishes.trans routeFinishes⟩

/-- Proof-relevant path data for one adjacent retained `sigma` commitment.

The canonical path runs from the parent reservation's stored left endpoint to
the child reservation's stored left endpoint.  Its construction retains the
parent anchor, the committed `new`-step path, the child anchor, and exact final
owned-occurrence accounting for both chronological raw ages. -/
def CommitmentEdgeReferencePath
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (parent child : RawTokenAge) : Prop :=
  ∃ (before after : ReservationState)
      (step : NewStep certificate before after)
      (parentEvent : ReservationEvent certificate)
      (parentComponent childComponent : UnificationComponent)
      (parentEventUsed parentForestUsed parentOwned : List Nat)
      (childEventUsed childForestUsed childOwned : List Nat)
      (parentAnchor committedPath childAnchor canonicalPath :
        certificate.referenceSwitchingGraph.EdgeSimplePath),
    tagHistory.reservationLedger[parent]? = some parentEvent ∧
      tagHistory.reservationLedger[child]? =
        some (ReservationEvent.new step) ∧
      parentEvent.rawAge = parent ∧
      parent = step.stackResult.rawAge ∧
      child = (ReservationEvent.new step).rawAge ∧
      state.core.marks[step.stackResult.vertex]? = some (some parent) ∧
      state.core.components[state.core.representative parent]? =
        some (some parentComponent) ∧
      certificate.OccurrenceDerivation parentComponent.tree
        parentComponent.frontier parentEventUsed parentOwned ∧
      parentEvent.linkIndex ∈ parentEventUsed ∧
      certificate.ComponentOccurrenceWitness parentComponent
        parentForestUsed parentOwned ∧
      Certificate.OwnedOccurrenceAccounted state.core
        (state.core.representative parent) parentComponent parentOwned ∧
      step.stackResult.vertex ∈ parentOwned ∧
      parentEvent.search.result.left ∈ parentOwned ∧
      state.core.components[state.core.representative child]? =
        some (some childComponent) ∧
      certificate.OccurrenceDerivation childComponent.tree
        childComponent.frontier childEventUsed childOwned ∧
      (ReservationEvent.new step).linkIndex ∈ childEventUsed ∧
      certificate.ComponentOccurrenceWitness childComponent
        childForestUsed childOwned ∧
      Certificate.OwnedOccurrenceAccounted state.core
        (state.core.representative child) childComponent childOwned ∧
      step.reached ∈ childOwned ∧
      parentAnchor.start = step.stackResult.vertex ∧
      parentAnchor.finish = parentEvent.search.result.left ∧
      (∀ vertex ∈ parentAnchor.vertices, vertex ∈ parentOwned) ∧
      committedPath.start = step.stackResult.vertex ∧
      committedPath.finish = step.reached ∧
      childAnchor.start = step.reached ∧
      childAnchor.finish = (ReservationEvent.new step).search.result.left ∧
      (∀ vertex ∈ childAnchor.vertices, vertex ∈ childOwned) ∧
      canonicalPath.start = parentEvent.search.result.left ∧
      canonicalPath.finish = (ReservationEvent.new step).search.result.left ∧
      (step.reached = step.search.left ∨ step.reached = step.search.right)

/-- Every adjacent retained `sigma` edge has a canonical parent-left to
child-left reference path with exact historical and final ownership evidence.

This theorem does not prove target avoidance, any raw seam, or progress. -/
theorem commitmentEdge_referencePath
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (invariant : SchedulerInvariant certificate state)
    {position parent child : RawTokenAge}
    (parentAt : state.stack.sigma[position]? = some parent)
    (childAt : state.stack.sigma[position + 1]? = some child) :
    tagHistory.CommitmentEdgeReferencePath parent child := by
  rcases tagHistory.commitmentSpine position parent child parentAt childAt with
    ⟨childEvent, childLookup, commits⟩
  have childMembership : childEvent ∈ tagHistory.reservationLedger :=
    List.mem_of_getElem? childLookup
  rcases commit_selected_finalRawMarked tagHistory childMembership commits with
    ⟨before, after, step, childEventEq, parentEq, childEq, selectedMarked⟩
  subst childEvent
  rcases tagHistory.rawMarked_reservationEvent_referenceAnchors invariant
      selectedMarked with
    ⟨parentEvent, parentComponent, parentEventUsed, parentForestUsed,
      parentOwned, leftPath, _rightPath, parentLookup, parentRawAge,
      parentComponentLookup, parentDerivation, parentLink, parentWitness,
      parentAccounted, selectedOwned, parentLeftOwned, _parentRightOwned,
      leftStarts, leftFinishes, leftWithin, _rightStarts, _rightFinishes,
      _rightWithin⟩
  have childEventMembership :
      ReservationEvent.new step ∈ tagHistory.reservationLedger := by
    simpa using childMembership
  rcases tagHistory.reservationLedger_axiomEndpoints_accounted
      invariant.structural childEventMembership with
    ⟨childComponent, childEventUsed, childForestUsed, childOwned,
      childComponentLookup, childDerivation, childLink, childWitness,
      childAccounted, childLeftOwned, childRightOwned⟩
  have childComponentLookupAtAge :
      state.core.components[state.core.representative child]? =
        some (some childComponent) := by
    simpa [childEq] using childComponentLookup
  have childAccountedAtAge :
      Certificate.OwnedOccurrenceAccounted state.core
        (state.core.representative child) childComponent childOwned := by
    simpa [childEq] using childAccounted
  have reachedEndpoint :
      step.reached = step.search.left ∨ step.reached = step.search.right := by
    rcases step.route.storedEndpoints with
      ⟨reachedLeft, _partnerRight⟩ | ⟨reachedRight, _partnerLeft⟩
    · exact Or.inl reachedLeft
    · exact Or.inr reachedRight
  have reachedOwned : step.reached ∈ childOwned := by
    rcases reachedEndpoint with reachedLeft | reachedRight
    · rw [reachedLeft]
      simpa [ReservationEvent.search, ReservationSearchEvent.ofNew] using
        childLeftOwned
    · rw [reachedRight]
      simpa [ReservationEvent.search, ReservationSearchEvent.ofNew] using
        childRightOwned
  rcases childWitness.referencePath_within_owned reachedOwned
      childLeftOwned with
    ⟨childAnchor, childAnchorStarts, childAnchorFinishes,
      childAnchorWithin⟩
  rcases newStepSelectedToReachedReferencePath invariant.structural step with
    ⟨selectedPath, selectedStarts, selectedFinishes⟩
  have meeting : leftPath.reverse.finish = selectedPath.start := by
    change leftPath.start = selectedPath.start
    rw [leftStarts, selectedStarts]
  have selectedWalk :
      certificate.referenceSwitchingGraph.EdgeWalk leftPath.reverse.finish
        selectedPath.traversed selectedPath.finish := by
    rw [meeting]
    exact selectedPath.walk
  have combined :
      certificate.referenceSwitchingGraph.EdgeWalk leftPath.reverse.start
        (leftPath.reverse.traversed ++ selectedPath.traversed)
        selectedPath.finish :=
    leftPath.reverse.walk.trans selectedWalk
  have childWalk :
      certificate.referenceSwitchingGraph.EdgeWalk selectedPath.finish
        childAnchor.traversed childAnchor.finish := by
    rw [selectedFinishes, ← childAnchorStarts]
    exact childAnchor.walk
  have complete := combined.trans childWalk
  rcases complete.toEdgeSimplePathWithVerticesSubset with
    ⟨canonicalPath, pathStarts, pathFinishes, _pathSubset⟩
  refine ⟨before, after, step, parentEvent, parentComponent, childComponent,
    parentEventUsed, parentForestUsed, parentOwned, childEventUsed,
    childForestUsed, childOwned, leftPath, selectedPath, childAnchor,
    canonicalPath, parentLookup, childLookup, parentRawAge, parentEq, childEq,
    selectedMarked, ?_, parentDerivation, parentLink, parentWitness, ?_,
    selectedOwned, parentLeftOwned, childComponentLookupAtAge,
    childDerivation, childLink, childWitness, childAccountedAtAge,
    reachedOwned, leftStarts, leftFinishes, leftWithin, selectedStarts,
    selectedFinishes, childAnchorStarts, childAnchorFinishes,
    childAnchorWithin, ?_, ?_, reachedEndpoint⟩
  · simpa [parentRawAge] using parentComponentLookup
  · simpa [parentRawAge] using parentAccounted
  · exact pathStarts.trans leftFinishes
  · exact pathFinishes.trans childAnchorFinishes

end CanonicalTagHistory
end SequentialFigure7
end ProofNetIR
