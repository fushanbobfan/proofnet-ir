/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7ActiveTopDebtParentExternalCommitmentOutcome

/-!
# Active-top debt external parent endpoint crossing

Both older branches of the external parent commitment outcome now carry an
exact reference-switching path from the active occurrence carrier to their
external continuation endpoint.  Each path retains one concrete stored-edge
occurrence crossing from the active owned region to its complement.

This is a geometric failure reduction.  It does not classify the crossing as
a distinct raw payer, prove endpoint re-entry, return a ready-tail witness,
derive the history-tail law, or establish progress or completion.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerBridge

/-- An exact reference-switching path from one active occurrence carrier to
an external endpoint, together with one stored-edge crossing of its boundary. -/
def ActiveCarrierExternalEndpointCrossing
    (certificate : Certificate) (owned : List Vertex) (endpoint : Vertex) : Prop :=
  ∃ (path : certificate.referenceSwitchingGraph.EdgeSimplePath)
      (directed : certificate.referenceSwitchingGraph.DirectedEdge),
    path.start ∈ owned ∧
      path.finish = endpoint ∧
      directed ∈ path.traversed ∧
      directed.source ∈ owned ∧
      directed.target ∉ owned

private theorem representative_eq_of_sigmaAt
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
  have boundaryLeRawAge : boundary ≤ rawAge := sigmaBoundary?_le boundaryLookup
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

private theorem externalEndpointCrossing
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    (connected : certificate.ReferenceSwitchingConnected)
    {component : UnificationComponent} {usedLinks owned : List Nat}
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component usedLinks owned)
    {start endpoint : Vertex}
    (startOwned : start ∈ owned)
    (endpointBound : endpoint < certificate.formulas.size)
    (endpointOutside : endpoint ∉ owned) :
    ActiveCarrierExternalEndpointCrossing certificate owned endpoint := by
  have startBound : start < certificate.formulas.size :=
    occurrence.derivation.owned_inBounds structural start startOwned
  have graphStartBound : start < certificate.referenceSwitchingGraph.vertexCount := by
    simpa [Certificate.referenceSwitchingGraph, Certificate.fullGraph,
      Graph.retainEdges] using startBound
  have graphEndpointBound :
      endpoint < certificate.referenceSwitchingGraph.vertexCount := by
    simpa [Certificate.referenceSwitchingGraph, Certificate.fullGraph,
      Graph.retainEdges] using endpointBound
  have zeroToStart : certificate.referenceSwitchingGraph.Walk 0 start :=
    connected.2 start graphStartBound
  have zeroToEndpoint : certificate.referenceSwitchingGraph.Walk 0 endpoint :=
    connected.2 endpoint graphEndpointBound
  have startToEndpoint := zeroToStart.symm.trans zeroToEndpoint
  rcases startToEndpoint.toSimple with ⟨_steps, _visited, simple⟩
  rcases simple.liftToEdgeSimplePathWithEdges
      (fun _ membership => membership) with
    ⟨path, pathStarts, pathFinishes, _pathVertices, _pathEdges⟩
  have pathStartOwned : path.start ∈ owned := by
    simpa [pathStarts] using startOwned
  have finishMembership : path.finish ∈ path.vertices := by
    simpa [Graph.EdgeSimplePath.vertices] using
      path.walk.finish_mem_visitedVertices
  have finishRejected : owned.contains path.finish = false := by
    simpa [pathFinishes] using endpointOutside
  rcases path.exists_traversed_boundary_of_start_true
      (fun vertex ↦ owned.contains vertex) (by simpa using pathStartOwned)
      ⟨path.finish, finishMembership, finishRejected⟩ with
    ⟨directed, directedMembership, sourceAccepted, targetRejected⟩
  exact ⟨path, directed, pathStartOwned, pathFinishes, directedMembership,
    by simpa using sourceAccepted, by simpa using targetRejected⟩

private theorem olderCommitment_endpointCrossing
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    (connected : certificate.ReferenceSwitchingConnected)
    (invariant : SchedulerInvariant certificate state)
    {first active : RawTokenAge}
    {component : UnificationComponent} {usedLinks owned : List Nat}
    (componentLookup : state.core.components[active]? = some (some component))
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component usedLinks owned)
    (split : tagHistory.StrictOlderCommitmentSplit first active)
    {endpoint : Vertex}
    (endpointBound : endpoint < certificate.formulas.size)
    (endpointOutside : endpoint ∉ owned) :
    ActiveCarrierExternalEndpointCrossing certificate owned endpoint := by
  rcases split with
    ⟨position, edgeCount, predecessor, _firstAt, _predecessorAt, activeAt,
      _representativeOlder, commitment⟩
  rcases commitment with
    ⟨before, after, step, parentEvent, parentComponent, childComponent,
      parentEventUsed, parentForestUsed, parentOwned, childEventUsed,
      childForestUsed, childOwned, parentAnchor, committedPath, childAnchor,
      canonicalPath, parentLookup, childLookup, parentRawAge, parentEq, childEq,
      selectedMarked, parentComponentLookup, parentDerivation, parentLink,
      parentWitness, parentAccounted, selectedOwned, parentLeftOwned,
      childComponentLookup, childDerivation, childLink, childWitness,
      childAccounted, reachedOwned, parentAnchorStarts, parentAnchorFinishes,
      parentAnchorWithin, committedStarts, committedFinishes, childAnchorStarts,
      childAnchorFinishes, childAnchorWithin, canonicalStarts,
      canonicalFinishes, reachedEndpoint⟩
  have activeRoot : state.core.representative active = active :=
    representative_eq_of_sigmaAt invariant activeAt
  have childComponentLookupAtActive :
      state.core.components[active]? = some (some childComponent) := by
    rw [activeRoot] at childComponentLookup
    exact childComponentLookup
  have childComponentEq : childComponent = component := by
    exact Option.some.inj
      (Option.some.inj (childComponentLookupAtActive.symm.trans componentLookup))
  subst childComponent
  have childOwnedEq : childOwned = owned :=
    Certificate.OccurrenceDerivation.owned_unique invariant.structural
      childDerivation occurrence.derivation
  have childLeftOwned :
      (ReservationEvent.new step).search.result.left ∈ owned := by
    have finishInChild : childAnchor.finish ∈ childOwned := by
      have finishInVertices : childAnchor.finish ∈ childAnchor.vertices := by
        simpa [Graph.EdgeSimplePath.vertices] using
          childAnchor.walk.finish_mem_visitedVertices
      exact childAnchorWithin childAnchor.finish finishInVertices
    simpa [childOwnedEq, childAnchorFinishes] using finishInChild
  exact externalEndpointCrossing invariant.structural connected occurrence
    childLeftOwned endpointBound endpointOutside

/-- The external parent commitment normal form after its older endpoints have
been connected to the active occurrence carrier and one exact boundary edge
has been retained. -/
inductive ActiveCarrierParentExternalCommitmentCrossingOutcome
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (activeRawAge : RawTokenAge) (owned : List Vertex) : Prop where
  | rawOutside
      (sibling : Vertex)
      (unmarked : state.core.marks[sibling]? = some none)
      (outside : sibling ∉ owned) :
      ActiveCarrierParentExternalCommitmentCrossingOutcome tagHistory
        activeRawAge owned
  | olderFuture
      (conclusion : Vertex) (boundary : RawTokenAge)
      (work : FutureWorkAt state boundary conclusion)
      (older : boundary < activeRawAge)
      (commitmentSplit :
        tagHistory.StrictOlderCommitmentSplit boundary activeRawAge)
      (outside : conclusion ∉ owned)
      (crossing :
        ActiveCarrierExternalEndpointCrossing certificate owned conclusion) :
      ActiveCarrierParentExternalCommitmentCrossingOutcome tagHistory
        activeRawAge owned
  | olderMarked
      (conclusion : Vertex) (conclusionAge : RawTokenAge)
      (marked : state.core.marks[conclusion]? = some (some conclusionAge))
      (olderRepresentative :
        state.core.representative conclusionAge < activeRawAge)
      (commitmentSplit : tagHistory.StrictOlderCommitmentSplit
        (state.core.representative conclusionAge) activeRawAge)
      (outside : conclusion ∉ owned)
      (crossing :
        ActiveCarrierExternalEndpointCrossing certificate owned conclusion) :
      ActiveCarrierParentExternalCommitmentCrossingOutcome tagHistory
        activeRawAge owned

namespace ActiveCarrierParentExternalCommitmentOutcome

/-- Connect both older external endpoints to the active occurrence carrier
through the correct reference switching and retain an exact boundary crossing. -/
theorem endpointCrossing
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {activeRawAge : RawTokenAge} {owned : List Vertex}
    (outcome : ActiveCarrierParentExternalCommitmentOutcome tagHistory
      activeRawAge owned)
    (connected : certificate.ReferenceSwitchingConnected)
    (invariant : SchedulerInvariant certificate state)
    {component : UnificationComponent} {usedLinks : List Nat}
    (componentLookup :
      state.core.components[activeRawAge]? = some (some component))
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component usedLinks owned) :
    ActiveCarrierParentExternalCommitmentCrossingOutcome tagHistory
      activeRawAge owned := by
  cases outcome with
  | rawOutside sibling unmarked outside =>
      exact .rawOutside sibling unmarked outside
  | olderFuture conclusion boundary work older split outside =>
      have endpointUnmarked : state.core.marks[conclusion]? = some none :=
        invariant.queued_vertices_unmarked conclusion work.mem_queued
      have coreMarksSize : state.core.marks.size = certificate.formulas.size := by
        rw [invariant.realizesSigma.marks_eq]
        exact invariant.stack_wellShaped.marks_size
      have endpointBound : conclusion < certificate.formulas.size := by
        rcases Array.getElem?_eq_some_iff.mp endpointUnmarked with
          ⟨markBound, _markValue⟩
        simpa [coreMarksSize] using markBound
      exact .olderFuture conclusion boundary work older split outside
        (olderCommitment_endpointCrossing connected invariant componentLookup
          occurrence split endpointBound outside)
  | olderMarked conclusion conclusionAge marked older split outside =>
      have coreMarksSize : state.core.marks.size = certificate.formulas.size := by
        rw [invariant.realizesSigma.marks_eq]
        exact invariant.stack_wellShaped.marks_size
      have endpointBound : conclusion < certificate.formulas.size := by
        rcases Array.getElem?_eq_some_iff.mp marked with
          ⟨markBound, _markValue⟩
        simpa [coreMarksSize] using markBound
      exact .olderMarked conclusion conclusionAge marked older split outside
        (olderCommitment_endpointCrossing connected invariant componentLookup
          occurrence split endpointBound outside)

end ActiveCarrierParentExternalCommitmentOutcome

end SequentialFigure7
end ProofNetIR
