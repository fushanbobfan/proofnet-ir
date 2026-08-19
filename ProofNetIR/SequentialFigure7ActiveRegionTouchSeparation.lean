/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7CommitmentBlockerMaximality
import ProofNetIR.SequentialFigure7CommitmentIntervalTargetAvoidance
import ProofNetIR.SequentialFigure7ActiveRegionTouchOrder

/-!
# Figure-7 active-region touch separation

Eliminates every authentic historical reservation-event touch from the
complete source-left region of an active `NewGuard`. The proof closes both
branches of commitment-blocker maximality: a target-avoiding commitment path
contradicts reference-switching acyclicity, while an equal-boundary
stored-left callback trace contradicts the unique active tensor edge once a
conclusion-avoiding active-mate anchor is present.

The public anchor carrier lets later raw-mark consumers supply this geometry
without manufacturing a `ReservationEvent.Touched` witness. All maximality,
callback, component, and exact-walk machinery remains private to this module.

This module does not construct an execution, prove raw-mark readiness,
establish `OperationalNewReadyAt` or `NewEnabled`, or imply scheduler
progress, totality, worklist completeness, fallback removal, token-age
scheduling, or whole-program linearity.
-/

namespace ProofNetIR
namespace Graph

/-- an exact tree edge has no alternate exact walk avoiding its
stored occurrence index. -/
private theorem IsTree.no_alternateEdgeWalk {graph : Graph}
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

end Graph

namespace SequentialFigure7

open SequentialUnification
open SequentialSchedulerState
open SequentialSchedulerBridge

private theorem parLeftEdge_mem_leftRetained_local
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

private theorem sourceLeftStep_referenceDirectedEdge_exact
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
        exact parLeftEdge_mem_leftRetained_local membership
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

private theorem SourceLeftReachable.referenceWalk_avoiding_upEdge
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
      rcases sourceLeftStep_referenceDirectedEdge_exact head with
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

private theorem TensorBelow.referenceWalk_avoiding_conclusionEdge
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

private theorem edgeSimplePath_edgeValues_avoid_incident_forbidden
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

private theorem NewStep.tensorConclusion_ne_futureCandidate_local
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

private theorem CanonicalTagHistory.reservationLedger_lookup_of_mem_rawAge
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

private theorem CanonicalTagHistory.reservationEvent_rawAge_eq_of_lookup_local
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

/-- A conclusion-avoiding exact reference anchor from the active mate to one
historical reservation event's stored-left axiom endpoint. -/
def ActiveMateEventAnchor
    {certificate : Certificate} {state : ReservationState}
    (guard : NewGuard certificate state)
    (event : ReservationEvent certificate) : Prop :=
  ∃ path : certificate.referenceSwitchingGraph.EdgeSimplePath,
    path.start = guard.tensor.mate ∧
      path.finish = event.search.result.left ∧
        guard.tensor.conclusion ∉ path.vertices

/-- Any touched vertex already lying in the active mate's complete
source-left region yields an active-mate event anchor. -/
private theorem activeTouch_activeMateEventAnchor
    {certificate : Certificate} {state : ReservationState}
    (correct : certificate.DeclarativelyCorrect)
    (guard : NewGuard certificate state)
    {event : ReservationEvent certificate} {vertex : Vertex}
    (touched : event.Touched vertex)
    (region :
      SourceLeftRegionVertex certificate guard.tensor.mate vertex) :
    ActiveMateEventAnchor guard event := by
  have mateBelow :=
    guard.sourceLeftRegion_formulaComplexity_lt_conclusion correct.1
      (.visited (.refl guard.tensor.mate))
  have vertexBelow :=
    guard.sourceLeftRegion_formulaComplexity_lt_conclusion correct.1 region
  have vertexNe : vertex ≠ guard.tensor.conclusion := by
    intro same
    rw [same] at vertexBelow
    omega
  have eventLeftNe :
      event.search.result.left ≠ guard.tensor.conclusion := by
    intro same
    have axiomMembership :
        Link.axiom event.search.result.left event.search.result.right ∈
          certificate.links :=
      List.mem_of_getElem? event.search.result.exactLink
    have tensorMembership :
        Link.tensor guard.tensor.storedLeft guard.tensor.storedRight
            guard.tensor.conclusion ∈ certificate.links :=
      List.mem_of_getElem? guard.tensor_valid.2.1
    exact correct.1.axiomEndpoint_ne_connectiveConclusion
      axiomMembership (Or.inl rfl) tensorMembership
        (by simpa [Link.produces] using same.symm)
  rcases sourceLeftRegionVertex_referencePath_avoiding correct.1
      region mateBelow vertexNe with
    ⟨first, firstStarts, firstFinishes, firstAvoids⟩
  have eventRegion :
      SourceLeftRegionVertex certificate vertex
        event.search.result.left :=
    event.leftEndpoint_sourceLeftRegion_of_touched touched
  rcases sourceLeftRegionVertex_referencePath_avoiding correct.1
      eventRegion vertexBelow eventLeftNe with
    ⟨second, secondStarts, secondFinishes, secondAvoids⟩
  rcases first.connectEraseAvoiding second
      (firstFinishes.trans secondStarts.symm) firstAvoids secondAvoids with
    ⟨path, pathStarts, pathFinishes, pathAvoids⟩
  exact ⟨path, pathStarts.trans firstStarts,
    pathFinishes.trans secondFinishes, pathAvoids⟩

/-- there is no reference walk from a tensor's right premise to its
conclusion if every step has a different stored edge value. -/
private theorem no_referenceAlternateToTensorConclusion
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
  apply correct.referenceSwitchingTree.no_alternateEdgeWalk
    activeDirected exactWalk
  intro directed inWalk sameIndex
  apply avoids directed inWalk
  apply Option.some.inj
  rw [← directed.lookup, ← activeLookup, sameIndex]

namespace CanonicalTagHistory

private theorem representative_eq_of_sigmaAt_local
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
  rcases
      invariant.stack_wellShaped.sigma_partition.boundary_exists rawAgeBound
    with ⟨boundary, boundaryLookup⟩
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

/-- an event and the ledger event at its current representative have
their left axiom endpoints joined inside the same final owned component, hence
away from the active tensor conclusion. -/
private theorem eventLeft_to_representativeEvent_referencePath_avoiding
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate state)
    (guard : NewGuard certificate state)
    {event representativeEvent : ReservationEvent certificate}
    (eventMembership : event ∈ tagHistory.reservationLedger)
    (representativeLookup :
      tagHistory.reservationLedger[state.core.representative event.rawAge]? =
        some representativeEvent) :
    ∃ path : certificate.referenceSwitchingGraph.EdgeSimplePath,
      path.start = event.search.result.left ∧
        path.finish = representativeEvent.search.result.left ∧
          guard.tensor.conclusion ∉ path.vertices := by
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
    tagHistory.reservationEvent_rawAge_eq_of_lookup_local
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
  have conclusionNotEventOwned : guard.tensor.conclusion ∉ eventOwned :=
    guard.tensorConclusion_not_owned invariant eventComponentLookup
      eventAccounted
  refine ⟨path, pathStarts, pathFinishes, ?_⟩
  intro inPath
  exact conclusionNotEventOwned
    (pathWithin guard.tensor.conclusion inPath)

/-- a conclusion-avoiding mate-to-parent path and the stored-left
callback trace cannot coexist. -/
private theorem storedLeft_callbackTrace_conflicts_with_mateToParentPath
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate state)
    (guard : NewGuard certificate state)
    {parentEvent childEvent : ReservationEvent certificate}
    {position : Nat} {parentAge : RawTokenAge}
    (parentAt : state.stack.sigma[position]? = some parentAge)
    (childAt :
      state.stack.sigma[position + 1]? = some guard.head.rawAge)
    (parentLookup :
      tagHistory.reservationLedger[parentAge]? = some parentEvent)
    (prefixPath : certificate.referenceSwitchingGraph.EdgeSimplePath)
    (prefixStarts : prefixPath.start = guard.tensor.mate)
    (prefixFinishes : prefixPath.finish = parentEvent.search.result.left)
    (prefixAvoids : guard.tensor.conclusion ∉ prefixPath.vertices)
    (childMembership : childEvent ∈ tagHistory.reservationLedger)
    (childAge : childEvent.rawAge = guard.head.rawAge)
    (storedLeft : guard.tensor.side = .storedLeft)
    {beforeTrace afterTrace : List Vertex}
    (callbackTrace :
      childEvent.search.result.trace =
        beforeTrace ++ guard.tensor.conclusion ::
          guard.head.vertex :: afterTrace) :
    False := by
  rcases tagHistory.commitmentEdge_referencePath invariant parentAt childAt with
    ⟨edgeBefore, edgeAfter, edgeStep, edgeParentEvent, parentComponent,
      childComponent, parentEventUsed, parentForestUsed, parentOwned,
      childEventUsed, childForestUsed, childOwned, parentAnchor,
      _oldCommittedPath, childAnchor, _oldCanonicalPath, edgeParentLookup,
      edgeChildLookup, _parentRawAge, _parentEq, _childEq, selectedMarked,
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
      tagHistory.reservationLedger[guard.head.rawAge]? = some childEvent :=
    tagHistory.reservationLedger_lookup_of_mem_rawAge
      childMembership childAge
  have callbackEventEq : childEvent = ReservationEvent.new edgeStep := by
    exact Option.some.inj (callbackLookup.symm.trans edgeChildLookup)
  subst childEvent
  have conclusionInTrace :
      guard.tensor.conclusion ∈ edgeStep.search.trace := by
    have inEventTrace :
        guard.tensor.conclusion ∈
          (ReservationEvent.new edgeStep).search.result.trace := by
      rw [callbackTrace]
      simp
    simpa [ReservationEvent.search, ReservationSearchEvent.ofNew] using
      inEventTrace
  have callbackReachable :
      SourceLeftReachable certificate edgeStep.tensor.mate
        guard.tensor.conclusion :=
    edgeStep.route.chain.reachable_of_head_mem
      edgeStep.route.traceHead conclusionInTrace
  have mateBelowConclusion :
      certificate.formulaComplexityAt guard.tensor.mate <
        certificate.formulaComplexityAt guard.tensor.conclusion :=
    guard.sourceLeftRegion_formulaComplexity_lt_conclusion correct.1
      (.visited (.refl _))
  rcases SourceLeftReachable.referenceWalk_avoiding_upEdge correct.1
      callbackReachable mateBelowConclusion with
    ⟨callbackTraversal, callbackWalk, callbackAvoids⟩
  have conclusionNotParentOwned :
      guard.tensor.conclusion ∉ parentOwned :=
    guard.tensorConclusion_not_owned invariant parentComponentLookup
      parentAccounted
  have parentAnchorAvoids :
      guard.tensor.conclusion ∉ parentAnchor.vertices := by
    intro inAnchor
    exact conclusionNotParentOwned
      (parentAnchorWithin guard.tensor.conclusion inAnchor)
  have reversedParentAnchorAvoids :
      guard.tensor.conclusion ∉ parentAnchor.reverse.vertices := by
    simpa using parentAnchorAvoids
  have ownConclusionNe :
      edgeStep.tensor.conclusion ≠ guard.tensor.conclusion :=
    NewStep.tensorConclusion_ne_futureCandidate_local invariant edgeStep
      (guard.futureNewCandidateAt invariant) selectedMarked
  rcases TensorBelow.referenceWalk_avoiding_conclusionEdge
      edgeStep.tensorValid (lower := guard.tensor.mate) ownConclusionNe with
    ⟨tensorTraversal, tensorWalk, tensorAvoids⟩
  have prefixWalk :
      certificate.referenceSwitchingGraph.EdgeWalk guard.tensor.mate
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
      Link.tensor guard.tensor.storedLeft guard.tensor.storedRight
          guard.tensor.conclusion ∈ certificate.links :=
    List.mem_of_getElem? guard.tensor_valid.2.1
  have mateIsRight : guard.tensor.mate = guard.tensor.storedRight := by
    simp [TensorBelow.mate, TensorPremiseSide.mate, storedLeft]
  apply no_referenceAlternateToTensorConclusion correct tensorMembership
    (by simpa [mateIsRight] using alternateWalk)
  intro directed directedMembership
  rcases List.mem_append.mp directedMembership with inPrefix | afterPrefix
  · exact edgeSimplePath_edgeValues_avoid_incident_forbidden
      prefixPath prefixAvoids directed inPrefix
  · rcases List.mem_append.mp afterPrefix with inParent | afterParent
    · exact edgeSimplePath_edgeValues_avoid_incident_forbidden
        parentAnchor.reverse reversedParentAnchorAvoids directed inParent
    · rcases List.mem_append.mp afterParent with inTensor | inCallback
      · simpa [mateIsRight] using tensorAvoids directed inTensor
      · simpa [mateIsRight] using callbackAvoids directed inCallback

/-- the path branch of the same final equal-boundary edge also
conflicts with an anchored older blocker. -/
private theorem commitmentPath_conflicts_with_mateToParentPath
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate state)
    (guard : NewGuard certificate state)
    {parentEvent : ReservationEvent certificate}
    {parentAge : RawTokenAge}
    (parentLookup :
      tagHistory.reservationLedger[parentAge]? = some parentEvent)
    (prefixPath : certificate.referenceSwitchingGraph.EdgeSimplePath)
    (prefixStarts : prefixPath.start = guard.tensor.mate)
    (prefixFinishes :
      prefixPath.finish = parentEvent.search.result.left)
    (prefixAvoids : guard.tensor.conclusion ∉ prefixPath.vertices)
    (suffix : tagHistory.CommitmentEdgeTargetAvoidingPath
      parentAge guard.head.rawAge guard.tensor.conclusion) :
    False := by
  rcases suffix with
    ⟨suffixParent, childEvent, suffixPath, suffixParentLookup,
      childLookup, suffixStarts, suffixFinishes, suffixAvoids⟩
  have suffixParentEq : suffixParent = parentEvent := by
    exact Option.some.inj (suffixParentLookup.symm.trans parentLookup)
  subst suffixParent
  have childMembership : childEvent ∈ tagHistory.reservationLedger :=
    List.mem_of_getElem? childLookup
  have childRawAge : childEvent.rawAge = guard.head.rawAge :=
    tagHistory.reservationEvent_rawAge_eq_of_lookup_local childLookup
  have childRepresentative :
      state.core.representative childEvent.rawAge = guard.head.rawAge := by
    rw [childRawAge]
    exact (guard.head.futureWorkAt invariant).representative_eq_rawAge invariant
  rcases guard.head.activeComponent invariant with
    ⟨activeComponent, _activeUsed, activeOwned, activeLookup,
      activeWitness, activeAccounted, headOwned, _activeRoot⟩
  rcases tagHistory.reservationLedger_axiomEndpoints_accounted
      correct.1 childMembership with
    ⟨childComponent, _childUsed, _childForest, childOwned,
      childComponentLookup, childDerivation, _childLink, _childWitness,
      _childAccounted, childLeftOwned, _childRightOwned⟩
  have childComponentLookupAtActive :
      state.core.components[guard.head.rawAge]? =
        some (some childComponent) := by
    simpa [childRepresentative] using childComponentLookup
  have childComponentEq : childComponent = activeComponent := by
    exact Option.some.inj
      (Option.some.inj
        (childComponentLookupAtActive.symm.trans activeLookup))
  subst childComponent
  have childOwnedEq : childOwned = activeOwned :=
    Certificate.OccurrenceDerivation.owned_unique correct.1
      childDerivation activeWitness.derivation
  have childLeftActiveOwned :
      childEvent.search.result.left ∈ activeOwned := by
    rw [← childOwnedEq]
    exact childLeftOwned
  rcases activeWitness.referencePath_within_owned childLeftActiveOwned
      headOwned with
    ⟨activePath, activeStarts, activeFinishes, activeWithin⟩
  have conclusionNotActiveOwned :
      guard.tensor.conclusion ∉ activeOwned :=
    guard.tensorConclusion_not_owned invariant activeLookup activeAccounted
  have activeAvoids : guard.tensor.conclusion ∉ activePath.vertices := by
    intro inPath
    exact conclusionNotActiveOwned
      (activeWithin guard.tensor.conclusion inPath)
  rcases prefixPath.connectEraseAvoiding suffixPath
      (prefixFinishes.trans suffixStarts.symm)
      prefixAvoids suffixAvoids with
    ⟨first, firstStarts, firstFinishes, firstAvoids⟩
  rcases first.connectEraseAvoiding activePath
      (firstFinishes.trans (suffixFinishes.trans activeStarts.symm))
      firstAvoids activeAvoids with
    ⟨bypass, bypassStarts, bypassFinishes, bypassAvoids⟩
  have tensorMembership :
      Link.tensor guard.tensor.storedLeft guard.tensor.storedRight
          guard.tensor.conclusion ∈ certificate.links :=
    List.mem_of_getElem? guard.tensor_valid.2.1
  have combinedStarts : bypass.start = guard.tensor.mate :=
    bypassStarts.trans (firstStarts.trans prefixStarts)
  have combinedFinishes : bypass.finish = guard.head.vertex :=
    bypassFinishes.trans activeFinishes
  have headEquation := guard.tensor_valid.2.2.2
  cases sideEquation : guard.tensor.side with
  | storedLeft =>
      have headIsLeft : guard.head.vertex = guard.tensor.storedLeft := by
        simpa [TensorBelow.premise, TensorPremiseSide.premise,
          sideEquation] using headEquation
      have mateIsRight : guard.tensor.mate = guard.tensor.storedRight := by
        simp [TensorBelow.mate, TensorPremiseSide.mate, sideEquation]
      apply referenceAcyclic_no_tensorBypass correct.1
        correct.referenceSwitchingTree.acyclic tensorMembership bypass.reverse
      · exact combinedFinishes.trans headIsLeft
      · exact combinedStarts.trans mateIsRight
      · simpa using bypassAvoids
  | storedRight =>
      have headIsRight : guard.head.vertex = guard.tensor.storedRight := by
        simpa [TensorBelow.premise, TensorPremiseSide.premise,
          sideEquation] using headEquation
      have mateIsLeft : guard.tensor.mate = guard.tensor.storedLeft := by
        simp [TensorBelow.mate, TensorPremiseSide.mate, sideEquation]
      apply referenceAcyclic_no_tensorBypass correct.1
        correct.referenceSwitchingTree.acyclic tensorMembership bypass
      · exact combinedStarts.trans mateIsLeft
      · exact combinedFinishes.trans headIsRight
      · exact bypassAvoids

/-- a maximal strictly older anchored event extends to a single
mate-to-parent path for the active equal-boundary commitment edge. -/
private theorem maximal_anchor_bridge
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate state)
    (guard : NewGuard certificate state)
    {event : ReservationEvent certificate}
    (eventMembership : event ∈ tagHistory.reservationLedger)
    (eventOlder :
      state.core.representative event.rawAge <
        state.core.representative guard.head.rawAge)
    (eventAnchor : certificate.referenceSwitchingGraph.EdgeSimplePath)
    (eventAnchorStarts : eventAnchor.start = guard.tensor.mate)
    (eventAnchorFinishes :
      eventAnchor.finish = event.search.result.left)
    (eventAnchorAvoids :
      guard.tensor.conclusion ∉ eventAnchor.vertices)
    (maximal : ∀ candidate : ReservationEvent certificate,
      candidate ∈ tagHistory.reservationLedger →
      state.core.representative candidate.rawAge <
          state.core.representative guard.head.rawAge →
      (∃ path : certificate.referenceSwitchingGraph.EdgeSimplePath,
        path.start = guard.tensor.mate ∧
          path.finish = candidate.search.result.left ∧
            guard.tensor.conclusion ∉ path.vertices) →
      state.core.representative candidate.rawAge ≤
        state.core.representative event.rawAge) :
    ∃ (position parent : RawTokenAge)
        (parentEvent : ReservationEvent certificate)
        (path : certificate.referenceSwitchingGraph.EdgeSimplePath),
      state.stack.sigma[position]? = some parent ∧
        state.stack.sigma[position + 1]? = some guard.head.rawAge ∧
        tagHistory.reservationLedger[parent]? = some parentEvent ∧
        path.start = guard.tensor.mate ∧
        path.finish = parentEvent.search.result.left ∧
        guard.tensor.conclusion ∉ path.vertices := by
  let candidate := guard.futureNewCandidateAt invariant
  rcases tagHistory.strictOlderSigmaSplit invariant eventMembership candidate
      eventOlder with
    ⟨startPosition, edgeCount, predecessor, firstAt, predecessorAt,
      childAt, predecessorOlder⟩
  change
    state.stack.sigma[startPosition + edgeCount + 1]? =
      some guard.head.rawAge at childAt
  have firstBound :
      state.core.representative event.rawAge < state.stack.nextAge :=
    invariant.stack_wellShaped.sigma_partition.boundary_lt _
      (List.mem_of_getElem? firstAt)
  rcases tagHistory.reservationLedger_eventAtRawAge
      (state.core.representative event.rawAge) firstBound with
    ⟨firstEvent, firstLookup, _firstEventAge⟩
  rcases tagHistory.eventLeft_to_representativeEvent_referencePath_avoiding
      correct invariant guard eventMembership firstLookup with
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
    have headSeparated : OlderEventFutureWorkTouchSeparated tagHistory :=
      tagHistory.olderEventFutureWorkTouchSeparated invariant.structural
    have intervalPath :
        tagHistory.CommitmentEdgeTargetAvoidingPath
          (state.core.representative event.rawAge) predecessor
          guard.tensor.conclusion := by
      apply tagHistory.commitmentInterval_referencePath_avoiding positive
        firstAt predecessorAt
      intro offset parent child offsetLt parentAt childAtLocal
      apply tagHistory.commitmentEdge_referencePath_avoiding invariant candidate
        parentAt childAtLocal
      intro childEvent childMembership childEventAge conclusionTouched
      have childRoot :=
        representative_eq_of_sigmaAt_local invariant childAtLocal
      have predecessorRoot :=
        representative_eq_of_sigmaAt_local invariant predecessorAt
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
            state.core.representative childEvent.rawAge := by
        rw [childEventAge, childRoot]
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
              startPosition + offset + 1 < startPosition + edgeCount := by
            omega
          have ordered :=
            (List.pairwise_iff_getElem.mp
              invariant.stack_wellShaped.sigma_partition.strictIncreasing)
              (startPosition + offset + 1) (startPosition + edgeCount)
              childPositionBound predecessorPositionBound positionLt
          rw [childValue, predecessorValue] at ordered
          exact Nat.le_of_lt ordered
      have childOlder :
          state.core.representative childEvent.rawAge <
            state.core.representative guard.head.rawAge := by
        rw [childEventAge, childRoot]
        rw [predecessorRoot] at predecessorOlder
        exact Nat.lt_of_le_of_lt childLePredecessor predecessorOlder
      rcases childEvent.touched_candidateConclusion_cases invariant.structural
          candidate conclusionTouched with childMateTouched | childHeadTouched
      · rcases activeTouch_activeMateEventAnchor correct guard
            childMateTouched (.visited (.refl guard.tensor.mate)) with
          ⟨childAnchor, childAnchorStarts, childAnchorFinishes,
            childAnchorAvoids⟩
        have upper := maximal childEvent childMembership childOlder
          ⟨childAnchor, childAnchorStarts, childAnchorFinishes,
            childAnchorAvoids⟩
        exact (Nat.not_lt_of_ge upper firstBeforeChild)
      · exact headSeparated.event_candidate childMembership candidate
          childOlder childHeadTouched
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

/-- no strictly older ledger event carrying an active-mate anchor can
coexist with the exact equal-boundary callback witness. -/
private theorem strictOlder_anchor_not_equalCallbackFailure
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate state)
    (guard : NewGuard certificate state)
    {event childEvent : ReservationEvent certificate}
    (eventMembership : event ∈ tagHistory.reservationLedger)
    (eventOlder :
      state.core.representative event.rawAge <
        state.core.representative guard.head.rawAge)
    (eventAnchor : certificate.referenceSwitchingGraph.EdgeSimplePath)
    (eventAnchorStarts : eventAnchor.start = guard.tensor.mate)
    (eventAnchorFinishes :
      eventAnchor.finish = event.search.result.left)
    (eventAnchorAvoids :
      guard.tensor.conclusion ∉ eventAnchor.vertices)
    (childMembership : childEvent ∈ tagHistory.reservationLedger)
    (childAge : childEvent.rawAge = guard.head.rawAge)
    (sideLeft : guard.tensor.side = .storedLeft)
    {beforeTrace afterTrace : List Vertex}
    (callbackTrace :
      childEvent.search.result.trace =
        beforeTrace ++ guard.tensor.conclusion ::
          guard.head.vertex :: afterTrace) :
    False := by
  classical
  let blockers := tagHistory.reservationLedger.filter fun candidate ↦
    state.core.representative candidate.rawAge <
        state.core.representative guard.head.rawAge ∧
      ∃ path : certificate.referenceSwitchingGraph.EdgeSimplePath,
        path.start = guard.tensor.mate ∧
          path.finish = candidate.search.result.left ∧
            guard.tensor.conclusion ∉ path.vertices
  let blockerRepresentatives := blockers.map fun candidate ↦
    state.core.representative candidate.rawAge
  have eventInBlockers : event ∈ blockers := by
    simp [blockers, eventMembership, eventOlder]
    exact ⟨eventAnchor, eventAnchorStarts, eventAnchorFinishes,
      eventAnchorAvoids⟩
  have eventRepresentativeIn :
      state.core.representative event.rawAge ∈ blockerRepresentatives :=
    List.mem_map.mpr ⟨event, eventInBlockers, rfl⟩
  cases maxEquation : blockerRepresentatives.max? with
  | none =>
      have empty : blockerRepresentatives = [] :=
        List.max?_eq_none_iff.mp maxEquation
      rw [empty] at eventRepresentativeIn
      contradiction
  | some maxRepresentative =>
      have maxFacts := List.max?_eq_some_iff.mp maxEquation
      rcases List.mem_map.mp maxFacts.1 with
        ⟨maxEvent, maxInBlockers, maxRepresentativeEquation⟩
      subst maxRepresentative
      have maxData :
          maxEvent ∈ tagHistory.reservationLedger ∧
            state.core.representative maxEvent.rawAge <
              state.core.representative guard.head.rawAge ∧
            ∃ path : certificate.referenceSwitchingGraph.EdgeSimplePath,
              path.start = guard.tensor.mate ∧
                path.finish = maxEvent.search.result.left ∧
                  guard.tensor.conclusion ∉ path.vertices := by
        simpa [blockers] using maxInBlockers
      rcases maxData with
        ⟨maxMembership, maxOlder, maxPath, maxPathStarts,
          maxPathFinishes, maxPathAvoids⟩
      have maximal : ∀ candidate : ReservationEvent certificate,
          candidate ∈ tagHistory.reservationLedger →
          state.core.representative candidate.rawAge <
              state.core.representative guard.head.rawAge →
          (∃ path : certificate.referenceSwitchingGraph.EdgeSimplePath,
            path.start = guard.tensor.mate ∧
              path.finish = candidate.search.result.left ∧
                guard.tensor.conclusion ∉ path.vertices) →
          state.core.representative candidate.rawAge ≤
            state.core.representative maxEvent.rawAge := by
        intro candidate candidateMembership candidateOlder candidateAnchor
        have candidateInBlockers : candidate ∈ blockers := by
          simp [blockers, candidateMembership, candidateOlder,
            candidateAnchor]
        have candidateRepresentativeIn :
            state.core.representative candidate.rawAge ∈
              blockerRepresentatives :=
          List.mem_map.mpr ⟨candidate, candidateInBlockers, rfl⟩
        exact maxFacts.2 _ candidateRepresentativeIn
      rcases tagHistory.maximal_anchor_bridge correct invariant guard
          maxMembership maxOlder maxPath maxPathStarts maxPathFinishes
          maxPathAvoids maximal with
        ⟨position, parent, parentEvent, prefixPath, parentAt, childAt,
          parentLookup, prefixStarts, prefixFinishes, prefixAvoids⟩
      exact
        tagHistory.storedLeft_callbackTrace_conflicts_with_mateToParentPath
          correct invariant guard parentAt childAt parentLookup prefixPath
          prefixStarts prefixFinishes prefixAvoids childMembership childAge
          sideLeft callbackTrace

/-- No authentic ledger event strictly below the active representative can
carry an exact reference path from the active mate to its stored-left axiom
endpoint while avoiding the active tensor conclusion.

This is the reusable blocker-elimination interface. It does not require the
anchor to arise from an event touch, and it does not claim that a callback
failure is impossible without such an anchor. -/
theorem no_strictOlder_activeMateEventAnchor
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate state)
    (guard : NewGuard certificate state)
    {event : ReservationEvent certificate}
    (eventMembership : event ∈ tagHistory.reservationLedger)
    (eventOlder :
      state.core.representative event.rawAge <
        state.core.representative guard.head.rawAge) :
    ¬ ActiveMateEventAnchor guard event := by
  rintro ⟨eventAnchor, eventAnchorStarts, eventAnchorFinishes,
    eventAnchorAvoids⟩
  rcases tagHistory.strictOlder_commitmentPath_or_equalCallbackFailure
      correct invariant guard eventMembership eventOlder with
    commitment | callback
  · rcases commitment with
      ⟨parentEvent, childEvent, commitmentPath, parentLookup, childLookup,
        commitmentStarts, commitmentFinishes, commitmentAvoids⟩
    rcases tagHistory.eventLeft_to_representativeEvent_referencePath_avoiding
        correct invariant guard eventMembership parentLookup with
      ⟨componentPath, componentStarts, componentFinishes, componentAvoids⟩
    rcases eventAnchor.connectEraseAvoiding componentPath
        (eventAnchorFinishes.trans componentStarts.symm)
        eventAnchorAvoids componentAvoids with
      ⟨prefixPath, prefixStarts, prefixFinishes, prefixAvoids⟩
    let rebuilt : tagHistory.CommitmentEdgeTargetAvoidingPath
        (state.core.representative event.rawAge) guard.head.rawAge
          guard.tensor.conclusion :=
      ⟨parentEvent, childEvent, commitmentPath, parentLookup, childLookup,
        commitmentStarts, commitmentFinishes, commitmentAvoids⟩
    exact tagHistory.commitmentPath_conflicts_with_mateToParentPath
      correct invariant guard parentLookup prefixPath
        (prefixStarts.trans eventAnchorStarts)
        (prefixFinishes.trans componentFinishes) prefixAvoids rebuilt
  · rcases callback with
      ⟨childEvent, beforeTrace, afterTrace, childMembership, childAge,
        sideLeft, callbackTrace⟩
    exact tagHistory.strictOlder_anchor_not_equalCallbackFailure
      correct invariant guard eventMembership eventOlder eventAnchor
      eventAnchorStarts eventAnchorFinishes eventAnchorAvoids childMembership
      childAge sideLeft callbackTrace

/-- Every authentic ledger event is touch-separated from the complete
source-left region of the active `NewGuard`, without assuming the global
`OlderEventTouchSeparated` predicate.

The theorem is local to the supplied active guard. It does not by itself
establish global historical separation, raw-mark readiness, `NewEnabled`, or
scheduler progress. -/
theorem event_touchSeparatedFrom_active_sourceLeftRegion
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate state)
    (guard : NewGuard certificate state)
    {event : ReservationEvent certificate}
    (eventMembership : event ∈ tagHistory.reservationLedger) :
    event.TouchSeparatedFrom guard.tensor.mate := by
  intro vertex touched region
  have eventOlder :=
    tagHistory.event_touch_active_region_implies_representative_lt
      correct invariant guard eventMembership touched region
  have eventAnchor :=
    activeTouch_activeMateEventAnchor correct guard touched region
  exact tagHistory.no_strictOlder_activeMateEventAnchor
    correct invariant guard eventMembership eventOlder eventAnchor

end CanonicalTagHistory

end SequentialFigure7
end ProofNetIR
