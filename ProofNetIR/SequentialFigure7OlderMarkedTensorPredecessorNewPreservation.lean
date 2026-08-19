/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7OlderMarkedTensorPredecessorInvariant
import ProofNetIR.SequentialFigure7ActiveRegionEnabledness
import ProofNetIR.SequentialFigure7CrossRepresentativeNewPreservation

/-!
# New preservation of the older marked-tensor predecessor invariant

The old-work case transports indexed adjacency through the fresh sigma append.
For a newly enqueued endpoint, canonical reservation history and the existing
active-anchor exclusion force every already marked tensor mate into the old
active boundary, which is immediately before the appended fresh boundary.

Only the direct `new` branch theorem is public. The reference-path and
marked-mate boundary arguments are implementation details. This module makes
no claim about `wait`, `forward`, `unifyPayload`, full history
preservation, progress, or completeness.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialUnification
open SequentialSchedulerBridge
open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState

private theorem localTensorReferencePath
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
        leftEdge, rightEdge, Graph.DirectedEdge.target,
        wellFormed.2.1]
      exact ⟨wellFormed.1, fun same ↦ wellFormed.2.2.1 same.symm⟩ }
  refine ⟨path, rfl, rfl, ?_⟩
  simp [path, Graph.EdgeSimplePath.vertices,
    Graph.EdgeWalk.visitedVertices, leftDirected, rightDirected,
    leftEdge, rightEdge, Graph.DirectedEdge.target]

private theorem connectiveTensorReferencePath
    {certificate : Certificate} {vertex : Vertex}
    (consumer : ConnectiveBelow certificate vertex)
    (tensorKind : consumer.kind = .tensor)
    (structural : certificate.StructurallyWellFormed) :
    ∃ path : certificate.referenceSwitchingGraph.EdgeSimplePath,
      path.start = vertex ∧ path.finish = consumer.mate ∧
        path.vertices = [vertex, consumer.conclusion, consumer.mate] := by
  have linkLookup :
      certificate.links[consumer.linkIndex]? =
        some (.tensor consumer.storedLeft consumer.storedRight
          consumer.conclusion) := by
    simpa [tensorKind, SequentialConnectiveKind.asLink] using consumer.link_eq
  have membership :
      Link.tensor consumer.storedLeft consumer.storedRight
          consumer.conclusion ∈ certificate.links :=
    List.mem_of_getElem? linkLookup
  rcases localTensorReferencePath structural membership with
    ⟨path, pathStarts, pathFinishes, pathVertices⟩
  cases sideEquation : consumer.side with
  | storedLeft =>
      have vertexLeft : vertex = consumer.storedLeft := by
        simpa [TensorPremiseSide.premise, sideEquation] using
          consumer.premise_eq
      refine ⟨path, pathStarts.trans vertexLeft.symm, ?_, ?_⟩
      · simpa [ConnectiveBelow.mate, TensorPremiseSide.mate,
          sideEquation] using pathFinishes
      · simpa [TensorPremiseSide.premise, ConnectiveBelow.mate,
          TensorPremiseSide.mate, sideEquation, consumer.premise_eq] using
          pathVertices
  | storedRight =>
      have vertexRight : vertex = consumer.storedRight := by
        simpa [TensorPremiseSide.premise, sideEquation] using
          consumer.premise_eq
      refine ⟨path.reverse, ?_, ?_, ?_⟩
      · exact pathFinishes.trans vertexRight.symm
      · simpa [Graph.EdgeSimplePath.reverse, ConnectiveBelow.mate,
          TensorPremiseSide.mate, sideEquation] using pathStarts
      · rw [Graph.EdgeSimplePath.reverse_vertices, pathVertices]
        simp [TensorPremiseSide.premise, ConnectiveBelow.mate,
          TensorPremiseSide.mate, sideEquation, consumer.premise_eq]

private theorem NewStep.created_connectiveConclusion_ne_current_of_oldMarkedMate
    {certificate : Certificate} {before after : ReservationState}
    (step : NewStep certificate before after)
    (structural : certificate.StructurallyWellFormed)
    {head : Vertex}
    (endpoint : head = step.reached ∨ head = step.partner)
    (consumer : ConnectiveBelow certificate head)
    (tensorKind : consumer.kind = .tensor)
    {mateRawAge : RawTokenAge}
    (mateMarked :
      before.core.marks[consumer.mate]? = some (some mateRawAge)) :
    consumer.conclusion ≠ step.tensor.conclusion := by
  intro sameConclusion
  have currentMembership :
      Link.tensor step.tensor.storedLeft step.tensor.storedRight
          step.tensor.conclusion ∈ certificate.links :=
    List.mem_of_getElem? step.tensorValid.2.1
  have consumerLookup :
      certificate.links[consumer.linkIndex]? =
        some (.tensor consumer.storedLeft consumer.storedRight
          consumer.conclusion) := by
    simpa [tensorKind, SequentialConnectiveKind.asLink] using consumer.link_eq
  have consumerMembership :
      Link.tensor consumer.storedLeft consumer.storedRight
          consumer.conclusion ∈ certificate.links :=
    List.mem_of_getElem? consumerLookup
  have sameLink :=
    UnificationState.StructurallyWellFormed.producerLink_unique
      (conclusion := step.tensor.conclusion) structural
      currentMembership (by simp [Link.produces])
      consumerMembership (by simp [Link.produces, sameConclusion])
  injection sameLink with leftEq rightEq _conclusionEq
  have selectedMarked :
      step.coreMarked.marks[step.stackResult.vertex]? =
        some (some step.stackResult.rawAge) :=
    (UnificationState.markReadyRaw?_exact step.core_mark_eq).2.2.2.2.2.2
  have selectedUnmarked :
      before.core.marks[step.stackResult.vertex]? = some none :=
    (UnificationState.markReadyRaw?_exact step.core_mark_eq).1
  have endpointUnmarked :
      step.coreMarked.marks[head]? = some none := by
    have reachedUnmarked :
        step.coreMarked.marks[step.reached]? = some none := by
      rcases step.route.storedEndpoints with
        ⟨reachedEq, _partnerEq⟩ | ⟨reachedEq, _partnerEq⟩
      · simpa [reachedEq] using step.search.leftReady
      · simpa [reachedEq] using step.search.rightReady
    have partnerUnmarked :
        step.coreMarked.marks[step.partner]? = some none := by
      rcases step.route.storedEndpoints with
        ⟨_reachedEq, partnerEq⟩ | ⟨_reachedEq, partnerEq⟩
      · simpa [partnerEq] using step.search.rightReady
      · simpa [partnerEq] using step.search.leftReady
    rcases endpoint with reached | partner
    · simpa [reached] using reachedUnmarked
    · simpa [partner] using partnerUnmarked
  have currentPremise := step.tensorValid.2.2.2
  have consumerPremise := consumer.premise_eq
  cases currentSide : step.tensor.side <;>
      cases consumerSide : consumer.side
  · have headEq : head = step.stackResult.vertex := by
      simp [TensorBelow.premise, TensorPremiseSide.premise,
        currentSide] at currentPremise
      simp [TensorPremiseSide.premise, consumerSide] at consumerPremise
      exact consumerPremise.trans (leftEq.symm.trans currentPremise.symm)
    rw [headEq, selectedMarked] at endpointUnmarked
    simp at endpointUnmarked
  · have mateEq : consumer.mate = step.stackResult.vertex := by
      simp [ConnectiveBelow.mate, TensorPremiseSide.mate, consumerSide]
      simp [TensorBelow.premise, TensorPremiseSide.premise,
        currentSide] at currentPremise
      exact leftEq.symm.trans currentPremise.symm
    rw [mateEq, selectedUnmarked] at mateMarked
    simp at mateMarked
  · have mateEq : consumer.mate = step.stackResult.vertex := by
      simp [ConnectiveBelow.mate, TensorPremiseSide.mate, consumerSide]
      simp [TensorBelow.premise, TensorPremiseSide.premise,
        currentSide] at currentPremise
      exact rightEq.symm.trans currentPremise.symm
    rw [mateEq, selectedUnmarked] at mateMarked
    simp at mateMarked
  · have headEq : head = step.stackResult.vertex := by
      simp [TensorBelow.premise, TensorPremiseSide.premise,
        currentSide] at currentPremise
      simp [TensorPremiseSide.premise, consumerSide] at consumerPremise
      exact consumerPremise.trans (rightEq.symm.trans currentPremise.symm)
    rw [headEq, selectedMarked] at endpointUnmarked
    simp at endpointUnmarked

private theorem CanonicalTagHistory.newEndpoint_oldMarkedTensor_sigmaBoundary_eq_active
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate before)
    (step : NewStep certificate before after)
    {head : Vertex}
    (endpoint : head = step.reached ∨ head = step.partner)
    (consumer : ConnectiveBelow certificate head)
    (tensorKind : consumer.kind = .tensor)
    {mateRawAge : RawTokenAge}
    (mateMarked :
      before.core.marks[consumer.mate]? = some (some mateRawAge)) :
    sigmaBoundary? before.stack.sigma mateRawAge =
      some step.stackResult.rawAge := by
  have representativeLe :=
    step.guard.marked_representative_le_active invariant mateMarked
  have representativeEq :
      before.core.representative mateRawAge =
        before.core.representative step.guard.head.rawAge := by
    apply Classical.byContradiction
    intro representativeNe
    have representativeLt :
        before.core.representative mateRawAge <
          before.core.representative step.guard.head.rawAge :=
      Nat.lt_of_le_of_ne representativeLe representativeNe
    rcases tagHistory.rawMarked_reservationEvent_referenceAnchors
        invariant mateMarked with
      ⟨event, component, _eventUsed, _forestUsed, owned,
        leftPath, _rightPath, eventLookup, eventAge,
        componentLookup, _eventDerivation, _eventLink, _eventWitness,
        eventAccounted, mateOwned, _eventLeftOwned, _eventRightOwned,
        leftStarts, leftFinishes, leftWithin,
        _rightStarts, _rightFinishes, _rightWithin⟩
    have eventMembership : event ∈ tagHistory.reservationLedger :=
      List.mem_of_getElem? eventLookup
    have eventOlder :
        before.core.representative event.rawAge <
          before.core.representative step.guard.head.rawAge := by
      simpa [eventAge] using representativeLt
    have endpointRegion :
        SourceLeftRegionVertex certificate step.tensor.mate head := by
      rcases endpoint with reached | partner
      · simpa [reached] using
          (SourceLeftRegionVertex.visited step.route.reachable)
      · simpa [partner] using
          (SourceLeftRegionVertex.terminalPartner step.route.reachable
            step.route.exactAxiom)
    have endpointRegionGuard :
        SourceLeftRegionVertex certificate step.guard.tensor.mate head := by
      simpa [NewStep.guard] using endpointRegion
    have mateBelowConclusion :
        certificate.formulaComplexityAt step.guard.tensor.mate <
          certificate.formulaComplexityAt step.guard.tensor.conclusion :=
      step.guard.sourceLeftRegion_formulaComplexity_lt_conclusion
        correct.1 (.visited (.refl _))
    have headBelowConclusion :
        certificate.formulaComplexityAt head <
          certificate.formulaComplexityAt step.guard.tensor.conclusion :=
      step.guard.sourceLeftRegion_formulaComplexity_lt_conclusion
        correct.1 endpointRegionGuard
    have headNeConclusion :
        head ≠ step.guard.tensor.conclusion := by
      intro same
      exact (Nat.ne_of_lt headBelowConclusion)
        (congrArg certificate.formulaComplexityAt same)
    rcases sourceLeftRegionVertex_referencePath_avoiding correct.1
        endpointRegionGuard mateBelowConclusion headNeConclusion with
      ⟨routePath, routeStarts, routeFinishes, routeAvoids⟩
    rcases connectiveTensorReferencePath consumer tensorKind correct.1 with
      ⟨tensorPath, tensorStarts, tensorFinishes, tensorVertices⟩
    have consumerConclusionNe :
        consumer.conclusion ≠ step.guard.tensor.conclusion := by
      simpa [NewStep.guard] using
        step.created_connectiveConclusion_ne_current_of_oldMarkedMate
          correct.1 endpoint consumer tensorKind mateMarked
    have conclusionNotOwned :
        step.guard.tensor.conclusion ∉ owned :=
      step.guard.tensorConclusion_not_owned invariant componentLookup
        eventAccounted
    have mateNeConclusion :
        consumer.mate ≠ step.guard.tensor.conclusion := by
      intro same
      exact conclusionNotOwned (by simpa [same] using mateOwned)
    have tensorAvoids :
        step.guard.tensor.conclusion ∉ tensorPath.vertices := by
      rw [tensorVertices]
      simp [Ne.symm headNeConclusion, Ne.symm consumerConclusionNe,
        Ne.symm mateNeConclusion]
    have leftAvoids :
        step.guard.tensor.conclusion ∉ leftPath.vertices := by
      intro inPath
      exact conclusionNotOwned
        (leftWithin step.guard.tensor.conclusion inPath)
    rcases Graph.EdgeSimplePath.connectEraseAvoiding routePath tensorPath
        (routeFinishes.trans tensorStarts.symm) routeAvoids tensorAvoids with
      ⟨prefixPath, prefixStarts, prefixFinishes, prefixAvoids⟩
    have prefixMeetsLeft : prefixPath.finish = leftPath.start :=
      prefixFinishes.trans (tensorFinishes.trans leftStarts.symm)
    rcases Graph.EdgeSimplePath.connectEraseAvoiding prefixPath leftPath
        prefixMeetsLeft prefixAvoids leftAvoids with
      ⟨anchorPath, anchorStarts, anchorFinishes, anchorAvoids⟩
    have anchor : ActiveMateEventAnchor step.guard event := by
      refine ⟨anchorPath, ?_, ?_, anchorAvoids⟩
      · exact anchorStarts.trans (prefixStarts.trans routeStarts)
      · exact anchorFinishes.trans leftFinishes
    exact tagHistory.no_strictOlder_activeMateEventAnchor
      correct invariant step.guard eventMembership eventOlder anchor
  have mateAgeBound : mateRawAge < before.stack.nextAge := by
    have stackMarked :
        before.stack.marks[consumer.mate]? = some (some mateRawAge) := by
      rw [← invariant.realizesSigma.marks_eq]
      exact mateMarked
    exact invariant.stack_wellShaped.assigned_age_bound
      consumer.mate mateRawAge stackMarked
  have realized :=
    invariant.realizesSigma.representative_eq_boundary mateAgeBound
  have activeRoot :
      before.core.representative step.guard.head.rawAge =
        step.guard.head.rawAge :=
    (step.guard.head.futureWorkAt invariant).representative_eq_rawAge invariant
  have boundaryAtActive :
      sigmaBoundary? before.stack.sigma mateRawAge =
        some step.guard.head.rawAge := by
    rw [realized, representativeEq, activeRoot]
  simpa [NewStep.guard, NewStep.readyHeadInput] using boundaryAtActive

/-- Every marked tensor mate of a fresh New endpoint lies in the active
sigma boundary in the marked middle state. -/
private theorem CanonicalTagHistory.newCreatedMarkedTensorMateAtActive
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate before)
    (step : NewStep certificate before after) :
    ∀ {head : Vertex},
      head = step.reached ∨ head = step.partner →
        ∀ (consumer : ConnectiveBelow certificate head),
          consumer.kind = .tensor →
            ∀ {mateRawAge : RawTokenAge},
              after.core.marks[consumer.mate]? =
                  some (some mateRawAge) →
                sigmaBoundary? step.markedMiddle.stack.sigma mateRawAge =
                  some step.stackResult.rawAge := by
  intro head endpoint consumer tensorKind mateRawAge mateMarkedAfter
  have mateMarkedMiddle :
      step.markedMiddle.core.marks[consumer.mate]? =
        some (some mateRawAge) := by
    rw [← step.after_marks_eq_markedMiddle]
    exact mateMarkedAfter
  by_cases selected : consumer.mate = step.stackResult.vertex
  · have selectedMarked :
        step.coreMarked.marks[step.stackResult.vertex]? =
          some (some step.stackResult.rawAge) :=
      (UnificationState.markReadyRaw?_exact step.core_mark_eq).2.2.2.2.2.2
    have mateAgeEq : mateRawAge = step.stackResult.rawAge := by
      have sameMark :
          some (some mateRawAge) =
            some (some step.stackResult.rawAge) := by
        calc
          some (some mateRawAge) =
              step.markedMiddle.core.marks[consumer.mate]? :=
            mateMarkedMiddle.symm
          _ = step.coreMarked.marks[step.stackResult.vertex]? := by
            simp [NewStep.markedMiddle, selected]
          _ = some (some step.stackResult.rawAge) := selectedMarked
      exact Option.some.inj (Option.some.inj sameMark)
    subst mateRawAge
    have sigmaTopBefore :
        before.stack.sigma.getLast? = some step.stackResult.rawAge :=
      (SequentialStackState.popReadyMark?_exact step.stack_eq).2.1
    have sigmaEq :
        step.stackResult.after.sigma = before.stack.sigma :=
      (SequentialStackState.popReadyMark?_exact step.stack_eq).2.2.2.2.2.1
    have sigmaTopMiddle :
        step.markedMiddle.stack.sigma.getLast? =
          some step.stackResult.rawAge := by
      simpa [NewStep.markedMiddle, sigmaEq] using sigmaTopBefore
    exact step.markedMiddle_reservationInvariant.stack_wellShaped
      |>.sigma_partition.sigmaBoundary?_eq_top sigmaTopMiddle
  · have beforeMarked :
        before.core.marks[consumer.mate]? =
          some (some mateRawAge) := by
      have marksEq :
          step.coreMarked.marks =
            before.core.marks.setIfInBounds
              step.stackResult.vertex (some step.stackResult.rawAge) :=
        (UnificationState.markReadyRaw?_exact step.core_mark_eq).2.1
      change step.coreMarked.marks[consumer.mate]? =
        some (some mateRawAge) at mateMarkedMiddle
      rw [marksEq,
        Array.getElem?_setIfInBounds_ne (Ne.symm selected)] at mateMarkedMiddle
      exact mateMarkedMiddle
    have lookupBefore :=
      tagHistory.newEndpoint_oldMarkedTensor_sigmaBoundary_eq_active
        correct invariant step endpoint consumer tensorKind beforeMarked
    have sigmaEq :
        step.stackResult.after.sigma = before.stack.sigma :=
      (SequentialStackState.popReadyMark?_exact step.stack_eq).2.2.2.2.2.1
    simpa [NewStep.markedMiddle, sigmaEq] using lookupBefore

private theorem CanonicalTagHistory.new_olderMarkedTensorPredecessorInvariant_of_middle
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate before)
    (step : NewStep certificate before after)
    (middle :
      OlderMarkedTensorPredecessorInvariant certificate
        step.markedMiddle) :
    OlderMarkedTensorPredecessorInvariant certificate after := by
  intro candidateRawAge candidateVertex work consumer tensorKind
    mateRawAge mateMarkedAfter representativeLt
  have afterStack : after.stack = step.stackAfter :=
    congrArg (fun state : ReservationState ↦ state.stack) step.output_eq
  rcases SequentialStackState.operationalNewEnqueue?_exact
      step.stack_enqueue_eq with
    ⟨_active, _activeEquation, _activeLt, _marks, _nextAge,
      sigmaEquation, _ready, _waiting, _activeWaiting, _freshWaiting⟩
  have afterSigma :
      after.stack.sigma =
        step.markedMiddle.stack.sigma ++
          [step.markedMiddle.stack.nextAge] := by
    rw [afterStack, sigmaEquation]
    rfl
  have mateMarkedMiddle :
      step.markedMiddle.core.marks[consumer.mate]? =
        some (some mateRawAge) := by
    rw [← step.after_marks_eq_markedMiddle]
    exact mateMarkedAfter
  have stackMateMarked :
      step.markedMiddle.stack.marks[consumer.mate]? =
        some (some mateRawAge) := by
    rw [← step.markedMiddle_reservationInvariant.realizesSigma.marks_eq]
    exact mateMarkedMiddle
  have mateAgeBound :
      mateRawAge < step.markedMiddle.stack.nextAge :=
    step.markedMiddle_reservationInvariant.stack_wellShaped
      |>.assigned_age_bound consumer.mate mateRawAge stackMateMarked
  rcases work.beforeNewOrInserted step with oldWork | inserted
  · have middleRepresentativeLt :
        step.markedMiddle.core.representative mateRawAge <
          step.markedMiddle.core.representative candidateRawAge := by
      rw [← step.after_representative_eq_markedMiddle mateRawAge]
      rw [← step.after_representative_eq_markedMiddle candidateRawAge]
      exact representativeLt
    rcases middle oldWork consumer tensorKind mateMarkedMiddle
        middleRepresentativeLt with
      ⟨previousBoundary, ⟨predecessor⟩⟩
    refine ⟨previousBoundary, ⟨{
      position := predecessor.position
      previous_at := ?_
      candidate_at := ?_
      mate_boundary := ?_ }⟩⟩
    · rw [afterSigma]
      have positionBound :
          predecessor.position <
            step.markedMiddle.stack.sigma.length :=
        (List.getElem?_eq_some_iff.mp predecessor.previous_at).choose
      rw [List.getElem?_append_left positionBound]
      exact predecessor.previous_at
    · rw [afterSigma]
      have positionBound :
          predecessor.position + 1 <
            step.markedMiddle.stack.sigma.length :=
        (List.getElem?_eq_some_iff.mp predecessor.candidate_at).choose
      rw [List.getElem?_append_left positionBound]
      exact predecessor.candidate_at
    · rw [afterSigma, sigmaBoundary?_append_fresh_old mateAgeBound]
      exact predecessor.mate_boundary
  · rcases inserted with ⟨candidateAge, endpoint⟩
    have mateAtActive :
        sigmaBoundary? step.markedMiddle.stack.sigma mateRawAge =
          some step.stackResult.rawAge :=
      tagHistory.newCreatedMarkedTensorMateAtActive
        correct invariant step endpoint consumer tensorKind mateMarkedAfter
    have sigmaTopBefore :
        before.stack.sigma.getLast? = some step.stackResult.rawAge :=
      (SequentialStackState.popReadyMark?_exact step.stack_eq).2.1
    have middleSigmaEq :
        step.markedMiddle.stack.sigma = before.stack.sigma := by
      change step.stackResult.after.sigma = before.stack.sigma
      exact
        (SequentialStackState.popReadyMark?_exact step.stack_eq)
          |>.2.2.2.2.2.1
    have sigmaTopMiddle :
        step.markedMiddle.stack.sigma.getLast? =
          some step.stackResult.rawAge := by
      rw [middleSigmaEq]
      exact sigmaTopBefore
    rcases List.getLast?_eq_some_iff.mp sigmaTopMiddle with
      ⟨sigmaPrefix, sigmaDecomposition⟩
    refine ⟨step.stackResult.rawAge, ⟨{
      position := sigmaPrefix.length
      previous_at := ?_
      candidate_at := ?_
      mate_boundary := ?_ }⟩⟩
    · rw [afterSigma, sigmaDecomposition]
      simp
    · rw [afterSigma, sigmaDecomposition, candidateAge,
        step.markedMiddle_nextAge_eq_event_rawAge]
      simp
    · rw [afterSigma, sigmaBoundary?_append_fresh_old mateAgeBound]
      exact mateAtActive

/-- A canonical successful `new` branch preserves the all-future-work
predecessor invariant directly from the input state. -/
theorem CanonicalTagHistory.new_olderMarkedTensorPredecessorInvariant
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate before)
    (step : NewStep certificate before after)
    (prior :
      OlderMarkedTensorPredecessorInvariant certificate before) :
    OlderMarkedTensorPredecessorInvariant certificate after := by
  refine @CanonicalTagHistory.new_olderMarkedTensorPredecessorInvariant_of_middle
    certificate before after history tagHistory correct invariant step ?_
  unfold OlderMarkedTensorPredecessorInvariant
  intro candidateRawAge candidateVertex work consumer tensorKind
    mateRawAge mateMarked representativeLt
  exact
    (PreparedStep.olderMarkedTensorPredecessorInvariant
      (certificate := certificate) step.preparedPrefix invariant prior)
        work consumer tensorKind mateMarked representativeLt

end SequentialFigure7
end ProofNetIR
