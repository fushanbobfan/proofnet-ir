/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7CrossRepresentativeNewPreservation
import ProofNetIR.SequentialFigure7OlderRawMarkedRegionSeparation

namespace ProofNetIR

/-!
# Figure-7 new preservation of older raw-marked region separation

A successful `new` transports every old future candidate from its marked
middle state and creates candidates only at the reached/partner endpoints.
For a created candidate, the selected raw mark is outside its source-left
region by reference-switching acyclicity.  The only genuinely new assumption
is therefore separation of raw marks retained from the input state from the
created candidate regions.

This module does not derive that retained-mark side condition from scheduler
reachability, tag history, or declarative correctness.  It proves neither
later-rule preservation nor progress, totality, completeness, fallback
removal, token-age scheduling, or whole-program linearity.
-/

namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge
open SequentialUnification

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
        leftEdge, rightEdge, Graph.DirectedEdge.target,
        wellFormed.2.1]
      exact
        ⟨wellFormed.1,
          fun same => wellFormed.2.2.1 same.symm⟩ }
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

private theorem TensorBelow.mate_complexity_lt_conclusion
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

private theorem SourceLeftRegionVertex.formulaComplexity_le_start
    {certificate : Certificate} {start vertex : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (region : SourceLeftRegionVertex certificate start vertex) :
    certificate.formulaComplexityAt vertex ≤
      certificate.formulaComplexityAt start := by
  cases region with
  | visited reachable =>
      exact reachable.formulaComplexity_le structural
  | terminalPartner _reachable exactAxiom =>
      have endpointFormula :
          ∃ name positive,
            certificate.formula? vertex = some (.atom name positive) := by
        rcases exactAxiom with exactAxiom | exactAxiom
        · have axiomWellFormed :=
            structural.2.2.2.2.1 _ (List.mem_of_getElem? exactAxiom)
          exact axiomWellFormed.axiom_endpointFormula (Or.inr rfl)
        · have axiomWellFormed :=
            structural.2.2.2.2.1 _ (List.mem_of_getElem? exactAxiom)
          exact axiomWellFormed.axiom_endpointFormula (Or.inl rfl)
      rcases endpointFormula with ⟨name, positive, partnerFormula⟩
      have partnerComplexity :
          certificate.formulaComplexityAt vertex = 0 := by
        simp [Certificate.formulaComplexityAt, partnerFormula,
          Formula.complexity]
      rw [partnerComplexity]
      omega

private theorem TensorBelow.noBypass
    {certificate : Certificate} {vertex : Vertex} {tensor : TensorBelow}
    (structural : certificate.StructurallyWellFormed)
    (acyclic : certificate.referenceSwitchingGraph.Acyclic)
    (valid : tensor.Valid certificate certificate.consumerIndex vertex)
    (path : certificate.referenceSwitchingGraph.EdgeSimplePath)
    (pathStarts : path.start = vertex)
    (pathFinishes : path.finish = tensor.mate)
    (conclusionNotInPath : tensor.conclusion ∉ path.vertices) : False := by
  have membership :
      Link.tensor tensor.storedLeft tensor.storedRight tensor.conclusion ∈
        certificate.links :=
    List.mem_of_getElem? valid.2.1
  have premise := valid.2.2.2
  cases sideEquation : tensor.side with
  | storedLeft =>
      have vertexLeft : vertex = tensor.storedLeft := by
        simpa [TensorBelow.premise, TensorPremiseSide.premise,
          sideEquation] using premise
      apply referenceAcyclic_no_tensorBypass structural acyclic membership path
      · exact pathStarts.trans vertexLeft
      · simpa [TensorBelow.mate, TensorPremiseSide.mate,
          sideEquation] using pathFinishes
      · exact conclusionNotInPath
  | storedRight =>
      have vertexRight : vertex = tensor.storedRight := by
        simpa [TensorBelow.premise, TensorPremiseSide.premise,
          sideEquation] using premise
      apply referenceAcyclic_no_tensorBypass structural acyclic membership
        path.reverse
      · change path.finish = tensor.storedLeft
        simpa [TensorBelow.mate, TensorPremiseSide.mate,
          sideEquation] using pathFinishes
      · change path.start = tensor.storedRight
        exact pathStarts.trans vertexRight
      · simpa using conclusionNotInPath

private theorem NewStep.created_tensor_conclusion_ne
    {certificate : Certificate} {before after : ReservationState}
    (structural : certificate.StructurallyWellFormed)
    (step : NewStep certificate before after)
    (created : NewCreatedCandidate certificate step) :
    created.tensor.conclusion ≠ step.tensor.conclusion := by
  intro sameConclusion
  have currentMembership :
      Link.tensor step.tensor.storedLeft step.tensor.storedRight
          step.tensor.conclusion ∈ certificate.links :=
    List.mem_of_getElem? step.tensorValid.2.1
  have createdMembership :
      Link.tensor created.tensor.storedLeft created.tensor.storedRight
          created.tensor.conclusion ∈ certificate.links :=
    List.mem_of_getElem? created.tensor_valid.2.1
  have sameLink :=
    UnificationState.StructurallyWellFormed.producerLink_unique
      (conclusion := step.tensor.conclusion) structural
      currentMembership (by simp [Link.produces])
      createdMembership (by simp [Link.produces, sameConclusion])
  injection sameLink with leftEq rightEq _conclusionEq
  have selectedMarked :
      step.coreMarked.marks[step.stackResult.vertex]? =
        some (some step.stackResult.rawAge) :=
    (UnificationState.markReadyRaw?_exact step.core_mark_eq).2.2.2.2.2.2
  have createdHeadUnmarked :
      step.coreMarked.marks[created.head]? = some none := by
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
    rcases created.endpoint with reached | partner
    · simpa [reached] using reachedUnmarked
    · simpa [partner] using partnerUnmarked
  have currentPremise := step.tensorValid.2.2.2
  have createdPremise := created.tensor_valid.2.2.2
  cases currentSide : step.tensor.side <;>
      cases createdSide : created.tensor.side
  · have headEq : created.head = step.stackResult.vertex := by
      simp [TensorBelow.premise, TensorPremiseSide.premise,
        currentSide] at currentPremise
      simp [TensorBelow.premise, TensorPremiseSide.premise,
        createdSide] at createdPremise
      exact createdPremise.trans (leftEq.symm.trans currentPremise.symm)
    rw [headEq, selectedMarked] at createdHeadUnmarked
    simp at createdHeadUnmarked
  · have mateEq : created.tensor.mate = step.stackResult.vertex := by
      simp [TensorBelow.mate, TensorPremiseSide.mate, createdSide]
      simp [TensorBelow.premise, TensorPremiseSide.premise,
        currentSide] at currentPremise
      exact leftEq.symm.trans currentPremise.symm
    have candidateMateUnmarked := created.mate_unmarked
    change
      step.coreMarked.marks[created.tensor.mate]? = some none
        at candidateMateUnmarked
    rw [mateEq, selectedMarked] at candidateMateUnmarked
    simp at candidateMateUnmarked
  · have mateEq : created.tensor.mate = step.stackResult.vertex := by
      simp [TensorBelow.mate, TensorPremiseSide.mate, createdSide]
      simp [TensorBelow.premise, TensorPremiseSide.premise,
        currentSide] at currentPremise
      exact rightEq.symm.trans currentPremise.symm
    have candidateMateUnmarked := created.mate_unmarked
    change
      step.coreMarked.marks[created.tensor.mate]? = some none
        at candidateMateUnmarked
    rw [mateEq, selectedMarked] at candidateMateUnmarked
    simp at candidateMateUnmarked
  · have headEq : created.head = step.stackResult.vertex := by
      simp [TensorBelow.premise, TensorPremiseSide.premise,
        currentSide] at currentPremise
      simp [TensorBelow.premise, TensorPremiseSide.premise,
        createdSide] at createdPremise
      exact createdPremise.trans (rightEq.symm.trans currentPremise.symm)
    rw [headEq, selectedMarked] at createdHeadUnmarked
    simp at createdHeadUnmarked

/-- Under structural well-formedness and reference-switching acyclicity, the
selected head of a successful `new` lies outside every source-left region of
a candidate created by that step.

This theorem is independent of scheduler invariants, tag history, and raw-age
ordering. -/
theorem NewStep.created_sourceRegion_not_selected_of_structural_acyclic
    {certificate : Certificate} {before after : ReservationState}
    (structural : certificate.StructurallyWellFormed)
    (acyclic : certificate.referenceSwitchingGraph.Acyclic)
    (step : NewStep certificate before after)
    (created : NewCreatedCandidate certificate step) :
    ¬ SourceLeftRegionVertex certificate created.tensor.mate
      step.stackResult.vertex := by
  intro selectedRegion
  have currentEndpointRegion :
      SourceLeftRegionVertex certificate step.tensor.mate created.head := by
    rcases created.endpoint with reached | partner
    · simpa [reached] using
        (SourceLeftRegionVertex.visited step.route.reachable)
    · simpa [partner] using
        (SourceLeftRegionVertex.terminalPartner step.route.reachable
          step.route.exactAxiom)
  have currentMateBelow :=
    TensorBelow.mate_complexity_lt_conclusion step.tensorValid
  have createdMateBelow :=
    TensorBelow.mate_complexity_lt_conclusion created.tensor_valid
  have createdConclusionNeCurrent :
      created.tensor.conclusion ≠ step.tensor.conclusion :=
    step.created_tensor_conclusion_ne structural created
  have selectedNeCurrentConclusion :
      step.stackResult.vertex ≠ step.tensor.conclusion := by
    intro same
    have premise := step.tensorValid.2.2.2
    have wellFormed := step.tensorValid.2.2.1
    cases sideEquation : step.tensor.side with
    | storedLeft =>
        have selectedLeft :
            step.stackResult.vertex = step.tensor.storedLeft := by
          simpa [TensorBelow.premise, TensorPremiseSide.premise,
            sideEquation] using premise
        exact wellFormed.2.1 (selectedLeft.symm.trans same)
    | storedRight =>
        have selectedRight :
            step.stackResult.vertex = step.tensor.storedRight := by
          simpa [TensorBelow.premise, TensorPremiseSide.premise,
            sideEquation] using premise
        exact wellFormed.2.2.1 (selectedRight.symm.trans same)
  have createdHeadNeCreatedConclusion :
      created.head ≠ created.tensor.conclusion := by
    intro same
    have premise := created.tensor_valid.2.2.2
    have wellFormed := created.tensor_valid.2.2.1
    cases sideEquation : created.tensor.side with
    | storedLeft =>
        have headLeft : created.head = created.tensor.storedLeft := by
          simpa [TensorBelow.premise, TensorPremiseSide.premise,
            sideEquation] using premise
        exact wellFormed.2.1 (headLeft.symm.trans same)
    | storedRight =>
        have headRight : created.head = created.tensor.storedRight := by
          simpa [TensorBelow.premise, TensorPremiseSide.premise,
            sideEquation] using premise
        exact wellFormed.2.2.1 (headRight.symm.trans same)
  by_cases order :
      certificate.formulaComplexityAt created.tensor.mate <
        certificate.formulaComplexityAt step.tensor.conclusion
  · have createdHeadNeCurrentConclusion :
        created.head ≠ step.tensor.conclusion := by
      have rank :
          certificate.formulaComplexityAt created.head <
            certificate.formulaComplexityAt step.tensor.conclusion := by
        simpa [NewStep.guard] using
          step.guard.sourceLeftRegion_formulaComplexity_lt_conclusion
            structural currentEndpointRegion
      intro same
      have sameComplexity := congrArg certificate.formulaComplexityAt same
      omega
    rcases sourceLeftRegionVertex_referencePath_avoiding structural
        currentEndpointRegion currentMateBelow
        createdHeadNeCurrentConclusion with
      ⟨currentPath, currentStarts, currentFinishes, currentAvoids⟩
    rcases TensorBelow.referencePath structural created.tensor_valid with
      ⟨createdTensorPath, createdTensorStarts, createdTensorFinishes,
        createdTensorVertices⟩
    have createdTensorAvoids :
        step.tensor.conclusion ∉ createdTensorPath.vertices := by
      rw [createdTensorVertices]
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      intro membership
      rcases membership with atHead | atCreatedConclusion | atMate
      · exact createdHeadNeCurrentConclusion atHead.symm
      · exact createdConclusionNeCurrent atCreatedConclusion.symm
      · have different :
            step.tensor.conclusion ≠ created.tensor.mate := by
          intro same
          have sameComplexity := congrArg certificate.formulaComplexityAt same
          omega
        exact different atMate
    rcases Graph.EdgeSimplePath.connectEraseAvoiding currentPath
        createdTensorPath (currentFinishes.trans createdTensorStarts.symm)
        currentAvoids createdTensorAvoids with
      ⟨prefixPath, prefixStarts, prefixFinishes, prefixAvoids⟩
    rcases sourceLeftRegionVertex_referencePath_avoiding structural
        selectedRegion order selectedNeCurrentConclusion with
      ⟨selectedPath, selectedStarts, selectedFinishes, selectedAvoids⟩
    rcases Graph.EdgeSimplePath.connectEraseAvoiding prefixPath selectedPath
        (prefixFinishes.trans
          (createdTensorFinishes.trans selectedStarts.symm))
        prefixAvoids selectedAvoids with
      ⟨path, pathStarts, pathFinishes, conclusionNotInPath⟩
    exact TensorBelow.noBypass structural acyclic step.tensorValid path.reverse
      (by
        change path.finish = step.stackResult.vertex
        exact pathFinishes.trans selectedFinishes)
      (by
        change path.start = step.tensor.mate
        exact pathStarts.trans (prefixStarts.trans currentStarts))
      (by simpa using conclusionNotInPath)
  · have currentConclusionLeCreatedMate :
        certificate.formulaComplexityAt step.tensor.conclusion ≤
          certificate.formulaComplexityAt created.tensor.mate :=
      Nat.le_of_not_gt order
    have currentMateBelowCreatedConclusion :
        certificate.formulaComplexityAt step.tensor.mate <
          certificate.formulaComplexityAt created.tensor.conclusion := by
      omega
    have selectedRank :=
      SourceLeftRegionVertex.formulaComplexity_le_start
        structural selectedRegion
    have selectedNeCreatedConclusion :
        step.stackResult.vertex ≠ created.tensor.conclusion := by
      intro same
      have sameComplexity := congrArg certificate.formulaComplexityAt same
      omega
    rcases sourceLeftRegionVertex_referencePath_avoiding structural
        selectedRegion createdMateBelow selectedNeCreatedConclusion with
      ⟨selectedPath, selectedStarts, selectedFinishes, selectedAvoids⟩
    rcases TensorBelow.referencePath structural step.tensorValid with
      ⟨currentTensorPath, currentTensorStarts, currentTensorFinishes,
        currentTensorVertices⟩
    have currentTensorAvoids :
        created.tensor.conclusion ∉ currentTensorPath.vertices := by
      rw [currentTensorVertices]
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      intro membership
      rcases membership with atSelected | atCurrentConclusion | atMate
      · exact selectedNeCreatedConclusion atSelected.symm
      · exact createdConclusionNeCurrent atCurrentConclusion
      · have different :
            created.tensor.conclusion ≠ step.tensor.mate := by
          intro same
          have sameComplexity := congrArg certificate.formulaComplexityAt same
          omega
        exact different atMate
    rcases Graph.EdgeSimplePath.connectEraseAvoiding selectedPath
        currentTensorPath
        (selectedFinishes.trans currentTensorStarts.symm)
        selectedAvoids currentTensorAvoids with
      ⟨prefixPath, prefixStarts, prefixFinishes, prefixAvoids⟩
    rcases sourceLeftRegionVertex_referencePath_avoiding structural
        currentEndpointRegion currentMateBelowCreatedConclusion
        createdHeadNeCreatedConclusion with
      ⟨currentPath, currentStarts, currentFinishes, currentAvoids⟩
    rcases Graph.EdgeSimplePath.connectEraseAvoiding prefixPath currentPath
        (prefixFinishes.trans
          (currentTensorFinishes.trans currentStarts.symm))
        prefixAvoids currentAvoids with
      ⟨path, pathStarts, pathFinishes, conclusionNotInPath⟩
    exact TensorBelow.noBypass structural acyclic created.tensor_valid
      path.reverse
      (by
        change path.finish = created.head
        exact pathFinishes.trans currentFinishes)
      (by
        change path.start = created.tensor.mate
        exact pathStarts.trans (prefixStarts.trans selectedStarts))
      (by simpa using conclusionNotInPath)

/-- Declarative correctness supplies the structural and reference-switching
acyclicity assumptions needed to exclude the selected head from every source
region created by a successful `new`. -/
theorem NewStep.created_sourceRegion_not_selected
    {certificate : Certificate} {before after : ReservationState}
    (correct : certificate.DeclarativelyCorrect)
    (step : NewStep certificate before after)
    (created : NewCreatedCandidate certificate step) :
    ¬ SourceLeftRegionVertex certificate created.tensor.mate
      step.stackResult.vertex :=
  step.created_sourceRegion_not_selected_of_structural_acyclic
    correct.1 correct.referenceSwitchingTree.acyclic created

/-- The new raw-mark geometry required from the caller of `new` preservation:
every raw mark retained from the input state and strictly older than the fresh
raw age lies outside every source-left region created by this step.

The predicate contains no history or reachability witness and no additional
executor result or equation beyond the supplied typed `NewStep`.
-/
def NewRetainedRawMarksSeparated
    {certificate : Certificate} {before after : ReservationState}
    (step : NewStep certificate before after) : Prop :=
  ∀ (created : NewCreatedCandidate certificate step) rawAge vertex,
    before.core.marks[vertex]? = some (some rawAge) →
      step.markedMiddle.core.representative rawAge <
          step.markedMiddle.core.representative
            (ReservationEvent.new step).rawAge →
        ¬ SourceLeftRegionVertex certificate created.tensor.mate vertex

/-- The fresh raw age is exactly the marked-middle horizon, so no future work
in the marked middle state can occur at that age.  Consequently the existing
state invariant cannot be instantiated directly at a created candidate. -/
theorem NewStep.no_middle_futureWork_at_fresh
    {certificate : Certificate} {before after : ReservationState}
    (step : NewStep certificate before after)
    (invariant : SchedulerInvariant certificate before)
    {vertex : Vertex} :
    ¬ FutureWorkAt step.markedMiddle (ReservationEvent.new step).rawAge
      vertex := by
  intro work
  have middleInvariant := step.markedMiddle_schedulerInvariant invariant
  have bound := work.rawAge_lt_nextAge middleInvariant
  rw [step.markedMiddle_nextAge_eq_event_rawAge] at bound
  exact Nat.lt_irrefl _ bound

/-- Every concrete raw mark retained from the input state is strictly older
than the fresh raw age when representatives are measured in the marked middle
state. -/
theorem NewStep.retained_mark_strictly_older_than_fresh
    {certificate : Certificate} {before after : ReservationState}
    (step : NewStep certificate before after)
    (invariant : SchedulerInvariant certificate before)
    {rawAge : RawTokenAge} {vertex : Vertex}
    (marked : before.core.marks[vertex]? = some (some rawAge)) :
    step.markedMiddle.core.representative rawAge <
      step.markedMiddle.core.representative
        (ReservationEvent.new step).rawAge := by
  have middleInvariant := step.markedMiddle_schedulerInvariant invariant
  rcases UnificationState.markReadyRaw?_exact step.core_mark_eq with
    ⟨selectedUnmarked, afterMarks, _parents, _components, _started,
      _fired, _selectedMarked⟩
  have selectedNe : step.stackResult.vertex ≠ vertex := by
    intro same
    subst vertex
    rw [selectedUnmarked] at marked
    simp at marked
  have middleMarked :
      step.markedMiddle.core.marks[vertex]? = some (some rawAge) := by
    change step.coreMarked.marks[vertex]? = some (some rawAge)
    rw [afterMarks]
    simpa [Array.getElem?_setIfInBounds, selectedNe] using marked
  have stackMarked :
      step.markedMiddle.stack.marks[vertex]? = some (some rawAge) := by
    rw [← middleInvariant.realizesSigma.marks_eq]
    exact middleMarked
  have rawAgeBound : rawAge < step.markedMiddle.stack.nextAge :=
    middleInvariant.stack_wellShaped.assigned_age_bound vertex rawAge
      stackMarked
  have representativeLe :
      step.markedMiddle.core.representative rawAge ≤ rawAge :=
    UnificationState.OrderedParents.representative_le
      middleInvariant.core_orderedParents rawAge
  have freshRepresentative :
      step.markedMiddle.core.representative
          (ReservationEvent.new step).rawAge =
        (ReservationEvent.new step).rawAge := by
    apply UnificationState.representative_eq_of_size_le
    rw [middleInvariant.realizesSigma.horizon_eq,
      step.markedMiddle_nextAge_eq_event_rawAge]
    exact Nat.le_refl _
  calc
    step.markedMiddle.core.representative rawAge ≤ rawAge :=
      representativeLe
    _ < (ReservationEvent.new step).rawAge := by
      simpa [← step.markedMiddle_nextAge_eq_event_rawAge] using rawAgeBound
    _ = step.markedMiddle.core.representative
        (ReservationEvent.new step).rawAge := freshRepresentative.symm

/-- The retained-mark side condition, together with the order-free
selected-head exclusion under declarative correctness, establishes the full
raw-mark separation primitive for each candidate created by the successful
`new`. -/
theorem NewStep.created_rawMarksSeparatedFrom_of_retained
    {certificate : Certificate} {before after : ReservationState}
    (correct : certificate.DeclarativelyCorrect)
    (step : NewStep certificate before after)
    (retained : NewRetainedRawMarksSeparated step) :
    ∀ created : NewCreatedCandidate certificate step,
      OlderRawMarksSeparatedFrom certificate step.markedMiddle
        (ReservationEvent.new step).rawAge created.tensor.mate := by
  intro created rawAge vertex marked older region
  rcases UnificationState.markReadyRaw?_exact step.core_mark_eq with
    ⟨_selectedUnmarked, afterMarks, _parents, _components, _started,
      _fired, _selectedMarked⟩
  by_cases selectedEq : step.stackResult.vertex = vertex
  · subst vertex
    exact step.created_sourceRegion_not_selected correct created region
  · have beforeMarked :
        before.core.marks[vertex]? = some (some rawAge) := by
      change step.coreMarked.marks[vertex]? = some (some rawAge) at marked
      rw [afterMarks] at marked
      simpa [Array.getElem?_setIfInBounds, selectedEq] using marked
    exact retained created rawAge vertex beforeMarked older region

/-- A successful `new` preserves older raw-marked region separation provided
the caller supplies exactly the retained-input-mark versus created-candidate
side condition.  Retained candidates use prepared-prefix preservation, while
created candidates use `created_rawMarksSeparatedFrom_of_retained`.

No reachability or canonical-history assumption is silently strengthened into
the retained-mark side condition. -/
theorem NewStep.olderRawMarkedRegionSeparated
    {certificate : Certificate} {before after : ReservationState}
    (correct : certificate.DeclarativelyCorrect)
    (step : NewStep certificate before after)
    (invariant : SchedulerInvariant certificate before)
    (separated : OlderRawMarkedRegionSeparated certificate before)
    (createdSeparated : NewRetainedRawMarksSeparated step) :
    OlderRawMarkedRegionSeparated certificate after := by
  have middleSeparated :
      OlderRawMarkedRegionSeparated certificate step.markedMiddle :=
    step.preparedPrefix.olderRawMarkedRegionSeparated invariant separated
  refine { candidate := ?_ }
  intro candidate rawAge vertex marked older region
  have middleMarked :
      step.markedMiddle.core.marks[vertex]? = some (some rawAge) := by
    rw [← step.after_marks_eq_markedMiddle]
    exact marked
  have middleOlder :
      step.markedMiddle.core.representative rawAge <
        step.markedMiddle.core.representative candidate.rawAge := by
    rw [← step.after_representative_eq_markedMiddle rawAge,
      ← step.after_representative_eq_markedMiddle candidate.rawAge]
    exact older
  rcases candidate.work.beforeNewOrInserted step with
    oldWork | ⟨candidateAge, candidateHead⟩
  · let middleCandidate :
        FutureNewCandidateAt certificate step.markedMiddle := {
      rawAge := candidate.rawAge
      head := candidate.head
      work := oldWork
      tensor := candidate.tensor
      tensor_valid := candidate.tensor_valid
      mate_unmarked := by
        have mateUnmarked := candidate.mate_unmarked
        rw [step.after_marks_eq_markedMiddle] at mateUnmarked
        exact mateUnmarked }
    exact middleSeparated.candidate middleCandidate rawAge vertex
      middleMarked middleOlder region
  · let created : NewCreatedCandidate certificate step := {
      head := candidate.head
      endpoint := candidateHead
      tensor := candidate.tensor
      tensor_valid := candidate.tensor_valid
      mate_unmarked := by
        have mateUnmarked := candidate.mate_unmarked
        rw [step.after_marks_eq_markedMiddle] at mateUnmarked
        exact mateUnmarked }
    have createdSeparatedAt :
        OlderRawMarksSeparatedFrom certificate step.markedMiddle
          (ReservationEvent.new step).rawAge created.tensor.mate :=
      step.created_rawMarksSeparatedFrom_of_retained correct
        createdSeparated created
    apply createdSeparatedAt rawAge vertex middleMarked
    · simpa [candidateAge] using middleOlder
    · exact region

end SequentialFigure7

end ProofNetIR
