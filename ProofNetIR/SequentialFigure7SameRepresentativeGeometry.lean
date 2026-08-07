import ProofNetIR.SequentialComponentReferenceGeometry
import ProofNetIR.SequentialFigure7ReservationRealization
import ProofNetIR.SequentialFigure7TerminalPartnerGeometry

namespace ProofNetIR

/-!
# Figure-7 same-representative source-region geometry

An input raw mark in the selected tensor mate's structural source-left region
cannot belong to the currently active live component.  If it did, exact
component provenance would provide a reference-switching path from that marked
occurrence to the ready head.  The structural source-region path supplies the
other half.  Both paths avoid the selected tensor conclusion, so together they
form a sibling-to-sibling bypass forbidden by reference-switching acyclicity.

This is a local obstruction-exclusion theorem.  It does not assert that a fresh
source-left run exists, that the dispatcher progresses, or that the worklist
sequentializer is complete.
-/

namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge
open SequentialUnification

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

namespace NewGuard

/-- The selected tensor conclusion has not yet been observably produced.

If it had, ProducedPremisesMarked would raw-mark both submitted premises,
contradicting the input guard's exact unmarked mate. -/
theorem tensorConclusion_not_produced
    {certificate : Certificate} {before : ReservationState}
    (guard : NewGuard certificate before)
    (invariant : SchedulerInvariant certificate before) :
    ¬ Produced before guard.tensor.conclusion := by
  intro produced
  have tensorMembership :
      Link.tensor guard.tensor.storedLeft guard.tensor.storedRight
          guard.tensor.conclusion ∈ certificate.links :=
    List.mem_of_getElem? guard.tensor_valid.2.1
  have premises :=
    invariant.produced_premises_marked tensorMembership produced
  cases sideEquation : guard.tensor.side with
  | storedLeft =>
      rcases premises.2 with ⟨mateAge, mateMarked⟩
      have mateIsRight :
          guard.tensor.mate = guard.tensor.storedRight := by
        simp [TensorBelow.mate, TensorPremiseSide.mate, sideEquation]
      rw [← mateIsRight, guard.mate_unmarked] at mateMarked
      simp at mateMarked
  | storedRight =>
      rcases premises.1 with ⟨mateAge, mateMarked⟩
      have mateIsLeft :
          guard.tensor.mate = guard.tensor.storedLeft := by
        simp [TensorBelow.mate, TensorPremiseSide.mate, sideEquation]
      rw [← mateIsLeft, guard.mate_unmarked] at mateMarked
      simp at mateMarked

/-- The selected tensor conclusion is absent from every exact owned list whose
live component lookup and ownership accounting are supplied. -/
theorem tensorConclusion_not_owned
    {certificate : Certificate} {before : ReservationState}
    (guard : NewGuard certificate before)
    (invariant : SchedulerInvariant certificate before)
    {index : Nat} {component : UnificationComponent}
    {owned : List Vertex}
    (componentLookup :
      before.core.components[index]? = some (some component))
    (accounted :
      Certificate.OwnedOccurrenceAccounted before.core index component owned) :
    guard.tensor.conclusion ∉ owned := by
  intro conclusionOwned
  apply guard.tensorConclusion_not_produced invariant
  rcases accounted guard.tensor.conclusion conclusionOwned with
    ⟨rawAge, marked, _representative⟩ | ⟨_unmarked, frontier⟩
  · exact Or.inl ⟨rawAge, marked⟩
  · exact Or.inr
      (mem_liveFrontierVertices_of_raw componentLookup frontier)

end NewGuard

namespace ReadyHeadInput

/-- Exact live-component provenance for the active ready head.

The result packages the raw component lookup, its occurrence derivation and
owned-occurrence accounting, ownership of the selected head, and the fact that
the active sigma boundary is a union-find root. -/
theorem activeComponent
    {certificate : Certificate} {before : ReservationState}
    (input : ReadyHeadInput before)
    (invariant : SchedulerInvariant certificate before) :
    ∃ (component : UnificationComponent) (usedLinks owned : List Nat),
      before.core.components[input.rawAge]? = some (some component) ∧
        Certificate.ComponentOccurrenceWitness certificate component
          usedLinks owned ∧
        Certificate.OwnedOccurrenceAccounted before.core input.rawAge
          component owned ∧
        input.vertex ∈ owned ∧
        before.core.representative input.rawAge = input.rawAge := by
  rcases List.getLast?_eq_some_iff.mp input.top_ready with
    ⟨readyPrefix, readyDecomposition⟩
  rcases List.getLast?_eq_some_iff.mp input.sigma_top with
    ⟨sigmaPrefix, sigmaDecomposition⟩
  have prefixLengths : readyPrefix.length = sigmaPrefix.length := by
    have aligned := invariant.stack_wellShaped.ready_aligned
    rw [readyDecomposition, sigmaDecomposition] at aligned
    simp at aligned
    omega
  have topSigmaLookup :
      before.stack.sigma[readyPrefix.length]? = some input.rawAge := by
    rw [sigmaDecomposition, prefixLengths]
    simp
  have topReadyLookup :
      before.stack.ready[readyPrefix.length]? =
        some (input.vertex :: input.readyTail) := by
    rw [readyDecomposition]
    simp
  rcases invariant.ready_bucket_frontier_exact
      topSigmaLookup topReadyLookup with
    ⟨component, componentLookup, frontierExact⟩
  have headFrontier : input.vertex ∈ component.frontier :=
    (frontierExact input.vertex).mp (by simp) |>.1
  rcases invariant.component_forest_provenance with
    ⟨usedAt, ownedAt, live, _disjoint, _markedOwned⟩
  rcases live componentLookup with ⟨witness, accounted⟩
  have headOwned : input.vertex ∈ ownedAt input.rawAge :=
    witness.derivation.frontier_subset_owned input.vertex headFrontier
  have rawAgeBound : input.rawAge < before.stack.nextAge := by
    have membership : input.rawAge ∈ before.stack.sigma := by
      rw [sigmaDecomposition]
      simp
    exact invariant.stack_wellShaped.sigma_partition.boundary_lt
      input.rawAge membership
  have rawAgeRoot :
      before.core.representative input.rawAge = input.rawAge := by
    have boundaryLookup :
        sigmaBoundary? before.stack.sigma input.rawAge =
          some input.rawAge :=
      invariant.stack_wellShaped.sigma_partition
        |>.sigmaBoundary?_eq_top input.sigma_top
    have realizesLookup :=
      invariant.realizesSigma.representative_eq_boundary rawAgeBound
    exact Option.some.inj (realizesLookup.symm.trans boundaryLookup)
  exact ⟨component, usedAt input.rawAge, ownedAt input.rawAge,
    componentLookup, witness, accounted, headOwned, rawAgeRoot⟩

end ReadyHeadInput

namespace NewGuard

/-- A concrete input raw mark anywhere in the selected mate's complete
structural source-left region cannot have the active ready head's current
representative. -/
theorem sourceLeftRegion_marked_representative_ne_active
    {certificate : Certificate} {before : ReservationState}
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate before)
    (guard : NewGuard certificate before)
    {vertex : Vertex} {rawAge : RawTokenAge}
    (region :
      SourceLeftRegionVertex certificate guard.tensor.mate vertex)
    (marked : before.core.marks[vertex]? = some (some rawAge)) :
    before.core.representative rawAge ≠
      before.core.representative guard.head.rawAge := by
  rcases guard.head.activeComponent invariant with
    ⟨activeComponent, activeUsed, activeOwned, activeLookup,
      activeWitness, activeAccounted, headOwned, activeRoot⟩
  rcases
      ProofNetIR.SequentialFigure7.SchedulerInvariant.exactMarkedOccurrenceOwner
        invariant marked with
    ⟨ownerRawAge, ownerIndex, ownerComponent, ownerUsed, ownerOwned,
      ownerMarked, ownerRepresentative, ownerLookup, ownerWitness,
      ownerAccounted, vertexOwnerOwned⟩
  have ownerRawAgeEq : ownerRawAge = rawAge := by
    exact Option.some.inj
      (Option.some.inj (ownerMarked.symm.trans marked))
  subst ownerRawAge
  intro sameRepresentative
  have ownerIndexEq : ownerIndex = guard.head.rawAge := by
    calc
      ownerIndex = before.core.representative rawAge :=
        ownerRepresentative.symm
      _ = before.core.representative guard.head.rawAge :=
        sameRepresentative
      _ = guard.head.rawAge := activeRoot
  have ownerLookupAtActive :
      before.core.components[guard.head.rawAge]? =
        some (some ownerComponent) := by
    simpa [ownerIndexEq] using ownerLookup
  have componentEq : ownerComponent = activeComponent := by
    exact Option.some.inj
      (Option.some.inj (ownerLookupAtActive.symm.trans activeLookup))
  subst ownerComponent
  have ownedEq : ownerOwned = activeOwned :=
    Certificate.OccurrenceDerivation.owned_unique invariant.structural
      ownerWitness.derivation activeWitness.derivation
  have vertexActiveOwned : vertex ∈ activeOwned := by
    rw [← ownedEq]
    exact vertexOwnerOwned
  rcases activeWitness.referencePath_within_owned
      vertexActiveOwned headOwned with
    ⟨componentPath, componentStarts, componentFinishes,
      componentPathOwned⟩
  have conclusionNotOwned :
      guard.tensor.conclusion ∉ activeOwned :=
    guard.tensorConclusion_not_owned invariant
      activeLookup activeAccounted
  have componentAvoids :
      guard.tensor.conclusion ∉ componentPath.vertices := by
    intro conclusionMembership
    exact conclusionNotOwned
      (componentPathOwned guard.tensor.conclusion conclusionMembership)
  have tensorMembership :
      Link.tensor guard.tensor.storedLeft guard.tensor.storedRight
          guard.tensor.conclusion ∈ certificate.links :=
    List.mem_of_getElem? guard.tensor_valid.2.1
  have tensorWellFormed := guard.tensor_valid.2.2.1
  have mateBelowConclusion :
      certificate.formulaComplexityAt guard.tensor.mate <
        certificate.formulaComplexityAt guard.tensor.conclusion := by
    simpa [Certificate.linkConclusionComplexity] using
      tensorWellFormed.premise_complexity_lt_conclusion
        (premise := guard.tensor.mate) (by
          cases sideEquation : guard.tensor.side <;>
            simp [Link.premises, TensorBelow.mate,
              TensorPremiseSide.mate, sideEquation])
  have vertexNeConclusion :
      vertex ≠ guard.tensor.conclusion := by
    intro same
    apply guard.tensorConclusion_not_produced invariant
    exact Or.inl ⟨rawAge, by simpa [same] using marked⟩
  rcases sourceLeftRegionVertex_referencePath_avoiding
      invariant.structural region mateBelowConclusion vertexNeConclusion with
    ⟨regionPath, regionStarts, regionFinishes, regionAvoids⟩
  have meeting : regionPath.finish = componentPath.start :=
    regionFinishes.trans componentStarts.symm
  rcases Graph.EdgeSimplePath.connectEraseAvoiding
      regionPath componentPath meeting regionAvoids componentAvoids with
    ⟨path, pathStarts, pathFinishes, conclusionNotInPath⟩
  have combinedStarts : path.start = guard.tensor.mate :=
    pathStarts.trans regionStarts
  have combinedFinishes : path.finish = guard.head.vertex :=
    pathFinishes.trans componentFinishes
  have headEquation := guard.tensor_valid.2.2.2
  cases sideEquation : guard.tensor.side with
  | storedLeft =>
      have headIsLeft :
          guard.head.vertex = guard.tensor.storedLeft := by
        simpa [TensorBelow.premise, TensorPremiseSide.premise,
          sideEquation] using headEquation
      have mateIsRight :
          guard.tensor.mate = guard.tensor.storedRight := by
        simp [TensorBelow.mate, TensorPremiseSide.mate, sideEquation]
      apply referenceAcyclic_no_tensorBypass invariant.structural
        correct.referenceSwitchingTree.acyclic tensorMembership path.reverse
      · exact combinedFinishes.trans headIsLeft
      · exact combinedStarts.trans mateIsRight
      · simpa using conclusionNotInPath
  | storedRight =>
      have headIsRight :
          guard.head.vertex = guard.tensor.storedRight := by
        simpa [TensorBelow.premise, TensorPremiseSide.premise,
          sideEquation] using headEquation
      have mateIsLeft :
          guard.tensor.mate = guard.tensor.storedLeft := by
        simp [TensorBelow.mate, TensorPremiseSide.mate, sideEquation]
      apply referenceAcyclic_no_tensorBypass invariant.structural
        correct.referenceSwitchingTree.acyclic tensorMembership path
      · exact combinedStarts.trans mateIsLeft
      · exact combinedFinishes.trans headIsRight
      · exact conclusionNotInPath

end NewGuard

end SequentialFigure7

end ProofNetIR
