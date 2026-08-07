import ProofNetIR.SequentialFigure7SameRepresentativeGeometry

namespace ProofNetIRSameRepresentativeGeometryTests

open ProofNetIR
open ProofNetIR.SequentialFigure7
open ProofNetIR.SequentialSchedulerBridge
open ProofNetIR.SequentialSchedulerState
open ProofNetIR.SequentialUnification

/-! ## Generic graph API consumers -/

example {graph : Graph} {start finish vertex : Vertex}
    {steps : Nat} {visited : List Vertex}
    (walk : graph.SimpleWalk start steps visited finish)
    (membership : vertex ∈ visited) :
    ∃ restrictedSteps restricted,
      graph.SimpleWalk start restrictedSteps restricted vertex ∧
        ∀ candidate ∈ restricted, candidate ∈ visited :=
  walk.restrictWithSubset membership

example {graph : Graph} {start finish : Vertex}
    {traversed : List graph.DirectedEdge}
    (walk : graph.EdgeWalk start traversed finish) :
    ∃ steps visited,
      graph.SimpleWalk start steps visited finish ∧
        ∀ vertex ∈ visited,
          vertex ∈ Graph.EdgeWalk.visitedVertices start traversed :=
  walk.toSimpleWalkWithSubset

example {graph : Graph} {start finish : Vertex}
    {traversed : List graph.DirectedEdge}
    (walk : graph.EdgeWalk start traversed finish) :
    ∃ path : graph.EdgeSimplePath,
      path.start = start ∧ path.finish = finish ∧
        ∀ vertex ∈ path.vertices,
          vertex ∈ Graph.EdgeWalk.visitedVertices start traversed :=
  walk.toEdgeSimplePathWithVerticesSubset

example {graph : Graph} (first second : graph.EdgeSimplePath)
    (meeting : first.finish = second.start) {forbidden : Vertex}
    (firstAvoids : forbidden ∉ first.vertices)
    (secondAvoids : forbidden ∉ second.vertices) :
    ∃ path : graph.EdgeSimplePath,
      path.start = first.start ∧ path.finish = second.finish ∧
        forbidden ∉ path.vertices :=
  Graph.EdgeSimplePath.connectEraseAvoiding first second meeting
    firstAvoids secondAvoids

/-! ## Public component and terminal-geometry consumers -/

example {certificate : Certificate} {component : UnificationComponent}
    {usedLinks owned : List Nat}
    (witness :
      Certificate.ComponentOccurrenceWitness certificate component
        usedLinks owned)
    {first second : Vertex}
    (firstOwned : first ∈ owned) (secondOwned : second ∈ owned) :
    ∃ path : certificate.referenceSwitchingGraph.EdgeSimplePath,
      path.start = first ∧ path.finish = second ∧
        ∀ vertex ∈ path.vertices, vertex ∈ owned :=
  witness.referencePath_within_owned firstOwned secondOwned

example {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {start vertex forbidden : Vertex}
    (region : SourceLeftRegionVertex certificate start vertex)
    (startBelowForbidden :
      certificate.formulaComplexityAt start <
        certificate.formulaComplexityAt forbidden)
    (vertexNeForbidden : vertex ≠ forbidden) :
    ∃ path : certificate.referenceSwitchingGraph.EdgeSimplePath,
      path.start = start ∧ path.finish = vertex ∧
        forbidden ∉ path.vertices :=
  sourceLeftRegionVertex_referencePath_avoiding structural region
    startBelowForbidden vertexNeForbidden

example {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    (acyclic : certificate.referenceSwitchingGraph.Acyclic)
    {left right conclusion : Vertex}
    (membership : Link.tensor left right conclusion ∈ certificate.links)
    (path : certificate.referenceSwitchingGraph.EdgeSimplePath)
    (pathStarts : path.start = left)
    (pathFinishes : path.finish = right)
    (conclusionNotInPath : conclusion ∉ path.vertices) : False :=
  referenceAcyclic_no_tensorBypass structural acyclic membership path
    pathStarts pathFinishes conclusionNotInPath

/-! ## Public same-representative consumers -/

example {certificate : Certificate} {before : ReservationState}
    (invariant : SchedulerInvariant certificate before)
    (guard : NewGuard certificate before) :
    ¬ Produced before guard.tensor.conclusion :=
  guard.tensorConclusion_not_produced invariant

example {certificate : Certificate} {before : ReservationState}
    (invariant : SchedulerInvariant certificate before)
    (guard : NewGuard certificate before)
    {index : Nat} {component : UnificationComponent}
    {owned : List Vertex}
    (componentLookup :
      before.core.components[index]? = some (some component))
    (accounted :
      Certificate.OwnedOccurrenceAccounted before.core index component
        owned) :
    guard.tensor.conclusion ∉ owned :=
  guard.tensorConclusion_not_owned invariant componentLookup accounted

example {certificate : Certificate} {before : ReservationState}
    (invariant : SchedulerInvariant certificate before)
    (input : ReadyHeadInput before) :
    ∃ (component : UnificationComponent) (usedLinks owned : List Nat),
      before.core.components[input.rawAge]? = some (some component) ∧
        Certificate.ComponentOccurrenceWitness certificate component
          usedLinks owned ∧
        Certificate.OwnedOccurrenceAccounted before.core input.rawAge
          component owned ∧
        input.vertex ∈ owned ∧
        before.core.representative input.rawAge = input.rawAge :=
  input.activeComponent invariant

example {certificate : Certificate} {before : ReservationState}
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate before)
    (guard : NewGuard certificate before)
    {vertex : Vertex} {rawAge : RawTokenAge}
    (region :
      SourceLeftRegionVertex certificate guard.tensor.mate vertex)
    (marked : before.core.marks[vertex]? = some (some rawAge)) :
    before.core.representative rawAge ≠
      before.core.representative guard.head.rawAge :=
  guard.sourceLeftRegion_marked_representative_ne_active
    correct invariant region marked

/-! ## Checker-accepted structural fixture -/

private def geometryP : Formula := .atom "p" true
private def geometryQ : Formula := .atom "q" true

/- This is the canonical two-axiom/one-tensor certificate used by the nearby
Figure-7 scheduler regressions. -/
private def geometryCertificate : Certificate where
  formulas := #[
    geometryP,
    geometryP.dual,
    geometryQ,
    geometryQ.dual,
    .tensor geometryP geometryQ]
  links := [
    .axiom 0 1,
    .axiom 2 3,
    .tensor 0 2 4]
  conclusions := [4, 1, 3]

private theorem geometryCertificate_correct :
    geometryCertificate.DeclarativelyCorrect :=
  geometryCertificate.check_iff_declarativelyCorrect.mp (by native_decide)

private def geometryInitial : ReservationState :=
  match initializeReservation? geometryCertificate 0 with
  | some state => state
  | none => ReservationState.empty geometryCertificate

private theorem geometryInitial_eq :
    initializeReservation? geometryCertificate 0 = some geometryInitial := by
  native_decide

private theorem geometryInitial_invariant :
    SchedulerInvariant geometryCertificate geometryInitial :=
  initializeReservation?_schedulerInvariant geometryCertificate_correct.1
    geometryInitial_eq

private def geometryHead : ReadyHeadInput geometryInitial where
  vertex := 0
  readyTail := [1]
  rawAge := 0
  top_ready := by native_decide
  sigma_top := by native_decide

private def geometryTensor : TensorBelow where
  linkIndex := 2
  storedLeft := 0
  storedRight := 2
  conclusion := 4
  side := .storedLeft

private theorem geometryTensor_eq :
    geometryCertificate.tensorBelow? geometryHead.vertex =
      some geometryTensor := by
  native_decide

private def geometryGuard : NewGuard geometryCertificate geometryInitial where
  head := geometryHead
  tensor := geometryTensor
  tensor_valid := Certificate.tensorBelow?_eq_some_iff.mp geometryTensor_eq
  mate_unmarked := by native_decide

/- The executable initialization creates a genuine live axiom component.
Its two stored occurrences are joined by the new owned-carrier path theorem;
no scheduler progress or later `new` success is inferred. -/
set_option maxHeartbeats 800000 in
private theorem canonical_owned_reference_path :
    geometryCertificate.DeclarativelyCorrect ∧
      ∃ (component : UnificationComponent) (usedLinks owned : List Nat)
          (path : geometryCertificate.referenceSwitchingGraph.EdgeSimplePath),
        geometryInitial.core.components[0]? = some (some component) ∧
          Certificate.ComponentOccurrenceWitness geometryCertificate
            component usedLinks owned ∧
          0 ∈ owned ∧ 1 ∈ owned ∧
          path.start = 0 ∧ path.finish = 1 ∧
          ∀ vertex ∈ path.vertices, vertex ∈ owned := by
  refine ⟨geometryCertificate_correct, ?_⟩
  have sigmaLookup : geometryInitial.stack.sigma[0]? = some 0 := by
    native_decide
  have readyLookup : geometryInitial.stack.ready[0]? = some [0, 1] := by
    native_decide
  rcases geometryInitial_invariant.ready_bucket_frontier_exact
      sigmaLookup readyLookup with
    ⟨component, componentLookup, frontierExact⟩
  rcases geometryInitial_invariant.component_forest_provenance with
    ⟨usedAt, ownedAt, live, _disjoint, _markedOwned⟩
  rcases live componentLookup with ⟨witness, _accounted⟩
  have zeroFrontier : 0 ∈ component.frontier :=
    ((frontierExact 0).mp (by simp)).1
  have oneFrontier : 1 ∈ component.frontier :=
    ((frontierExact 1).mp (by simp)).1
  have zeroOwned : 0 ∈ ownedAt 0 :=
    witness.derivation.frontier_subset_owned 0 zeroFrontier
  have oneOwned : 1 ∈ ownedAt 0 :=
    witness.derivation.frontier_subset_owned 1 oneFrontier
  rcases witness.referencePath_within_owned zeroOwned oneOwned with
    ⟨path, pathStarts, pathFinishes, pathOwned⟩
  exact ⟨component, usedAt 0, ownedAt 0, path, componentLookup,
    witness, zeroOwned, oneOwned, pathStarts, pathFinishes, pathOwned⟩

example :
    geometryCertificate.DeclarativelyCorrect ∧
      ∃ (component : UnificationComponent) (usedLinks owned : List Nat)
          (path : geometryCertificate.referenceSwitchingGraph.EdgeSimplePath),
        geometryInitial.core.components[0]? = some (some component) ∧
          Certificate.ComponentOccurrenceWitness geometryCertificate
            component usedLinks owned ∧
          0 ∈ owned ∧ 1 ∈ owned ∧
          path.start = 0 ∧ path.finish = 1 ∧
          ∀ vertex ∈ path.vertices, vertex ∈ owned :=
  canonical_owned_reference_path

/- The same real initialized state exercises both active-component helpers. -/
private theorem canonical_active_component :
    ∃ (component : UnificationComponent) (usedLinks owned : List Nat),
      geometryInitial.core.components[geometryHead.rawAge]? =
          some (some component) ∧
        Certificate.ComponentOccurrenceWitness geometryCertificate component
          usedLinks owned ∧
        Certificate.OwnedOccurrenceAccounted geometryInitial.core
          geometryHead.rawAge component owned ∧
        geometryHead.vertex ∈ owned ∧
        geometryInitial.core.representative geometryHead.rawAge =
          geometryHead.rawAge :=
  geometryHead.activeComponent geometryInitial_invariant

private theorem canonical_tensor_conclusion_not_produced :
    ¬ Produced geometryInitial geometryGuard.tensor.conclusion :=
  geometryGuard.tensorConclusion_not_produced geometryInitial_invariant

private theorem canonical_tensor_conclusion_not_owned :
    ∃ (component : UnificationComponent) (usedLinks owned : List Nat),
      geometryInitial.core.components[geometryHead.rawAge]? =
          some (some component) ∧
        Certificate.ComponentOccurrenceWitness geometryCertificate component
          usedLinks owned ∧
        geometryGuard.tensor.conclusion ∉ owned := by
  rcases canonical_active_component with
    ⟨component, usedLinks, owned, lookup, witness, accounted,
      _headOwned, _root⟩
  exact ⟨component, usedLinks, owned, lookup, witness,
    geometryGuard.tensorConclusion_not_owned geometryInitial_invariant
      lookup accounted⟩

/- The terminal partner of the second submitted axiom has a concrete
reference path from source `2` that avoids the strictly larger tensor
conclusion `4`. -/
private theorem geometryTerminalRegion :
    SourceLeftRegionVertex geometryCertificate 2 3 :=
  .terminalPartner (linkIndex := 1) (.refl 2) (Or.inl (by native_decide))

private theorem canonical_terminal_region_path :
    ∃ path : geometryCertificate.referenceSwitchingGraph.EdgeSimplePath,
      path.start = 2 ∧ path.finish = 3 ∧ 4 ∉ path.vertices :=
  sourceLeftRegionVertex_referencePath_avoiding
    geometryCertificate_correct.1 geometryTerminalRegion
      (by native_decide) (by decide)

/- Compile the tensor-bypass contradiction against the actual accepted
fixture.  The path hypotheses are intentionally explicit: no bypass path or
progress statement is manufactured. -/
example
    (path : geometryCertificate.referenceSwitchingGraph.EdgeSimplePath)
    (pathStarts : path.start = 0) (pathFinishes : path.finish = 2)
    (conclusionNotInPath : 4 ∉ path.vertices) : False :=
  referenceAcyclic_no_tensorBypass geometryCertificate_correct.1
    geometryCertificate_correct.referenceSwitchingTree.acyclic
      (by native_decide) path pathStarts pathFinishes conclusionNotInPath

/- The main theorem remains conditional on a concrete old raw mark.  This
consumer fixes the real accepted certificate, initialized state, and guard;
it does not claim that such a mark exists in the initial state. -/
example {vertex : Vertex} {rawAge : RawTokenAge}
    (region :
      SourceLeftRegionVertex geometryCertificate
        geometryGuard.tensor.mate vertex)
    (marked : geometryInitial.core.marks[vertex]? = some (some rawAge)) :
    geometryInitial.core.representative rawAge ≠
      geometryInitial.core.representative geometryGuard.head.rawAge :=
  geometryGuard.sourceLeftRegion_marked_representative_ne_active
    geometryCertificate_correct geometryInitial_invariant region marked

/- Consume the remaining concrete fixture results. -/
example : ¬ Produced geometryInitial geometryGuard.tensor.conclusion :=
  canonical_tensor_conclusion_not_produced

example :
    ∃ (component : UnificationComponent) (usedLinks owned : List Nat),
      geometryInitial.core.components[geometryHead.rawAge]? =
          some (some component) ∧
        Certificate.ComponentOccurrenceWitness geometryCertificate component
          usedLinks owned ∧
        geometryGuard.tensor.conclusion ∉ owned :=
  canonical_tensor_conclusion_not_owned

example :
    ∃ path : geometryCertificate.referenceSwitchingGraph.EdgeSimplePath,
      path.start = 2 ∧ path.finish = 3 ∧ 4 ∉ path.vertices :=
  canonical_terminal_region_path

end ProofNetIRSameRepresentativeGeometryTests

def main : IO Unit :=
  IO.println "Figure-7 same-representative geometry passed"
