import ProofNetIR.SequentialFigure7BlockerHistory

namespace ProofNetIR

/-!
# Figure-7 terminal-partner switching geometry

The recursively visited source-left route cannot return to the selected ready
head by structural descent alone.  Its terminal axiom partner needs one
additional proof-net fact: in the deterministic all-left reference switching,
a sibling-to-sibling bypass of the selected tensor conclusion would close an
occurrence-aware cycle with the tensor's two fixed edges.

This module constructs that exact cycle.  It assumes reference-switching
acyclicity explicitly and does not derive scheduler progress, totality, or
worklist completeness.
-/

namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge
open SequentialUnification

private theorem axiomEdge_mem_leftRetained_local
    {links : List Link} {left right : Vertex}
    (membership : Link.axiom left right ∈ links) :
    ({ first := left, second := right } : Edge) ∈
      Certificate.linkLeftRetainedEdges links := by
  induction links with
  | nil =>
      simp at membership
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

private theorem parLeftEdge_mem_leftRetained_local
    {links : List Link} {left right conclusion : Vertex}
    (membership : Link.par left right conclusion ∈ links) :
    ({ first := left, second := conclusion } : Edge) ∈
      Certificate.linkLeftRetainedEdges links := by
  induction links with
  | nil =>
      simp at membership
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

/-- Every source-left step is an exact directed occurrence in the deterministic
all-left reference switching. -/
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
        exact parLeftEdge_mem_leftRetained_local membership
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

/-- A structural source-left route gives an exact simple path in the reference
switching. Every visited vertex remains source-left reachable from the original
start and has complexity at most that start. -/
private theorem sourceLeftReachable_referencePath
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {source target : Vertex}
    (reachable : SourceLeftReachable certificate source target) :
    ∃ path : certificate.referenceSwitchingGraph.EdgeSimplePath,
      path.start = source ∧
        path.finish = target ∧
          (∀ vertex ∈ path.vertices,
            certificate.formulaComplexityAt vertex ≤
              certificate.formulaComplexityAt source) ∧
          (∀ vertex ∈ path.vertices,
            SourceLeftReachable certificate source vertex) := by
  induction reachable with
  | refl vertex =>
      let path : certificate.referenceSwitchingGraph.EdgeSimplePath := {
        start := vertex
        finish := vertex
        traversed := []
        walk := .refl vertex
        verticesNodup := by
          simp [Graph.EdgeWalk.visitedVertices] }
      refine ⟨path, rfl, rfl, ?_, ?_⟩
      · intro candidate membership
        have same : candidate = vertex := by
          simpa [path, Graph.EdgeSimplePath.vertices,
            Graph.EdgeWalk.visitedVertices] using membership
        subst candidate
        exact Nat.le_refl _
      · intro candidate membership
        have same : candidate = vertex := by
          simpa [path, Graph.EdgeSimplePath.vertices,
            Graph.EdgeWalk.visitedVertices] using membership
        subst candidate
        exact .refl vertex
  | @step source next target head tail induction =>
      rcases induction with
        ⟨tailPath, tailStarts, tailFinishes, tailRanks,
          tailReachability⟩
      rcases sourceLeftStep_referenceDirectedEdge head with
        ⟨directed, directedStarts, directedTargets⟩
      have sourceFresh : source ∉ tailPath.vertices := by
        intro membership
        have tailRank := tailRanks source membership
        have strict := head.formulaComplexity_lt structural
        omega
      have combinedVertices :
          Graph.EdgeWalk.visitedVertices source
              (directed :: tailPath.traversed) =
            source :: tailPath.vertices := by
        simp [Graph.EdgeWalk.visitedVertices,
          Graph.EdgeSimplePath.vertices, directedTargets, ← tailStarts]
      have tailChain :
          certificate.referenceSwitchingGraph.EdgeChain directed.target
            tailPath.traversed target := by
        rw [directedTargets, ← tailStarts, ← tailFinishes]
        exact tailPath.walk.toChain
      let path : certificate.referenceSwitchingGraph.EdgeSimplePath := {
        start := source
        finish := target
        traversed := directed :: tailPath.traversed
        walk := by
          apply Graph.EdgeChain.toWalk
          exact Graph.EdgeChain.cons directed directedStarts tailChain
        verticesNodup := by
          rw [combinedVertices]
          exact List.nodup_cons.mpr
            ⟨sourceFresh, tailPath.verticesNodup⟩ }
      refine ⟨path, rfl, rfl, ?_, ?_⟩
      · intro candidate membership
        have split :
            candidate = source ∨ candidate ∈ tailPath.vertices := by
          simpa [path, Graph.EdgeSimplePath.vertices,
            combinedVertices] using membership
        rcases split with same | inTail
        · subst candidate
          exact Nat.le_refl _
        · exact Nat.le_trans (tailRanks candidate inTail)
            (Nat.le_of_lt (head.formulaComplexity_lt structural))
      · intro candidate membership
        have split :
            candidate = source ∨ candidate ∈ tailPath.vertices := by
          simpa [path, Graph.EdgeSimplePath.vertices,
            combinedVertices] using membership
        rcases split with same | inTail
        · subst candidate
          exact .refl source
        · exact .step head (tailReachability candidate inTail)

/-- The exact terminal axiom gives a directed reached-to-partner occurrence in
the reference switching, independently of its stored orientation. -/
private theorem terminalAxiom_referenceDirectedEdge
    {certificate : Certificate} {reached partner : Vertex} {linkIndex : Nat}
    (exactAxiom :
      certificate.links[linkIndex]? = some (.axiom reached partner) ∨
        certificate.links[linkIndex]? = some (.axiom partner reached)) :
    ∃ directed : certificate.referenceSwitchingGraph.DirectedEdge,
      directed.source = reached ∧ directed.target = partner := by
  rcases exactAxiom with storedForward | storedBackward
  · have membership := List.mem_of_getElem? storedForward
    have edgeMembership :
        ({ first := reached, second := partner } : Edge) ∈
          certificate.referenceSwitchingGraph.edges := by
      rw [UnificationMarking.referenceSwitchingGraph_edges_eq_leftRetained]
      exact axiomEdge_mem_leftRetained_local membership
    rcases List.getElem?_of_mem edgeMembership with
      ⟨edgeIndex, edgeLookup⟩
    let directed : certificate.referenceSwitchingGraph.DirectedEdge := {
      index := edgeIndex
      edge := { first := reached, second := partner }
      lookup := edgeLookup
      forward := true }
    refine ⟨directed, ?_, ?_⟩ <;>
      simp [directed, Graph.DirectedEdge.source,
        Graph.DirectedEdge.target]
  · have membership := List.mem_of_getElem? storedBackward
    have edgeMembership :
        ({ first := partner, second := reached } : Edge) ∈
          certificate.referenceSwitchingGraph.edges := by
      rw [UnificationMarking.referenceSwitchingGraph_edges_eq_leftRetained]
      exact axiomEdge_mem_leftRetained_local membership
    rcases List.getElem?_of_mem edgeMembership with
      ⟨edgeIndex, edgeLookup⟩
    let directed : certificate.referenceSwitchingGraph.DirectedEdge := {
      index := edgeIndex
      edge := { first := partner, second := reached }
      lookup := edgeLookup
      forward := false }
    refine ⟨directed, ?_, ?_⟩ <;>
      simp [directed, Graph.DirectedEdge.source,
        Graph.DirectedEdge.target]

/-- The source-left route followed by its terminal axiom has a simple
start-to-partner representative avoiding any strictly more complex forbidden
vertex distinct from the partner.

If the partner already occurs on the route, the corresponding reachable prefix
is rebuilt. Otherwise the exact terminal axiom occurrence is appended. -/
private theorem terminalPartner_referencePath_avoiding
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {start reached partner forbidden : Vertex} {linkIndex : Nat}
    (reachable : SourceLeftReachable certificate start reached)
    (exactAxiom :
      certificate.links[linkIndex]? = some (.axiom reached partner) ∨
        certificate.links[linkIndex]? = some (.axiom partner reached))
    (startBelowForbidden :
      certificate.formulaComplexityAt start <
        certificate.formulaComplexityAt forbidden)
    (partnerNeForbidden : partner ≠ forbidden) :
    ∃ path : certificate.referenceSwitchingGraph.EdgeSimplePath,
      path.start = start ∧ path.finish = partner ∧
        forbidden ∉ path.vertices := by
  rcases sourceLeftReachable_referencePath structural reachable with
    ⟨routePath, routeStarts, routeFinishes, routeRanks,
      routeReachability⟩
  by_cases partnerInRoute : partner ∈ routePath.vertices
  · have partnerReachable :=
      routeReachability partner partnerInRoute
    rcases sourceLeftReachable_referencePath structural partnerReachable with
      ⟨partnerPath, partnerStarts, partnerFinishes, partnerRanks,
        _partnerReachability⟩
    refine ⟨partnerPath, partnerStarts, partnerFinishes, ?_⟩
    intro forbiddenMembership
    have rank := partnerRanks forbidden forbiddenMembership
    omega
  · rcases terminalAxiom_referenceDirectedEdge exactAxiom with
      ⟨axiomDirected, axiomStarts, axiomFinishes⟩
    have reachedInRoute : reached ∈ routePath.vertices := by
      rw [← routeFinishes]
      exact routePath.walk.finish_mem_visitedVertices
    have reachedNePartner : reached ≠ partner := by
      intro same
      apply partnerInRoute
      rw [← same]
      exact reachedInRoute
    let axiomPath :
        certificate.referenceSwitchingGraph.EdgeSimplePath := {
      start := reached
      finish := partner
      traversed := [axiomDirected]
      walk := by
        exact Graph.EdgeWalk.step (.refl reached) axiomDirected
          axiomStarts axiomFinishes
      verticesNodup := by
        change [reached, axiomDirected.target].Nodup
        rw [axiomFinishes]
        simp [reachedNePartner] }
    have axiomVertices :
        axiomPath.vertices = [reached, partner] := by
      change [reached, axiomDirected.target] = [reached, partner]
      rw [axiomFinishes]
    have meeting : routePath.finish = axiomPath.start := by
      simpa [axiomPath] using routeFinishes
    have disjoint :
        ∀ vertex,
          vertex ∈ routePath.vertices →
            vertex ∈ axiomPath.vertices.tail → False := by
      intro vertex inRoute inAxiomTail
      rw [axiomVertices] at inAxiomTail
      have same : vertex = partner := by
        simpa using inAxiomTail
      subst vertex
      exact partnerInRoute inRoute
    let combined := routePath.append axiomPath meeting disjoint
    refine ⟨combined, ?_, ?_, ?_⟩
    · simp [combined, routeStarts]
    · simp [combined, axiomPath]
    · intro forbiddenMembership
      have split :
          forbidden ∈ routePath.vertices ∨
            forbidden ∈ axiomPath.vertices.tail := by
        simpa [combined] using forbiddenMembership
      rcases split with inRoute | inAxiomTail
      · have rank := routeRanks forbidden inRoute
        omega
      · rw [axiomVertices] at inAxiomTail
        have same : forbidden = partner := by
          simpa using inAxiomTail
        exact partnerNeForbidden same.symm

/-- A simple sibling-to-sibling path avoiding a submitted tensor's conclusion,
together with the two fixed tensor occurrences, contradicts reference
switching acyclicity. -/
private theorem referenceAcyclic_no_tensorBypass
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    (acyclic : certificate.referenceSwitchingGraph.Acyclic)
    {left right conclusion : Vertex}
    (membership : Link.tensor left right conclusion ∈ certificate.links)
    (path : certificate.referenceSwitchingGraph.EdgeSimplePath)
    (pathStarts : path.start = left)
    (pathFinishes : path.finish = right)
    (conclusionNotInPath : conclusion ∉ path.vertices) :
    False := by
  have wellFormed :
      certificate.LinkWellFormed (.tensor left right conclusion) :=
    structural.2.2.2.2.1 _ membership
  have pathNonempty : path.traversed ≠ [] := by
    intro empty
    have finishMembership := path.walk.finish_mem_visitedVertices
    have sameEndpoints : path.finish = path.start := by
      simpa [Graph.EdgeWalk.visitedVertices, empty] using finishMembership
    rw [pathStarts, pathFinishes] at sameEndpoints
    exact wellFormed.1 sameEndpoints.symm
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
  let rightDirected :
      certificate.referenceSwitchingGraph.DirectedEdge := {
    index := rightIndex
    edge := rightEdge
    lookup := rightEdgeLookup
    forward := true }
  let leftDirected :
      certificate.referenceSwitchingGraph.DirectedEdge := {
    index := leftIndex
    edge := leftEdge
    lookup := leftEdgeLookup
    forward := false }
  have tensorIndicesDifferent : rightIndex ≠ leftIndex := by
    intro sameIndex
    have sameEdges : rightEdge = leftEdge := by
      apply Option.some.inj
      rw [← rightEdgeLookup, ← leftEdgeLookup, sameIndex]
    apply wellFormed.1
    have sameFirst := congrArg Edge.first sameEdges
    simpa [rightEdge, leftEdge] using sameFirst.symm
  let returnPath : certificate.referenceSwitchingGraph.EdgeSimplePath := {
    start := right
    finish := left
    traversed := [rightDirected, leftDirected]
    walk := by
      simpa [rightDirected, leftDirected, rightEdge, leftEdge,
        Graph.DirectedEdge.source, Graph.DirectedEdge.target] using
        Graph.EdgeWalk.step
          (Graph.EdgeWalk.step
            (Graph.EdgeWalk.refl
              (graph := certificate.referenceSwitchingGraph) right)
            rightDirected rfl rfl)
          leftDirected rfl rfl
    verticesNodup := by
      simp [Graph.EdgeWalk.visitedVertices, rightDirected, leftDirected,
        rightEdge, leftEdge, Graph.DirectedEdge.target,
        wellFormed.2.2.1]
      exact
        ⟨fun same => wellFormed.1 same.symm,
          fun same => wellFormed.2.1 same.symm⟩ }
  have returnNonempty : returnPath.traversed ≠ [] := by
    simp [returnPath]
  have meeting : path.finish = returnPath.start := by
    simpa [returnPath] using pathFinishes
  have closing : returnPath.finish = path.start := by
    simpa [returnPath] using pathStarts.symm
  have vertexDisjoint :
      ∀ vertex,
        vertex ∈ path.vertices →
          vertex ∈ returnPath.vertices.tail.dropLast → False := by
    intro vertex pathMembership returnMembership
    have vertexConclusion : vertex = conclusion := by
      simpa [returnPath, Graph.EdgeSimplePath.vertices,
        Graph.EdgeWalk.visitedVertices, rightDirected, leftDirected,
        rightEdge, leftEdge, Graph.DirectedEdge.target] using
          returnMembership
    subst vertex
    exact conclusionNotInPath pathMembership
  have edgeDisjoint :
      ∀ index,
        index ∈ path.traversed.map Graph.DirectedEdge.index →
          index ∈ returnPath.traversed.map Graph.DirectedEdge.index →
            False := by
    intro index pathIndex returnIndex
    rcases List.mem_map.mp pathIndex with
      ⟨directed, directedMembership, directedIndex⟩
    have endpoints :=
      path.directed_endpoints_mem_vertices directedMembership
    have returnCases : index = rightIndex ∨ index = leftIndex := by
      simpa [returnPath, rightDirected, leftDirected] using returnIndex
    rcases returnCases with rightCase | leftCase
    · have sameIndex : directed.index = rightIndex :=
        directedIndex.trans rightCase
      have sameEdge : directed.edge = rightEdge := by
        apply Option.some.inj
        rw [← directed.lookup, ← rightEdgeLookup, sameIndex]
      cases forward : directed.forward with
      | false =>
          have sourceConclusion :
              directed.source = conclusion := by
            simp [Graph.DirectedEdge.source, forward, sameEdge, rightEdge]
          rw [sourceConclusion] at endpoints
          exact conclusionNotInPath endpoints.1
      | true =>
          have targetConclusion :
              directed.target = conclusion := by
            simp [Graph.DirectedEdge.target, forward, sameEdge, rightEdge]
          rw [targetConclusion] at endpoints
          exact conclusionNotInPath endpoints.2
    · have sameIndex : directed.index = leftIndex :=
        directedIndex.trans leftCase
      have sameEdge : directed.edge = leftEdge := by
        apply Option.some.inj
        rw [← directed.lookup, ← leftEdgeLookup, sameIndex]
      cases forward : directed.forward with
      | false =>
          have sourceConclusion :
              directed.source = conclusion := by
            simp [Graph.DirectedEdge.source, forward, sameEdge, leftEdge]
          rw [sourceConclusion] at endpoints
          exact conclusionNotInPath endpoints.1
      | true =>
          have targetConclusion :
              directed.target = conclusion := by
            simp [Graph.DirectedEdge.target, forward, sameEdge, leftEdge]
          rw [targetConclusion] at endpoints
          exact conclusionNotInPath endpoints.2
  let cycle : certificate.referenceSwitchingGraph.EdgeSimpleCycle :=
    Graph.EdgeSimpleCycle.ofTwoPaths
      path returnPath pathNonempty returnNonempty
      meeting closing vertexDisjoint edgeDisjoint
  exact acyclic cycle

namespace NewGuard

/-- A terminal source-left axiom partner cannot be the currently selected ready
head on a structurally well-formed proof net whose deterministic reference
switching is acyclic. -/
theorem terminalPartner_ne_head
    {certificate : Certificate}
    {before : SequentialSchedulerBridge.ReservationState}
    (structural : certificate.StructurallyWellFormed)
    (acyclic : certificate.referenceSwitchingGraph.Acyclic)
    (guard : NewGuard certificate before)
    {reached partner : Vertex} {linkIndex : Nat}
    (reachable :
      SourceLeftReachable certificate guard.tensor.mate reached)
    (exactAxiom :
      certificate.links[linkIndex]? = some (.axiom reached partner) ∨
        certificate.links[linkIndex]? = some (.axiom partner reached)) :
    partner ≠ guard.head.vertex := by
  intro partnerIsHead
  subst partner
  have tensorLookup := guard.tensor_valid.2.1
  have tensorMembership := List.mem_of_getElem? tensorLookup
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
  have headNeConclusion :
      guard.head.vertex ≠ guard.tensor.conclusion := by
    have headEquation := guard.tensor_valid.2.2.2
    cases sideEquation : guard.tensor.side with
    | storedLeft =>
        have headIsLeft :
            guard.head.vertex = guard.tensor.storedLeft := by
          simpa [TensorBelow.premise, TensorPremiseSide.premise,
            sideEquation] using headEquation
        rw [headIsLeft]
        exact tensorWellFormed.2.1
    | storedRight =>
        have headIsRight :
            guard.head.vertex = guard.tensor.storedRight := by
          simpa [TensorBelow.premise, TensorPremiseSide.premise,
            sideEquation] using headEquation
        rw [headIsRight]
        exact tensorWellFormed.2.2.1
  rcases terminalPartner_referencePath_avoiding structural reachable
      exactAxiom mateBelowConclusion headNeConclusion with
    ⟨path, pathStarts, pathFinishes, conclusionNotInPath⟩
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
      apply referenceAcyclic_no_tensorBypass structural acyclic
        tensorMembership path.reverse
      · exact pathFinishes.trans headIsLeft
      · exact pathStarts.trans mateIsRight
      · simpa using conclusionNotInPath
  | storedRight =>
      have headIsRight :
          guard.head.vertex = guard.tensor.storedRight := by
        simpa [TensorBelow.premise, TensorPremiseSide.premise,
          sideEquation] using headEquation
      have mateIsLeft :
          guard.tensor.mate = guard.tensor.storedLeft := by
        simp [TensorBelow.mate, TensorPremiseSide.mate, sideEquation]
      apply referenceAcyclic_no_tensorBypass structural acyclic
        tensorMembership path
      · exact pathStarts.trans mateIsLeft
      · exact pathFinishes.trans headIsRight
      · exact conclusionNotInPath

/-- Declarative proof-net correctness supplies the reference-switching
acyclicity needed by `terminalPartner_ne_head`. -/
theorem terminalPartner_ne_head_of_declarativelyCorrect
    {certificate : Certificate}
    {before : SequentialSchedulerBridge.ReservationState}
    (correct : certificate.DeclarativelyCorrect)
    (guard : NewGuard certificate before)
    {reached partner : Vertex} {linkIndex : Nat}
    (reachable :
      SourceLeftReachable certificate guard.tensor.mate reached)
    (exactAxiom :
      certificate.links[linkIndex]? = some (.axiom reached partner) ∨
        certificate.links[linkIndex]? = some (.axiom partner reached)) :
    partner ≠ guard.head.vertex :=
  guard.terminalPartner_ne_head correct.1
    correct.referenceSwitchingTree.acyclic reachable exactAxiom

end NewGuard

namespace CanonicalTagHistory

/-- Under reference-switching acyclicity, a raw-mark failure anywhere in the
complete source-left region has an exact old live-component owner.  Structural
descent handles recursively visited vertices; the switching-cycle argument
handles the terminal axiom partner. -/
theorem classifyFreshRawBlocker_of_referenceAcyclic
    {certificate : Certificate} {before : ReservationState}
    (invariant : SchedulerInvariant certificate before)
    (acyclic : certificate.referenceSwitchingGraph.Acyclic)
    (guard : NewGuard certificate before)
    {vertex : Vertex}
    (region :
      SourceLeftRegionVertex certificate guard.tensor.mate vertex)
    (markBlocked :
      guard.head.markedCore.marks[vertex]? ≠ some none) :
    ExactMarkedOccurrenceOwner certificate before.core vertex := by
  cases region with
  | visited reachable =>
      exact classifyVisitedFreshRawBlocker invariant guard reachable
        markBlocked
  | @terminalPartner reached partner linkIndex reachable exactAxiom =>
      rcases classifyFreshRawBlocker invariant guard
          (.terminalPartner reachable exactAxiom) markBlocked with
        selected | owned
      · exact False.elim
          (guard.terminalPartner_ne_head invariant.structural acyclic
            reachable exactAxiom selected)
      · exact owned

/-- With reference-switching acyclicity, every dynamic source-region failure
is either an exact prior canonical touch or an exact old live-component owner;
the selected-head alternative has been eliminated for both region forms. -/
theorem classifyFreshBlocker_of_referenceAcyclic
    {certificate : Certificate} {before : ReservationState}
    {history : ExecutedHistory certificate before}
    (tagHistory : CanonicalTagHistory certificate history)
    (invariant : SchedulerInvariant certificate before)
    (acyclic : certificate.referenceSwitchingGraph.Acyclic)
    (guard : NewGuard certificate before)
    {vertex : Vertex}
    (region :
      SourceLeftRegionVertex certificate guard.tensor.mate vertex)
    (unavailable :
      before.tags[vertex]? ≠ some false ∨
        guard.head.markedCore.marks[vertex]? ≠ some none) :
    tagHistory.Touched vertex ∨
      ExactMarkedOccurrenceOwner certificate before.core vertex := by
  rcases unavailable with tagBlocked | markBlocked
  · exact Or.inl
      (tagHistory.classifyFreshTagBlocker invariant guard region tagBlocked)
  · exact Or.inr
      (classifyFreshRawBlocker_of_referenceAcyclic invariant acyclic guard
        region markBlocked)

/-- A complete fresh-source blocker on an acyclic reference switching has
only historical tag-touch or exact old-component ownership provenance. -/
theorem classifyFreshSourceBlocker_of_referenceAcyclic
    {certificate : Certificate} {before : ReservationState}
    {history : ExecutedHistory certificate before}
    (tagHistory : CanonicalTagHistory certificate history)
    (invariant : SchedulerInvariant certificate before)
    (acyclic : certificate.referenceSwitchingGraph.Acyclic)
    (guard : NewGuard certificate before)
    (blocker :
      FreshSourceBlocker certificate guard.head.markedCore before.tags
        guard.tensor.mate) :
    tagHistory.Touched blocker.vertex ∨
      ExactMarkedOccurrenceOwner certificate before.core blocker.vertex :=
  tagHistory.classifyFreshBlocker_of_referenceAcyclic invariant acyclic guard
    blocker.region blocker.unavailable

/-- Declarative correctness removes the selected-head branch from every
complete source-left blocker classification.  Prior-touch and old-owner
obstructions remain explicit and are not discharged here. -/
theorem classifyFreshSourceBlocker_of_declarativelyCorrect
    {certificate : Certificate} {before : ReservationState}
    {history : ExecutedHistory certificate before}
    (tagHistory : CanonicalTagHistory certificate history)
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate before)
    (guard : NewGuard certificate before)
    (blocker :
      FreshSourceBlocker certificate guard.head.markedCore before.tags
        guard.tensor.mate) :
    tagHistory.Touched blocker.vertex ∨
      ExactMarkedOccurrenceOwner certificate before.core blocker.vertex :=
  tagHistory.classifyFreshSourceBlocker_of_referenceAcyclic invariant
    correct.referenceSwitchingTree.acyclic guard blocker

end CanonicalTagHistory

end SequentialFigure7

end ProofNetIR
