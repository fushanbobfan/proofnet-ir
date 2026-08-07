import ProofNetIR.SequentialComponentProvenance

namespace ProofNetIR

/-!
# Reference-switching geometry of live occurrence components

Every occurrence-exact runtime component is connected inside the deterministic
all-left reference switching by paths that stay within the component's exact
owned-occurrence carrier.  The proof follows submitted link positions through
the axiom, par, tensor, and exchange constructors; repeated formula labels are
never used as occurrence identities.

The final path is occurrence-aware.  Loop erasure may choose another stored
occurrence with the same edge value, so this module does not claim preservation
of a particular parallel-edge index along the returned path.
-/

namespace Certificate

private theorem axiomEdge_mem_leftRetained_geometry
    {links : List Link} {left right : Vertex}
    (membership : Link.axiom left right ∈ links) :
    ({ first := left, second := right } : Edge) ∈
      Certificate.linkLeftRetainedEdges links := by
  induction links with
  | nil => simp at membership
  | cons head tail ih =>
      rcases List.mem_cons.mp membership with rfl | rest
      · simp [Certificate.linkLeftRetainedEdges]
      · cases head <;>
          simp only [Certificate.linkLeftRetainedEdges, List.mem_cons] <;>
          first | exact Or.inr (ih rest) |
            exact Or.inr (Or.inr (ih rest))

private theorem parLeftEdge_mem_leftRetained_geometry
    {links : List Link} {left right conclusion : Vertex}
    (membership : Link.par left right conclusion ∈ links) :
    ({ first := left, second := conclusion } : Edge) ∈
      Certificate.linkLeftRetainedEdges links := by
  induction links with
  | nil => simp at membership
  | cons head tail ih =>
      rcases List.mem_cons.mp membership with rfl | rest
      · simp [Certificate.linkLeftRetainedEdges]
      · cases head <;>
          simp only [Certificate.linkLeftRetainedEdges, List.mem_cons] <;>
          first | exact Or.inr (ih rest) |
            exact Or.inr (Or.inr (ih rest))

/-- Same-name subgraph of the reference switching induced by one exact owned
occurrence carrier. -/
private def referenceOwnedGraph (certificate : Certificate)
    (owned : List Vertex) : Graph where
  vertexCount := certificate.referenceSwitchingGraph.vertexCount
  edges := certificate.referenceSwitchingGraph.edges.filter fun edge =>
    owned.contains edge.first && owned.contains edge.second

private theorem referenceOwnedGraph_edges_subset
    (certificate : Certificate) (owned : List Vertex) :
    ∀ edge ∈ (referenceOwnedGraph certificate owned).edges,
      edge ∈ certificate.referenceSwitchingGraph.edges := by
  intro edge membership
  exact (List.mem_filter.mp membership).1

private theorem referenceOwnedGraph_edge_mem
    {certificate : Certificate} {owned : List Vertex}
    {edge : Edge}
    (ambient : edge ∈ certificate.referenceSwitchingGraph.edges)
    (firstOwned : edge.first ∈ owned)
    (secondOwned : edge.second ∈ owned) :
    edge ∈ (referenceOwnedGraph certificate owned).edges := by
  apply List.mem_filter.mpr
  exact ⟨ambient, by simp [firstOwned, secondOwned]⟩

private theorem referenceOwnedGraph_mono
    {certificate : Certificate} {small large : List Vertex}
    (subset : ∀ vertex, vertex ∈ small → vertex ∈ large) :
    ∀ edge ∈ (referenceOwnedGraph certificate small).edges,
      edge ∈ (referenceOwnedGraph certificate large).edges := by
  intro edge membership
  rcases List.mem_filter.mp membership with ⟨ambient, endpoints⟩
  have endpointFacts := Bool.and_eq_true_iff.mp endpoints
  have firstSmall : edge.first ∈ small :=
    List.contains_iff_mem.mp endpointFacts.1
  have secondSmall : edge.second ∈ small :=
    List.contains_iff_mem.mp endpointFacts.2
  exact referenceOwnedGraph_edge_mem ambient
    (subset edge.first firstSmall) (subset edge.second secondSmall)

private theorem referenceOwnedGraph_adjacent
    {certificate : Certificate} {owned : List Vertex}
    {left right : Vertex} {edge : Edge}
    (ambient : edge ∈ certificate.referenceSwitchingGraph.edges)
    (edgeEq : edge = { first := left, second := right })
    (leftOwned : left ∈ owned) (rightOwned : right ∈ owned) :
    (referenceOwnedGraph certificate owned).Adjacent left right := by
  subst edge
  refine ⟨{ first := left, second := right },
    referenceOwnedGraph_edge_mem ambient leftOwned rightOwned,
    Or.inl ⟨rfl, rfl⟩⟩

/-- One occurrence derivation admits a root connected to every exact owned
occurrence inside the induced owned subgraph. -/
private theorem OccurrenceDerivation.referenceRootConnected
    {certificate : Certificate}
    {tree : CutFreeDerivation} {frontier usedLinks owned : List Nat}
    (witness :
      OccurrenceDerivation certificate tree frontier usedLinks owned) :
    ∃ root ∈ owned, ∀ vertex ∈ owned,
      (referenceOwnedGraph certificate owned).Walk root vertex := by
  induction witness with
  | «axiom» linkIndex left right name positive linkLookup leftFormula =>
      have membership := List.mem_of_getElem? linkLookup
      have ambient :
          ({ first := left, second := right } : Edge) ∈
            certificate.referenceSwitchingGraph.edges := by
        rw [UnificationMarking.referenceSwitchingGraph_edges_eq_leftRetained]
        exact axiomEdge_mem_leftRetained_geometry membership
      have adjacent :
          (referenceOwnedGraph certificate [left, right]).Adjacent left right :=
        referenceOwnedGraph_adjacent ambient rfl (by simp) (by simp)
      refine ⟨left, by simp, ?_⟩
      intro vertex vertexOwned
      simp at vertexOwned
      rcases vertexOwned with same | same
      · subst vertex
        exact .refl left
      · subst vertex
        exact .step (.refl left) adjacent
  | @par premise frontier usedLinks owned premiseWitness
      linkIndex left right conclusion leftFocus rightFocus afterLeft context
      linkLookup leftPick rightPick induction =>
      rcases induction with ⟨root, rootOwned, connected⟩
      have oldSubset :
          ∀ vertex, vertex ∈ owned → vertex ∈ conclusion :: owned := by
        intro vertex membership
        exact List.mem_cons_of_mem conclusion membership
      have graphSubset :=
        referenceOwnedGraph_mono
          (certificate := certificate) oldSubset
      have leftFrontier : left ∈ frontier :=
        (CutFreeDerivation.pick?_perm leftPick.positional).mem_iff.mpr
          (by simp)
      have leftOwned : left ∈ owned :=
        premiseWitness.frontier_subset_owned left leftFrontier
      have membership := List.mem_of_getElem? linkLookup
      have ambient :
          ({ first := left, second := conclusion } : Edge) ∈
            certificate.referenceSwitchingGraph.edges := by
        rw [UnificationMarking.referenceSwitchingGraph_edges_eq_leftRetained]
        exact parLeftEdge_mem_leftRetained_geometry membership
      have adjacent :
          (referenceOwnedGraph certificate (conclusion :: owned)).Adjacent
            left conclusion :=
        referenceOwnedGraph_adjacent ambient rfl
          (oldSubset left leftOwned) (by simp)
      refine ⟨root, oldSubset root rootOwned, ?_⟩
      intro vertex vertexOwned
      simp only [List.mem_cons] at vertexOwned
      rcases vertexOwned with same | oldOwned
      · subst vertex
        exact (Graph.Walk.mono graphSubset (connected left leftOwned)).trans
          (.step (.refl left) adjacent)
      · exact Graph.Walk.mono graphSubset (connected vertex oldOwned)
  | @tensor leftTree rightTree leftFrontier rightFrontier
      leftUsed rightUsed leftOwned rightOwned leftWitness rightWitness
      linkIndex left right conclusion leftFocus rightFocus
      leftContext rightContext linkLookup leftPick rightPick
      leftInduction rightInduction =>
      rcases leftInduction with
        ⟨leftRoot, leftRootOwned, leftConnected⟩
      rcases rightInduction with
        ⟨rightRoot, rightRootOwned, rightConnected⟩
      let allOwned := conclusion :: (leftOwned ++ rightOwned)
      have leftSubset :
          ∀ vertex, vertex ∈ leftOwned → vertex ∈ allOwned := by
        intro vertex membership
        exact List.mem_cons_of_mem conclusion
          (List.mem_append_left rightOwned membership)
      have rightSubset :
          ∀ vertex, vertex ∈ rightOwned → vertex ∈ allOwned := by
        intro vertex membership
        exact List.mem_cons_of_mem conclusion
          (List.mem_append_right leftOwned membership)
      have leftGraphSubset :=
        referenceOwnedGraph_mono
          (certificate := certificate) leftSubset
      have rightGraphSubset :=
        referenceOwnedGraph_mono
          (certificate := certificate) rightSubset
      have leftFrontierMembership : left ∈ leftFrontier :=
        (CutFreeDerivation.pick?_perm leftPick.positional).mem_iff.mpr
          (by simp)
      have rightFrontierMembership : right ∈ rightFrontier :=
        (CutFreeDerivation.pick?_perm rightPick.positional).mem_iff.mpr
          (by simp)
      have leftMembership : left ∈ leftOwned :=
        leftWitness.frontier_subset_owned left leftFrontierMembership
      have rightMembership : right ∈ rightOwned :=
        rightWitness.frontier_subset_owned right rightFrontierMembership
      have membership := List.mem_of_getElem? linkLookup
      have ambient :=
        UnificationMarking.referenceSwitchingGraph_tensorEdges
          certificate membership
      have leftAdjacent :
          (referenceOwnedGraph certificate allOwned).Adjacent
            left conclusion :=
        referenceOwnedGraph_adjacent ambient.1 rfl
          (leftSubset left leftMembership) (by simp [allOwned])
      have rightAdjacent :
          (referenceOwnedGraph certificate allOwned).Adjacent
            right conclusion :=
        referenceOwnedGraph_adjacent ambient.2 rfl
          (rightSubset right rightMembership) (by simp [allOwned])
      have leftRootToLeft :
          (referenceOwnedGraph certificate allOwned).Walk leftRoot left :=
        Graph.Walk.mono leftGraphSubset
          (leftConnected left leftMembership)
      have rightRootToRight :
          (referenceOwnedGraph certificate allOwned).Walk rightRoot right :=
        Graph.Walk.mono rightGraphSubset
          (rightConnected right rightMembership)
      have leftRootToConclusion :
          (referenceOwnedGraph certificate allOwned).Walk leftRoot conclusion :=
        leftRootToLeft.trans (.step (.refl left) leftAdjacent)
      have leftRootToRightRoot :
          (referenceOwnedGraph certificate allOwned).Walk leftRoot rightRoot :=
        (leftRootToConclusion.trans
          (.step (.refl conclusion) rightAdjacent.symm)).trans
            rightRootToRight.symm
      refine ⟨leftRoot, leftSubset leftRoot leftRootOwned, ?_⟩
      intro vertex vertexOwned
      change vertex ∈ allOwned at vertexOwned
      simp only [allOwned, List.mem_cons, List.mem_append] at vertexOwned
      rcases vertexOwned with same | inLeft | inRight
      · subst vertex
        exact leftRootToConclusion
      · exact Graph.Walk.mono leftGraphSubset
          (leftConnected vertex inLeft)
      · exact leftRootToRightRoot.trans
          (Graph.Walk.mono rightGraphSubset
            (rightConnected vertex inRight))
  | @exchange premise frontier usedLinks owned premiseWitness
      order reordered reorderEquation induction =>
      exact induction

private theorem referenceOwnedGraph_simpleWalk_subset
    {certificate : Certificate} {owned : List Vertex}
    {start finish : Vertex} {steps : Nat} {visited : List Vertex}
    (walk :
      (referenceOwnedGraph certificate owned).SimpleWalk
        start steps visited finish)
    (startOwned : start ∈ owned) :
    ∀ vertex ∈ visited, vertex ∈ owned := by
  induction walk with
  | refl =>
      intro vertex membership
      simp only [List.mem_singleton] at membership
      subst vertex
      exact startOwned
  | @step priorSteps priorVisited middle current prior adjacency fresh ih =>
      rcases adjacency with ⟨edge, edgeMembership, direction⟩
      have endpointFacts :=
        Bool.and_eq_true_iff.mp (List.mem_filter.mp edgeMembership).2
      have firstOwned : edge.first ∈ owned :=
        List.contains_iff_mem.mp endpointFacts.1
      have secondOwned : edge.second ∈ owned :=
        List.contains_iff_mem.mp endpointFacts.2
      have currentOwned : current ∈ owned := by
        rcases direction with forward | backward
        · rw [forward.2] at secondOwned
          exact secondOwned
        · rw [backward.1] at firstOwned
          exact firstOwned
      intro vertex membership
      simp only [List.mem_append, List.mem_singleton] at membership
      rcases membership with earlier | same
      · exact ih vertex earlier
      · simpa [same] using currentOwned

namespace ComponentOccurrenceWitness

/-- Any two exact occurrences owned by one live component are joined in the
deterministic reference switching by a simple path whose every visited vertex
remains owned by that component. -/
theorem referencePath_within_owned
    {certificate : Certificate} {component : UnificationComponent}
    {usedLinks owned : List Nat}
    (witness :
      ComponentOccurrenceWitness certificate component usedLinks owned)
    {first second : Vertex}
    (firstOwned : first ∈ owned) (secondOwned : second ∈ owned) :
    ∃ path : certificate.referenceSwitchingGraph.EdgeSimplePath,
      path.start = first ∧ path.finish = second ∧
        ∀ vertex ∈ path.vertices, vertex ∈ owned := by
  rcases witness.derivation.referenceRootConnected with
    ⟨root, rootOwned, connected⟩
  have between :
      (referenceOwnedGraph certificate owned).Walk first second :=
    (connected first firstOwned).symm.trans (connected second secondOwned)
  rcases between.toSimple with ⟨steps, visited, simple⟩
  have contained :=
    referenceOwnedGraph_simpleWalk_subset simple firstOwned
  rcases simple.liftToEdgeSimplePath
      (referenceOwnedGraph_edges_subset certificate owned) with
    ⟨path, starts, finishes, vertices⟩
  refine ⟨path, starts, finishes, ?_⟩
  intro vertex membership
  exact contained vertex (by simpa [vertices] using membership)

end ComponentOccurrenceWitness

end Certificate

end ProofNetIR
