import ProofNetIR.NetEquivalence

namespace ProofNetIR

namespace Edge

/-- Translate both endpoints by a fixed offset. -/
def shift (offset : Nat) (edge : Edge) : Edge where
  first := edge.first + offset
  second := edge.second + offset

end Edge

namespace Graph

/-- Append one fresh vertex and connect it to an existing parent. -/
def addLeaf (graph : Graph) (parent : Vertex) : Graph where
  vertexCount := graph.vertexCount + 1
  edges := graph.edges ++ [{ first := parent, second := graph.vertexCount }]

/-- Disjointly place `right` after `left`, append one fresh vertex, and join
the two selected roots to that vertex. This is the graph operation induced by
a tensor link in every switching. -/
def tensorJoin (left right : Graph) (leftRoot rightRoot : Vertex) : Graph where
  vertexCount := left.vertexCount + right.vertexCount + 1
  edges := left.edges ++ right.edges.map (Edge.shift left.vertexCount) ++ [
    { first := leftRoot,
      second := left.vertexCount + right.vertexCount },
    { first := rightRoot + left.vertexCount,
      second := left.vertexCount + right.vertexCount }]

theorem Adjacent.symm {graph : Graph} {left right : Vertex}
    (adjacent : graph.Adjacent left right) : graph.Adjacent right left := by
  rcases adjacent with ⟨edge, membership, direction⟩
  exact ⟨edge, membership, direction.elim Or.inr Or.inl⟩

theorem Adjacent.mono {source target : Graph} {left right : Vertex}
    (subset : ∀ edge ∈ source.edges, edge ∈ target.edges)
    (adjacent : source.Adjacent left right) :
    target.Adjacent left right := by
  rcases adjacent with ⟨edge, membership, direction⟩
  exact ⟨edge, subset edge membership, direction⟩

namespace Walk

theorem mono {source target : Graph} {start finish : Vertex}
    (subset : ∀ edge ∈ source.edges, edge ∈ target.edges)
    (walk : source.Walk start finish) : target.Walk start finish := by
  induction walk with
  | refl => exact .refl _
  | step prior adjacent ih =>
      exact .step ih (adjacent.mono subset)

theorem symm {graph : Graph} {start finish : Vertex}
    (walk : graph.Walk start finish) : graph.Walk finish start := by
  induction walk with
  | refl => exact .refl _
  | @step middle finish prior adjacent ih =>
      exact (Graph.Walk.step (Graph.Walk.refl finish) adjacent.symm).trans ih

end Walk

private theorem leftEdge_mem_tensorJoin (left right : Graph)
    (leftRoot rightRoot : Vertex) {edge : Edge}
    (membership : edge ∈ left.edges) :
    edge ∈ (left.tensorJoin right leftRoot rightRoot).edges := by
  simp [tensorJoin, membership]

private theorem shiftedRightEdge_mem_tensorJoin (left right : Graph)
    (leftRoot rightRoot : Vertex) {edge : Edge}
    (membership : edge ∈ right.edges) :
    Edge.shift left.vertexCount edge ∈
      (left.tensorJoin right leftRoot rightRoot).edges := by
  change Edge.shift left.vertexCount edge ∈
    left.edges ++ right.edges.map (Edge.shift left.vertexCount) ++ _
  exact List.mem_append.mpr (.inl (List.mem_append.mpr (.inr
    (List.mem_map.mpr ⟨edge, membership, rfl⟩))))

private theorem Walk.shiftIntoTensorJoin (left right : Graph)
    (leftRoot rightRoot : Vertex) {start finish : Vertex}
    (walk : right.Walk start finish) :
    (left.tensorJoin right leftRoot rightRoot).Walk
      (start + left.vertexCount) (finish + left.vertexCount) := by
  induction walk with
  | refl => exact .refl _
  | @step middle finish prior adjacent ih =>
      apply Walk.step ih
      rcases adjacent with ⟨edge, membership, direction⟩
      refine ⟨Edge.shift left.vertexCount edge,
        shiftedRightEdge_mem_tensorJoin left right leftRoot rightRoot
          membership, ?_⟩
      rcases direction with direction | direction
      · left
        simp [Edge.shift, direction.1, direction.2]
      · right
        simp [Edge.shift, direction.1, direction.2]

private theorem tensorJoin_leftNew_adjacent (left right : Graph)
    (leftRoot rightRoot : Vertex) :
    (left.tensorJoin right leftRoot rightRoot).Adjacent leftRoot
      (left.vertexCount + right.vertexCount) := by
  refine ⟨Edge.mk leftRoot (left.vertexCount + right.vertexCount), ?_,
        Or.inl ⟨rfl, rfl⟩⟩
  simp [tensorJoin]

private theorem tensorJoin_rightNew_adjacent (left right : Graph)
    (leftRoot rightRoot : Vertex) :
    (left.tensorJoin right leftRoot rightRoot).Adjacent
      (rightRoot + left.vertexCount)
      (left.vertexCount + right.vertexCount) := by
  refine ⟨Edge.mk (rightRoot + left.vertexCount)
      (left.vertexCount + right.vertexCount), ?_,
        Or.inl ⟨rfl, rfl⟩⟩
  simp [tensorJoin]

private theorem addLeaf_parent_adjacent (graph : Graph) (parent : Vertex) :
    (graph.addLeaf parent).Adjacent parent graph.vertexCount := by
  refine ⟨Edge.mk parent graph.vertexCount, ?_, Or.inl ⟨rfl, rfl⟩⟩
  simp [addLeaf]

/-- The tree property is closed under adjoining a fresh leaf. -/
theorem IsTree.addLeaf {graph : Graph} (tree : graph.IsTree)
    {parent : Vertex} (parentInBounds : parent < graph.vertexCount) :
    (graph.addLeaf parent).IsTree := by
  rcases tree with ⟨bounded, connected, edgeCount⟩
  rcases connected with ⟨positive, reaches⟩
  refine ⟨?_, ?_, ?_⟩
  · intro edge membership
    change edge ∈ graph.edges ++
      [Edge.mk parent graph.vertexCount] at membership
    simp only [List.mem_append, List.mem_singleton] at membership
    rcases membership with old | rfl
    · have bounds := bounded edge old
      change edge.first < graph.vertexCount + 1 ∧
        edge.second < graph.vertexCount + 1 ∧ edge.first ≠ edge.second
      exact ⟨Nat.lt_succ_of_lt bounds.1,
        Nat.lt_succ_of_lt bounds.2.1, bounds.2.2⟩
    · change parent < graph.vertexCount + 1 ∧
        graph.vertexCount < graph.vertexCount + 1 ∧
        parent ≠ graph.vertexCount
      exact ⟨Nat.lt_succ_of_lt parentInBounds, Nat.lt_add_one _,
        Nat.ne_of_lt parentInBounds⟩
  · refine ⟨by change 0 < graph.vertexCount + 1; omega, ?_⟩
    intro vertex inBounds
    change vertex < graph.vertexCount + 1 at inBounds
    by_cases old : vertex < graph.vertexCount
    · exact (reaches vertex old).mono (by
        intro edge membership
        change edge ∈ graph.edges ++ [Edge.mk parent graph.vertexCount]
        exact List.mem_append.mpr (.inl membership))
    · have atNew : vertex = graph.vertexCount := by
        omega
      subst vertex
      have toParent : (graph.addLeaf parent).Walk 0 parent :=
        (reaches parent parentInBounds).mono (by
        intro edge membership
        change edge ∈ graph.edges ++ [Edge.mk parent graph.vertexCount]
        exact List.mem_append.mpr (.inl membership))
      exact Graph.Walk.step toParent (addLeaf_parent_adjacent graph parent)
  · change (graph.edges ++ [Edge.mk parent graph.vertexCount]).length + 1 =
      graph.vertexCount + 1
    simp
    omega

/-- The tree property is closed under the graph composition induced by a
tensor link: two disjoint trees plus one fresh degree-two joining vertex. -/
theorem IsTree.tensorJoin {left right : Graph}
    (leftTree : left.IsTree) (rightTree : right.IsTree)
    {leftRoot rightRoot : Vertex}
    (leftRootInBounds : leftRoot < left.vertexCount)
    (rightRootInBounds : rightRoot < right.vertexCount) :
    (left.tensorJoin right leftRoot rightRoot).IsTree := by
  let joined := left.tensorJoin right leftRoot rightRoot
  rcases leftTree with ⟨leftBounded, leftConnected, leftEdgeCount⟩
  rcases leftConnected with ⟨leftPositive, leftReaches⟩
  rcases rightTree with ⟨rightBounded, rightConnected, rightEdgeCount⟩
  rcases rightConnected with ⟨rightPositive, rightReaches⟩
  refine ⟨?_, ?_, ?_⟩
  · intro edge membership
    change edge ∈
      (left.edges ++ right.edges.map (Edge.shift left.vertexCount)) ++ [
        Edge.mk leftRoot (left.vertexCount + right.vertexCount),
        Edge.mk (rightRoot + left.vertexCount)
          (left.vertexCount + right.vertexCount)] at membership
    rw [List.mem_append] at membership
    rcases membership with oldCombined | newEdge
    · rw [List.mem_append] at oldCombined
      rcases oldCombined with oldLeft | shiftedRight
      · rcases leftBounded edge oldLeft with
          ⟨firstBound, secondBound, distinct⟩
        change edge.first < left.vertexCount + right.vertexCount + 1 ∧
          edge.second < left.vertexCount + right.vertexCount + 1 ∧
          edge.first ≠ edge.second
        exact ⟨Nat.lt_trans firstBound (by omega),
          Nat.lt_trans secondBound (by omega), distinct⟩
      · rcases List.mem_map.mp shiftedRight with
          ⟨source, sourceMembership, rfl⟩
        rcases rightBounded source sourceMembership with
          ⟨firstBound, secondBound, distinct⟩
        change source.first + left.vertexCount <
            left.vertexCount + right.vertexCount + 1 ∧
          source.second + left.vertexCount <
            left.vertexCount + right.vertexCount + 1 ∧
          source.first + left.vertexCount ≠
            source.second + left.vertexCount
        have shiftedFirst := Nat.add_lt_add_right firstBound left.vertexCount
        have shiftedSecond := Nat.add_lt_add_right secondBound left.vertexCount
        exact ⟨Nat.lt_trans shiftedFirst (by omega),
          Nat.lt_trans shiftedSecond (by omega), by
            intro same
            exact distinct (Nat.add_right_cancel same)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at newEdge
      rcases newEdge with rfl | rfl
      · change leftRoot < left.vertexCount + right.vertexCount + 1 ∧
          left.vertexCount + right.vertexCount <
            left.vertexCount + right.vertexCount + 1 ∧
          leftRoot ≠ left.vertexCount + right.vertexCount
        have leftBeforeNew : leftRoot <
            left.vertexCount + right.vertexCount :=
          Nat.lt_trans leftRootInBounds (by omega)
        exact ⟨Nat.lt_trans leftRootInBounds (by omega), Nat.lt_succ_self _,
          Nat.ne_of_lt leftBeforeNew⟩
      · change rightRoot + left.vertexCount <
            left.vertexCount + right.vertexCount + 1 ∧
          left.vertexCount + right.vertexCount <
            left.vertexCount + right.vertexCount + 1 ∧
          rightRoot + left.vertexCount ≠
            left.vertexCount + right.vertexCount
        have rightBeforeNew : rightRoot + left.vertexCount <
            left.vertexCount + right.vertexCount := by
          have shifted := Nat.add_lt_add_right rightRootInBounds left.vertexCount
          simpa [Nat.add_comm] using shifted
        exact ⟨Nat.lt_trans rightBeforeNew (Nat.lt_succ_self _),
          Nat.lt_succ_self _,
          Nat.ne_of_lt rightBeforeNew⟩
  · refine ⟨by change 0 < left.vertexCount + right.vertexCount + 1; omega, ?_⟩
    intro vertex inBounds
    change vertex < left.vertexCount + right.vertexCount + 1 at inBounds
    have leftSubset : ∀ edge ∈ left.edges, edge ∈ joined.edges := by
      intro edge membership
      exact leftEdge_mem_tensorJoin left right leftRoot rightRoot membership
    have toLeftRoot : joined.Walk 0 leftRoot :=
      (leftReaches leftRoot leftRootInBounds).mono leftSubset
    have toNew : joined.Walk 0 (left.vertexCount + right.vertexCount) :=
      .step toLeftRoot
        (tensorJoin_leftNew_adjacent left right leftRoot rightRoot)
    by_cases inLeft : vertex < left.vertexCount
    · exact (leftReaches vertex inLeft).mono leftSubset
    · by_cases atNew : vertex = left.vertexCount + right.vertexCount
      · simpa [joined, atNew] using toNew
      · have rightIndexInBounds :
            vertex - left.vertexCount < right.vertexCount := by
          omega
        have vertexEquation :
            vertex - left.vertexCount + left.vertexCount = vertex := by
          omega
        have rightBetween : right.Walk rightRoot
            (vertex - left.vertexCount) :=
          (rightReaches rightRoot rightRootInBounds).symm.trans
            (rightReaches _ rightIndexInBounds)
        have shiftedBetween := rightBetween.shiftIntoTensorJoin
          left right leftRoot rightRoot
        have fromNewToRightRoot : joined.Walk
            (left.vertexCount + right.vertexCount)
            (rightRoot + left.vertexCount) :=
          (Graph.Walk.step (Graph.Walk.refl _)
            (tensorJoin_rightNew_adjacent left right
            leftRoot rightRoot).symm)
        have complete := toNew.trans (fromNewToRightRoot.trans shiftedBetween)
        simpa [joined, vertexEquation] using complete
  · change ((left.edges ++ right.edges.map (Edge.shift left.vertexCount)) ++
      [Edge.mk leftRoot (left.vertexCount + right.vertexCount),
        Edge.mk (rightRoot + left.vertexCount)
          (left.vertexCount + right.vertexCount)]).length + 1 =
        left.vertexCount + right.vertexCount + 1
    simp
    omega

end Graph

end ProofNetIR
