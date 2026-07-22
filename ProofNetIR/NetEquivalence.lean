import ProofNetIR.Serialization

namespace ProofNetIR

namespace Graph

/-- Reordering the stored edge list does not change undirected adjacency. -/
theorem adjacent_iff_of_edges_perm {left right : Graph}
    (permutation : left.edges.Perm right.edges) (first second : Vertex) :
    left.Adjacent first second ↔ right.Adjacent first second := by
  constructor
  · rintro ⟨edge, membership, direction⟩
    exact ⟨edge, permutation.mem_iff.mp membership, direction⟩
  · rintro ⟨edge, membership, direction⟩
    exact ⟨edge, permutation.mem_iff.mpr membership, direction⟩

/-- Walks depend on edge membership, not edge storage order. -/
theorem Walk.permuteEdges {left right : Graph} {start finish : Vertex}
    (walk : left.Walk start finish)
    (permutation : left.edges.Perm right.edges) :
    right.Walk start finish := by
  induction walk with
  | refl => exact .refl _
  | step prior adjacency ih =>
      exact .step ih
        ((adjacent_iff_of_edges_perm permutation _ _).mp adjacency)

/-- The declarative tree property is invariant under edge-list permutation
and transport of the vertex-count equality. -/
theorem IsTree.permuteEdges {left right : Graph}
    (tree : left.IsTree)
    (vertexCount : left.vertexCount = right.vertexCount)
    (permutation : left.edges.Perm right.edges) :
    right.IsTree := by
  refine ⟨?_, ?_, ?_⟩
  · intro edge membership
    have leftMembership : edge ∈ left.edges :=
      permutation.mem_iff.mpr membership
    rcases tree.1 edge leftMembership with ⟨first, second, distinct⟩
    exact ⟨by simpa [vertexCount] using first,
      by simpa [vertexCount] using second, distinct⟩
  · rcases tree.2.1 with ⟨positive, connected⟩
    refine ⟨by simpa [vertexCount] using positive, ?_⟩
    intro vertex inBounds
    have leftInBounds : vertex < left.vertexCount := by
      simpa [vertexCount] using inBounds
    exact (connected vertex leftInBounds).permuteEdges permutation
  · calc
      right.edges.length + 1 = left.edges.length + 1 := by
        rw [permutation.length_eq]
      _ = left.vertexCount := tree.2.2
      _ = right.vertexCount := vertexCount

theorem isTree_iff_of_edgePermutation {left right : Graph}
    (vertexCount : left.vertexCount = right.vertexCount)
    (permutation : left.edges.Perm right.edges) :
    left.IsTree ↔ right.IsTree :=
  ⟨fun tree => tree.permuteEdges vertexCount permutation,
    fun tree => tree.permuteEdges vertexCount.symm permutation.symm⟩

end Graph

namespace Certificate

@[simp] theorem conclusionFormulas?_reindex (certificate : Certificate)
    (r : VertexRenaming certificate.formulas.size) :
    (certificate.reindex r).conclusionFormulas? =
      certificate.conclusionFormulas? := by
  unfold conclusionFormulas?
  rw [reindex_conclusions]
  induction certificate.conclusions with
  | nil => rfl
  | cons head tail ih =>
      simp [certificate.reindex_formula?_forward r, ih]

/-- Equality of proof-net certificates modulo the storage order of links.
Formula occurrences and the ordered conclusion boundary remain literal. -/
structure LinkPermutationEquivalent (left right : Certificate) : Prop where
  formulas : left.formulas = right.formulas
  links : left.links.Perm right.links
  conclusions : left.conclusions = right.conclusions

namespace LinkPermutationEquivalent

/-- Reordering the par-choice list merely reorders the independently selected
edges. Every pointwise choice is preserved. -/
theorem ChoiceSelection.permuteChoices
    {choices reordered : List (Edge × Edge)} {selected : List Edge}
    (selection : ChoiceSelection choices selected)
    (permutation : choices.Perm reordered) :
    ∃ reorderedSelected,
      selected.Perm reorderedSelected ∧
        ChoiceSelection reordered reorderedSelected := by
  induction permutation generalizing selected with
  | nil =>
      cases selection
      exact ⟨[], .nil, .nil⟩
  | cons choice permutation ih =>
      cases selection with
      | left prior =>
          rcases ih prior with
            ⟨reorderedSelected, selectedPermutation, reorderedSelection⟩
          exact ⟨_ :: reorderedSelected,
            selectedPermutation.cons _, .left reorderedSelection⟩
      | right prior =>
          rcases ih prior with
            ⟨reorderedSelected, selectedPermutation, reorderedSelection⟩
          exact ⟨_ :: reorderedSelected,
            selectedPermutation.cons _, .right reorderedSelection⟩
  | swap first second rest =>
      cases selection with
      | left secondSelection =>
          cases secondSelection with
          | left restSelection =>
              exact ⟨_ :: _ :: _, .swap _ _ _,
                .left (.left restSelection)⟩
          | right restSelection =>
              exact ⟨_ :: _ :: _, .swap _ _ _,
                .right (.left restSelection)⟩
      | right secondSelection =>
          cases secondSelection with
          | left restSelection =>
              exact ⟨_ :: _ :: _, .swap _ _ _,
                .left (.right restSelection)⟩
          | right restSelection =>
              exact ⟨_ :: _ :: _, .swap _ _ _,
                .right (.right restSelection)⟩
  | trans first second firstIH secondIH =>
      rcases firstIH selection with
        ⟨middleSelected, firstPermutation, middleSelection⟩
      rcases secondIH middleSelection with
        ⟨reorderedSelected, secondPermutation, reorderedSelection⟩
      exact ⟨reorderedSelected, firstPermutation.trans secondPermutation,
        reorderedSelection⟩

theorem refl (certificate : Certificate) :
    certificate.LinkPermutationEquivalent certificate :=
  ⟨rfl, .refl _, rfl⟩

theorem symm {left right : Certificate}
    (equivalent : left.LinkPermutationEquivalent right) :
    right.LinkPermutationEquivalent left :=
  ⟨equivalent.formulas.symm, equivalent.links.symm,
    equivalent.conclusions.symm⟩

theorem trans {left middle right : Certificate}
    (first : left.LinkPermutationEquivalent middle)
    (second : middle.LinkPermutationEquivalent right) :
    left.LinkPermutationEquivalent right :=
  ⟨first.formulas.trans second.formulas,
    first.links.trans second.links,
    first.conclusions.trans second.conclusions⟩

theorem formula?_eq {left right : Certificate}
    (equivalent : left.LinkPermutationEquivalent right) (vertex : Vertex) :
    left.formula? vertex = right.formula? vertex := by
  simp [formula?, equivalent.formulas]

theorem axiomCount_eq {left right : Certificate}
    (equivalent : left.LinkPermutationEquivalent right) (vertex : Vertex) :
    left.axiomCount vertex = right.axiomCount vertex := by
  exact (equivalent.links.filter
    (·.containsAxiomEndpoint vertex)).length_eq

theorem producerCount_eq {left right : Certificate}
    (equivalent : left.LinkPermutationEquivalent right) (vertex : Vertex) :
    left.producerCount vertex = right.producerCount vertex := by
  exact (equivalent.links.filter (·.produces vertex)).length_eq

theorem parentUseCount_eq {left right : Certificate}
    (equivalent : left.LinkPermutationEquivalent right) (vertex : Vertex) :
    left.parentUseCount vertex = right.parentUseCount vertex := by
  exact (equivalent.links.filter (·.usesAsPremise vertex)).length_eq

theorem conclusionFormulas?_eq {left right : Certificate}
    (equivalent : left.LinkPermutationEquivalent right) :
    left.conclusionFormulas? = right.conclusionFormulas? := by
  unfold conclusionFormulas?
  rw [equivalent.conclusions]
  induction right.conclusions with
  | nil => rfl
  | cons head tail ih =>
      simp [equivalent.formula?_eq, ih]

theorem fixedEdges_perm {left right : Certificate}
    (equivalent : left.LinkPermutationEquivalent right) :
    left.fixedEdges.Perm right.fixedEdges := by
  unfold fixedEdges
  exact equivalent.links.flatMap_right _

theorem parChoices_perm {left right : Certificate}
    (equivalent : left.LinkPermutationEquivalent right) :
    left.parChoices.Perm right.parChoices := by
  unfold parChoices
  exact equivalent.links.filterMap _

theorem linkWellFormed_iff {left right : Certificate}
    (equivalent : left.LinkPermutationEquivalent right) (link : Link) :
    left.LinkWellFormed link ↔ right.LinkWellFormed link := by
  cases link <;>
    simp [LinkWellFormed, equivalent.formulas,
      equivalent.formula?_eq]

theorem nodeWellFormed_iff {left right : Certificate}
    (equivalent : left.LinkPermutationEquivalent right) (vertex : Vertex) :
    left.NodeWellFormed vertex ↔ right.NodeWellFormed vertex := by
  simp [NodeWellFormed, equivalent.formula?_eq,
    equivalent.axiomCount_eq, equivalent.producerCount_eq,
    equivalent.parentUseCount_eq, equivalent.conclusions]

theorem StructurallyWellFormed.permuteLinks {left right : Certificate}
    (wellFormed : left.StructurallyWellFormed)
    (equivalent : left.LinkPermutationEquivalent right) :
    right.StructurallyWellFormed := by
  rcases wellFormed with ⟨formulaPositive, conclusionPositive,
    conclusionsInBounds, conclusionsNodup, linksWellFormed,
    nodesWellFormed⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [equivalent.formulas] using formulaPositive
  · simpa [equivalent.conclusions] using conclusionPositive
  · intro vertex member
    have leftMember : vertex ∈ left.conclusions := by
      simpa [equivalent.conclusions] using member
    simpa [equivalent.formulas] using
      conclusionsInBounds vertex leftMember
  · simpa [equivalent.conclusions] using conclusionsNodup
  · intro link member
    have leftMember : link ∈ left.links :=
      equivalent.links.mem_iff.mpr member
    exact (equivalent.linkWellFormed_iff link).mp
      (linksWellFormed link leftMember)
  · intro vertex inBounds
    have leftInBounds : vertex < left.formulas.size := by
      simpa [equivalent.formulas] using inBounds
    exact (equivalent.nodeWellFormed_iff vertex).mp
      (nodesWellFormed vertex leftInBounds)

theorem structurallyWellFormed_iff {left right : Certificate}
    (equivalent : left.LinkPermutationEquivalent right) :
    left.StructurallyWellFormed ↔ right.StructurallyWellFormed :=
  ⟨fun wellFormed => StructurallyWellFormed.permuteLinks wellFormed equivalent,
    fun wellFormed =>
      StructurallyWellFormed.permuteLinks wellFormed equivalent.symm⟩

/-- Declarative Danos--Regnier correctness is insensitive to link storage
order. The proof explicitly transports every par switching and its tree. -/
theorem DeclarativelyCorrect.permuteLinks {left right : Certificate}
    (correct : left.DeclarativelyCorrect)
    (equivalent : left.LinkPermutationEquivalent right) :
    right.DeclarativelyCorrect := by
  refine ⟨StructurallyWellFormed.permuteLinks correct.1 equivalent, ?_⟩
  intro graph switching
  rcases switching with ⟨rightSelected, rightSelection, rfl⟩
  rcases LinkPermutationEquivalent.ChoiceSelection.permuteChoices
      rightSelection equivalent.parChoices_perm.symm with
    ⟨leftSelected, selectedPermutation, leftSelection⟩
  have leftTree : (left.graphForSelection leftSelected).IsTree :=
    correct.2 _ ⟨leftSelected, leftSelection, rfl⟩
  have vertexCount :
      (left.graphForSelection leftSelected).vertexCount =
        (right.graphForSelection rightSelected).vertexCount := by
    simp [graphForSelection, equivalent.formulas]
  have edgePermutation :
      (left.graphForSelection leftSelected).edges.Perm
        (right.graphForSelection rightSelected).edges := by
    exact equivalent.fixedEdges_perm.append selectedPermutation.symm
  exact leftTree.permuteEdges vertexCount edgePermutation

theorem declarativelyCorrect_iff {left right : Certificate}
    (equivalent : left.LinkPermutationEquivalent right) :
    left.DeclarativelyCorrect ↔ right.DeclarativelyCorrect :=
  ⟨fun correct =>
      LinkPermutationEquivalent.DeclarativelyCorrect.permuteLinks
        correct equivalent,
    fun correct =>
      LinkPermutationEquivalent.DeclarativelyCorrect.permuteLinks
        correct equivalent.symm⟩

theorem check_eq {left right : Certificate}
    (equivalent : left.LinkPermutationEquivalent right) :
    left.check = right.check := by
  apply Bool.eq_iff_iff.mpr
  rw [left.check_iff_declarativelyCorrect,
    right.check_iff_declarativelyCorrect]
  exact equivalent.declarativelyCorrect_iff

theorem correct_iff {left right : Certificate}
    (equivalent : left.LinkPermutationEquivalent right) :
    left.Correct ↔ right.Correct := by
  rw [← left.check_iff_correct, equivalent.check_eq,
    right.check_iff_correct]

/-- Link-permutation equivalence is functorial under the same vertex
renaming.  The source renaming is transported across the proved equality of
formula-array bounds. -/
theorem reindex {left right : Certificate}
    (equivalent : left.LinkPermutationEquivalent right)
    (r : VertexRenaming right.formulas.size) :
    ∃ transported : VertexRenaming left.formulas.size,
      (left.reindex transported).LinkPermutationEquivalent
        (right.reindex r) := by
  have sizeEquation : left.formulas.size = right.formulas.size :=
    congrArg Array.size equivalent.formulas
  let transported : VertexRenaming left.formulas.size :=
    r.changeBound sizeEquation.symm
  refine ⟨transported, ?_⟩
  refine {
    formulas := ?_
    links := ?_
    conclusions := ?_ }
  · apply Array.ext
    · simpa using sizeEquation
    · intro index leftInBounds rightInBounds
      simp [Certificate.reindex, transported, equivalent.formulas]
  · change
      (left.links.map (Link.reindex transported)).Perm
        (right.links.map (Link.reindex r))
    have reindexFunction : Link.reindex transported = Link.reindex r := by
      funext link
      cases link <;> simp [Link.reindex, transported]
    rw [reindexFunction]
    exact equivalent.links.map (Link.reindex r)
  · change
      left.conclusions.map transported.forward =
        right.conclusions.map r.forward
    simpa [transported, equivalent.conclusions]

end LinkPermutationEquivalent

theorem linkPermutationEquivalent_equivalence :
    Equivalence LinkPermutationEquivalent :=
  ⟨LinkPermutationEquivalent.refl, LinkPermutationEquivalent.symm,
    LinkPermutationEquivalent.trans⟩

/-- A flattened witness for the equivalence generated by renaming and link
permutation.  It states that one composite bounded vertex map followed by one
link permutation suffices. -/
def DirectProofNetEquivalent (left right : Certificate) : Prop :=
  ∃ vertexMap : VertexRenaming left.formulas.size,
    (left.reindex vertexMap).LinkPermutationEquivalent right

namespace DirectProofNetEquivalent

theorem refl (certificate : Certificate) :
    certificate.DirectProofNetEquivalent certificate := by
  refine ⟨VertexRenaming.refl certificate.formulas.size, ?_⟩
  simpa using LinkPermutationEquivalent.refl certificate

theorem ofReindexEquivalent {left right : Certificate}
    (equivalent : left.ReindexEquivalent right) :
    left.DirectProofNetEquivalent right := by
  rcases equivalent with ⟨vertexMap, rfl⟩
  exact ⟨vertexMap, LinkPermutationEquivalent.refl _⟩

theorem ofLinkPermutationEquivalent {left right : Certificate}
    (equivalent : left.LinkPermutationEquivalent right) :
    left.DirectProofNetEquivalent right := by
  refine ⟨VertexRenaming.refl left.formulas.size, ?_⟩
  simpa using equivalent

theorem trans {left middle right : Certificate}
    (first : left.DirectProofNetEquivalent middle)
    (second : middle.DirectProofNetEquivalent right) :
    left.DirectProofNetEquivalent right := by
  rcases first with ⟨firstMap, firstPermutation⟩
  rcases second with ⟨secondMap, secondPermutation⟩
  rcases firstPermutation.reindex secondMap with
    ⟨transported, transportedEquivalent⟩
  let combined := firstMap.trans
    (left.alignNextRenaming firstMap transported)
  refine ⟨combined, ?_⟩
  have chained := transportedEquivalent.trans secondPermutation
  simpa [combined] using chained

theorem symm {left right : Certificate}
    (direct : left.DirectProofNetEquivalent right) :
    right.DirectProofNetEquivalent left := by
  rcases direct with ⟨vertexMap, linkPermutation⟩
  have reversed := linkPermutation.symm
  rcases reversed.reindex (left.inverseReindexing vertexMap) with
    ⟨transported, transportedEquivalent⟩
  refine ⟨transported, ?_⟩
  rw [left.reindex_inverse vertexMap] at transportedEquivalent
  exact transportedEquivalent

end DirectProofNetEquivalent

/-- The equivalence generated by bounded vertex renaming and semantically
irrelevant link-list permutation. This is the minimum relation suitable for a
general sequentialization theorem, because desequentialization emits links in
rule-tree postorder while the checker accepts any storage order. -/
inductive ProofNetEquivalent : Certificate → Certificate → Prop where
  | reindex {left right} : left.ReindexEquivalent right →
      ProofNetEquivalent left right
  | permuteLinks {left right} : left.LinkPermutationEquivalent right →
      ProofNetEquivalent left right
  | refl (certificate) : ProofNetEquivalent certificate certificate
  | symm {left right} : ProofNetEquivalent left right →
      ProofNetEquivalent right left
  | trans {left middle right} : ProofNetEquivalent left middle →
      ProofNetEquivalent middle right → ProofNetEquivalent left right

/-- The generated equivalence has no hidden extra cases: every proof flattens
to one bounded vertex renaming followed by one link permutation. -/
theorem ProofNetEquivalent.toDirect {left right : Certificate}
    (equivalent : left.ProofNetEquivalent right) :
    left.DirectProofNetEquivalent right := by
  induction equivalent with
  | reindex relation =>
      exact DirectProofNetEquivalent.ofReindexEquivalent relation
  | permuteLinks relation =>
      exact DirectProofNetEquivalent.ofLinkPermutationEquivalent relation
  | refl certificate => exact DirectProofNetEquivalent.refl certificate
  | symm _ ih => exact ih.symm
  | trans _ _ firstIH secondIH => exact firstIH.trans secondIH

theorem DirectProofNetEquivalent.toProofNetEquivalent
    {left right : Certificate}
    (equivalent : left.DirectProofNetEquivalent right) :
    left.ProofNetEquivalent right := by
  rcases equivalent with ⟨vertexMap, linkPermutation⟩
  exact .trans (.reindex ⟨vertexMap, rfl⟩)
    (.permuteLinks linkPermutation)

theorem proofNetEquivalent_iff_direct {left right : Certificate} :
    left.ProofNetEquivalent right ↔ left.DirectProofNetEquivalent right :=
  ⟨ProofNetEquivalent.toDirect,
    DirectProofNetEquivalent.toProofNetEquivalent⟩

theorem proofNetEquivalent_equivalence : Equivalence ProofNetEquivalent :=
  ⟨ProofNetEquivalent.refl, ProofNetEquivalent.symm,
    ProofNetEquivalent.trans⟩

theorem ReindexEquivalent.toProofNetEquivalent {left right : Certificate}
    (equivalent : left.ReindexEquivalent right) :
    left.ProofNetEquivalent right :=
  .reindex equivalent

theorem ReindexEquivalent.conclusionFormulas?_eq
    {left right : Certificate}
    (equivalent : left.ReindexEquivalent right) :
    left.conclusionFormulas? = right.conclusionFormulas? := by
  rcases equivalent with ⟨r, rfl⟩
  exact (left.conclusionFormulas?_reindex r).symm

theorem LinkPermutationEquivalent.toProofNetEquivalent
    {left right : Certificate}
    (equivalent : left.LinkPermutationEquivalent right) :
    left.ProofNetEquivalent right :=
  .permuteLinks equivalent

namespace ProofNetEquivalent

theorem check_eq {left right : Certificate}
    (equivalent : left.ProofNetEquivalent right) :
    left.check = right.check := by
  induction equivalent with
  | reindex equivalent => exact equivalent.check_eq
  | permuteLinks equivalent => exact equivalent.check_eq
  | refl => rfl
  | symm equivalent ih => exact ih.symm
  | trans first second firstIH secondIH => exact firstIH.trans secondIH

theorem declarativelyCorrect_iff {left right : Certificate}
    (equivalent : left.ProofNetEquivalent right) :
    left.DeclarativelyCorrect ↔ right.DeclarativelyCorrect := by
  rw [← left.check_iff_declarativelyCorrect, equivalent.check_eq,
    right.check_iff_declarativelyCorrect]

theorem correct_iff {left right : Certificate}
    (equivalent : left.ProofNetEquivalent right) :
    left.Correct ↔ right.Correct := by
  rw [← left.check_iff_correct, equivalent.check_eq,
    right.check_iff_correct]

theorem conclusionFormulas?_eq {left right : Certificate}
    (equivalent : left.ProofNetEquivalent right) :
    left.conclusionFormulas? = right.conclusionFormulas? := by
  induction equivalent with
  | reindex equivalent => exact equivalent.conclusionFormulas?_eq
  | permuteLinks equivalent => exact equivalent.conclusionFormulas?_eq
  | refl => rfl
  | symm equivalent ih => exact ih.symm
  | trans first second firstIH secondIH => exact firstIH.trans secondIH

end ProofNetEquivalent

end Certificate

end ProofNetIR
