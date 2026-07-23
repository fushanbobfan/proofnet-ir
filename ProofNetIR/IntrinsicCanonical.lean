import ProofNetIR.ProofNetCanonical

namespace ProofNetIR

/-!
# Intrinsic, non-factorial proof-net normalization

The v0.7 exact key is a specification oracle: it enumerates every link-list
permutation and minimizes the resulting complete family.  This module begins
the replacement construction.  It discovers formula occurrences from the
ordered conclusion boundary, follows the unique connective producer in
left/right premise order, and emits each link at its orientation-sensitive
owner:

* an axiom link is owned by its stored left endpoint;
* a tensor or par link is owned by its conclusion.

The construction is polynomial (the current direct implementation scans the
link list for each visited occurrence) and never enumerates a permutation.
The first group of theorems proves unconditional invariance under bounded
vertex reindexing and literal link-list permutation.  The later coverage,
permutation, and representative theorems prove completeness on the
structurally well-formed domain.  `IntrinsicCanonicalKeyWire.lean` exposes the
result through a new, versioned wire contract.
-/

namespace ExactOne

/-- Return the element of an exact singleton and reject zero or multiple
matches.  Unlike `List.find?`, this selector is invariant under permutation
without an ordering assumption on the element type. -/
def select? : List α → Option α
  | [value] => some value
  | _ => none

theorem select?_eq_of_perm {left right : List α}
    (permutation : left.Perm right) :
    select? left = select? right := by
  induction permutation with
  | nil => rfl
  | @cons value left right permutation ih =>
      cases left with
      | nil =>
          have : right = [] := by
            simpa using permutation
          subst right
          rfl
      | cons leftHead leftTail =>
          cases right with
          | nil => simp at permutation
          | cons rightHead rightTail => rfl
  | swap first second rest =>
      rfl
  | trans first second ihFirst ihSecond =>
      exact ihFirst.trans ihSecond

@[simp] theorem select?_map (mapValue : α → β) (values : List α) :
    select? (values.map mapValue) = (select? values).map mapValue := by
  cases values with
  | nil => rfl
  | cons head tail =>
      cases tail <;> rfl

theorem select?_eq_some_of_mem_of_length_eq_one
    {values : List α} {value : α}
    (member : value ∈ values) (length : values.length = 1) :
    select? values = some value := by
  rcases List.length_eq_one_iff.mp length with ⟨only, rfl⟩
  simp at member
  subst only
  rfl

theorem mem_of_select?_eq_some {values : List α} {value : α}
    (equation : select? values = some value) :
    value ∈ values := by
  cases values with
  | nil => simp [select?] at equation
  | cons head tail =>
      cases tail with
      | nil =>
          simp [select?] at equation
          subst head
          simp
      | cons second rest =>
          simp [select?] at equation

end ExactOne

namespace Link

/-- Orientation-sensitive owner used to emit every link once.  In particular,
an axiom with reversed endpoints has a different owner and remains distinct,
as required by `ProofNetEquivalent`. -/
def ownedBy (vertex : Vertex) : Link → Bool
  | .axiom left _ => left == vertex
  | .tensor _ _ conclusion => conclusion == vertex
  | .par _ _ conclusion => conclusion == vertex

/-- The unique orientation-sensitive owner selected by `ownedBy`. -/
def owner : Link → Vertex
  | .axiom left _ => left
  | .tensor _ _ conclusion => conclusion
  | .par _ _ conclusion => conclusion

@[simp] theorem ownedBy_owner (link : Link) :
    link.ownedBy link.owner = true := by
  cases link <;> simp [ownedBy, owner]

theorem ownedBy_eq_true_iff_owner_eq (link : Link) (vertex : Vertex) :
    link.ownedBy vertex = true ↔ link.owner = vertex := by
  cases link <;> simp [ownedBy, owner]

theorem owner_mem_vertices (link : Link) :
    link.owner ∈ link.vertices := by
  cases link <;> simp [owner, vertices]

@[simp] theorem ownedBy_reindex {bound : Nat}
    (r : VertexRenaming bound) (vertex : Vertex) (link : Link) :
    (link.reindex r).ownedBy (r.forward vertex) = link.ownedBy vertex := by
  cases link <;> simp [ownedBy, reindex, r.forward_beq]

/-- Relabeling a reindexed link by first occurrence in the correspondingly
reindexed order erases the submitted vertex names. -/
theorem relabel_reindex_idxOf_map_forward {bound : Nat}
    (r : VertexRenaming bound) (order : List Vertex) (link : Link) :
    (link.reindex r).relabel
        (fun vertex => (order.map r.forward).idxOf vertex) =
      link.relabel (fun vertex => order.idxOf vertex) := by
  cases link <;>
    simp [relabel, reindex, r.idxOf_map_forward]

end Link

namespace Certificate

/-- The unique connective link producing an occurrence, when there is exactly
one.  Malformed zero- and multiple-producer inputs fail closed. -/
def uniqueProducer? (certificate : Certificate) (vertex : Vertex) :
    Option Link :=
  ExactOne.select? (certificate.links.filter (·.produces vertex))

/-- The unique link owned by an occurrence, when there is exactly one.
Right-hand axiom endpoints intentionally own no link. -/
def uniqueOwnedLink? (certificate : Certificate) (vertex : Vertex) :
    Option Link :=
  ExactOne.select? (certificate.links.filter (·.ownedBy vertex))

theorem uniqueProducer?_eq_some_of_count
    {certificate : Certificate} {vertex : Vertex} {link : Link}
    (count : certificate.producerCount vertex = 1)
    (membership : link ∈ certificate.links)
    (produces : link.produces vertex = true) :
    certificate.uniqueProducer? vertex = some link := by
  unfold producerCount at count
  unfold uniqueProducer?
  apply ExactOne.select?_eq_some_of_mem_of_length_eq_one
  · exact List.mem_filter.mpr ⟨membership, produces⟩
  · exact count

theorem uniqueOwnedLink?_eq_some_of_count
    {certificate : Certificate} {vertex : Vertex} {link : Link}
    (count :
      (certificate.links.filter (·.ownedBy vertex)).length = 1)
    (membership : link ∈ certificate.links)
    (owned : link.ownedBy vertex = true) :
    certificate.uniqueOwnedLink? vertex = some link := by
  unfold uniqueOwnedLink?
  apply ExactOne.select?_eq_some_of_mem_of_length_eq_one
  · exact List.mem_filter.mpr ⟨membership, owned⟩
  · exact count

theorem LinkPermutationEquivalent.uniqueProducer?_eq
    {left right : Certificate}
    (equivalent : left.LinkPermutationEquivalent right)
    (vertex : Vertex) :
    left.uniqueProducer? vertex = right.uniqueProducer? vertex := by
  unfold uniqueProducer?
  exact ExactOne.select?_eq_of_perm
    (equivalent.links.filter (·.produces vertex))

theorem LinkPermutationEquivalent.uniqueOwnedLink?_eq
    {left right : Certificate}
    (equivalent : left.LinkPermutationEquivalent right)
    (vertex : Vertex) :
    left.uniqueOwnedLink? vertex = right.uniqueOwnedLink? vertex := by
  unfold uniqueOwnedLink?
  exact ExactOne.select?_eq_of_perm
    (equivalent.links.filter (·.ownedBy vertex))

private theorem producerFilter_reindex (certificate : Certificate)
    (r : VertexRenaming certificate.formulas.size) (vertex : Vertex) :
    (certificate.reindex r).links.filter
        (·.produces (r.forward vertex)) =
      (certificate.links.filter (·.produces vertex)).map
        (Link.reindex r) := by
  simp only [reindex_links]
  induction certificate.links with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.map_cons, List.filter_cons,
        Link.produces_reindex]
      cases equation : head.produces vertex <;>
        simp [ih]

private theorem ownedLinkFilter_reindex (certificate : Certificate)
    (r : VertexRenaming certificate.formulas.size) (vertex : Vertex) :
    (certificate.reindex r).links.filter
        (·.ownedBy (r.forward vertex)) =
      (certificate.links.filter (·.ownedBy vertex)).map
        (Link.reindex r) := by
  simp only [reindex_links]
  induction certificate.links with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.map_cons, List.filter_cons,
        Link.ownedBy_reindex]
      cases equation : head.ownedBy vertex <;>
        simp [ih]

@[simp] theorem uniqueProducer?_reindex (certificate : Certificate)
    (r : VertexRenaming certificate.formulas.size) (vertex : Vertex) :
    (certificate.reindex r).uniqueProducer? (r.forward vertex) =
      (certificate.uniqueProducer? vertex).map (Link.reindex r) := by
  unfold uniqueProducer?
  rw [certificate.producerFilter_reindex r vertex,
    ExactOne.select?_map]

@[simp] theorem uniqueOwnedLink?_reindex (certificate : Certificate)
    (r : VertexRenaming certificate.formulas.size) (vertex : Vertex) :
    (certificate.reindex r).uniqueOwnedLink? (r.forward vertex) =
      (certificate.uniqueOwnedLink? vertex).map (Link.reindex r) := by
  unfold uniqueOwnedLink?
  rw [certificate.ownedLinkFilter_reindex r vertex,
    ExactOne.select?_map]

/-- Preorder walk of one formula occurrence.  The recursion follows the
formula syntax, so termination is structural rather than fuel-based. -/
def occurrenceWalk (certificate : Certificate) (vertex : Vertex) :
    Formula → List Vertex
  | .atom _ _ => [vertex]
  | .tensor leftFormula rightFormula =>
      match certificate.uniqueProducer? vertex with
      | some (.tensor left right _) =>
          vertex ::
            (certificate.occurrenceWalk left leftFormula ++
              certificate.occurrenceWalk right rightFormula)
      | _ => [vertex]
  | .par leftFormula rightFormula =>
      match certificate.uniqueProducer? vertex with
      | some (.par left right _) =>
          vertex ::
            (certificate.occurrenceWalk left leftFormula ++
              certificate.occurrenceWalk right rightFormula)
      | _ => [vertex]

/-- Discover one occurrence tree from the formula label stored at its root. -/
def occurrenceWalk? (certificate : Certificate) (vertex : Vertex) :
    List Vertex :=
  match certificate.formula? vertex with
  | some formula => certificate.occurrenceWalk vertex formula
  | none => [vertex]

theorem occurrenceWalk_root_mem (certificate : Certificate)
    (vertex : Vertex) (formula : Formula) :
    vertex ∈ certificate.occurrenceWalk vertex formula := by
  cases formula with
  | atom name positive => simp [occurrenceWalk]
  | tensor left right =>
      cases equation : certificate.uniqueProducer? vertex with
      | none => simp [occurrenceWalk, equation]
      | some link =>
          cases link <;> simp [occurrenceWalk, equation]
  | par left right =>
      cases equation : certificate.uniqueProducer? vertex with
      | none => simp [occurrenceWalk, equation]
      | some link =>
          cases link <;> simp [occurrenceWalk, equation]

theorem occurrenceWalk?_root_mem (certificate : Certificate)
    (vertex : Vertex) :
    vertex ∈ certificate.occurrenceWalk? vertex := by
  unfold occurrenceWalk?
  cases certificate.formula? vertex with
  | none => simp
  | some formula =>
      exact certificate.occurrenceWalk_root_mem vertex formula

theorem StructurallyWellFormed.uniqueTensorProducerData
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {vertex : Vertex} {leftFormula rightFormula : Formula}
    (inBounds : vertex < certificate.formulas.size)
    (formulaEquation :
      certificate.formula? vertex =
        some (.tensor leftFormula rightFormula)) :
    ∃ left right,
      certificate.uniqueProducer? vertex =
        some (.tensor left right vertex) ∧
      certificate.formula? left = some leftFormula ∧
      certificate.formula? right = some rightFormula := by
  have node := structural.2.2.2.2.2 vertex inBounds
  have count : certificate.producerCount vertex = 1 := by
    simpa [NodeWellFormed, formulaEquation] using node.1
  unfold producerCount at count
  rcases List.length_eq_one_iff.mp count with
    ⟨producer, producerFilter⟩
  have filtered : producer ∈
      certificate.links.filter (·.produces vertex) := by
    rw [producerFilter]
    simp
  rcases List.mem_filter.mp filtered with
    ⟨producerMember, produces⟩
  have selected :=
    uniqueProducer?_eq_some_of_count
      (certificate := certificate) count producerMember produces
  have producerWellFormed :=
    structural.2.2.2.2.1 producer producerMember
  cases producer with
  | «axiom» first second =>
      simp [Link.produces] at produces
  | tensor left right conclusion =>
      have conclusionEq : conclusion = vertex := by
        simpa [Link.produces] using produces
      subst conclusion
      rcases producerWellFormed.tensor_formulaData with
        ⟨actualLeft, actualRight, leftEquation, rightEquation,
          conclusionEquation⟩
      have formulaEquality :
          Formula.tensor actualLeft actualRight =
            Formula.tensor leftFormula rightFormula := by
        exact Option.some.inj
          (conclusionEquation.symm.trans formulaEquation)
      injection formulaEquality with leftSame rightSame
      subst actualLeft
      subst actualRight
      exact ⟨left, right, selected, leftEquation, rightEquation⟩
  | par left right conclusion =>
      have conclusionEq : conclusion = vertex := by
        simpa [Link.produces] using produces
      subst conclusion
      rcases producerWellFormed.par_formulaData with
        ⟨actualLeft, actualRight, _leftEquation, _rightEquation,
          conclusionEquation⟩
      have impossible :
          Formula.par actualLeft actualRight =
            Formula.tensor leftFormula rightFormula := by
        exact Option.some.inj
          (conclusionEquation.symm.trans formulaEquation)
      cases impossible

theorem StructurallyWellFormed.uniqueParProducerData
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {vertex : Vertex} {leftFormula rightFormula : Formula}
    (inBounds : vertex < certificate.formulas.size)
    (formulaEquation :
      certificate.formula? vertex =
        some (.par leftFormula rightFormula)) :
    ∃ left right,
      certificate.uniqueProducer? vertex =
        some (.par left right vertex) ∧
      certificate.formula? left = some leftFormula ∧
      certificate.formula? right = some rightFormula := by
  have node := structural.2.2.2.2.2 vertex inBounds
  have count : certificate.producerCount vertex = 1 := by
    simpa [NodeWellFormed, formulaEquation] using node.1
  unfold producerCount at count
  rcases List.length_eq_one_iff.mp count with
    ⟨producer, producerFilter⟩
  have filtered : producer ∈
      certificate.links.filter (·.produces vertex) := by
    rw [producerFilter]
    simp
  rcases List.mem_filter.mp filtered with
    ⟨producerMember, produces⟩
  have selected :=
    uniqueProducer?_eq_some_of_count
      (certificate := certificate) count producerMember produces
  have producerWellFormed :=
    structural.2.2.2.2.1 producer producerMember
  cases producer with
  | «axiom» first second =>
      simp [Link.produces] at produces
  | tensor left right conclusion =>
      have conclusionEq : conclusion = vertex := by
        simpa [Link.produces] using produces
      subst conclusion
      rcases producerWellFormed.tensor_formulaData with
        ⟨actualLeft, actualRight, _leftEquation, _rightEquation,
          conclusionEquation⟩
      have impossible :
          Formula.tensor actualLeft actualRight =
            Formula.par leftFormula rightFormula := by
        exact Option.some.inj
          (conclusionEquation.symm.trans formulaEquation)
      cases impossible
  | par left right conclusion =>
      have conclusionEq : conclusion = vertex := by
        simpa [Link.produces] using produces
      subst conclusion
      rcases producerWellFormed.par_formulaData with
        ⟨actualLeft, actualRight, leftEquation, rightEquation,
          conclusionEquation⟩
      have formulaEquality :
          Formula.par actualLeft actualRight =
            Formula.par leftFormula rightFormula := by
        exact Option.some.inj
          (conclusionEquation.symm.trans formulaEquation)
      injection formulaEquality with leftSame rightSame
      subst actualLeft
      subst actualRight
      exact ⟨left, right, selected, leftEquation, rightEquation⟩

theorem inBounds_of_formula?_eq_some
    {certificate : Certificate} {vertex : Vertex} {formula : Formula}
    (equation : certificate.formula? vertex = some formula) :
    vertex < certificate.formulas.size := by
  unfold formula? at equation
  exact (Array.getElem?_eq_some_iff.mp equation).choose

/-- Every producer premise below a vertex already discovered by a well-formed
occurrence walk is discovered by that same walk.  This is the local closure
lemma needed to lift boundary roots to complete occurrence coverage. -/
theorem StructurallyWellFormed.occurrenceWalk_closed_under_premises
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {root : Vertex} {formula : Formula}
    (rootInBounds : root < certificate.formulas.size)
    (rootFormula : certificate.formula? root = some formula)
    {produced premise : Vertex} {link : Link}
    (linkMember : link ∈ certificate.links)
    (produces : link.produces produced = true)
    (premiseMember : premise ∈ link.premises)
    (producedMember :
      produced ∈ certificate.occurrenceWalk root formula) :
    premise ∈ certificate.occurrenceWalk root formula := by
  induction formula generalizing root produced premise link with
  | atom name positive =>
      simp only [occurrenceWalk, List.mem_singleton] at producedMember
      subst produced
      have linkWellFormed :=
        structural.2.2.2.2.1 link linkMember
      cases link with
      | «axiom» left right =>
          simp [Link.produces] at produces
      | tensor left right conclusion =>
          have conclusionEq : conclusion = root := by
            simpa [Link.produces] using produces
          subst conclusion
          rcases linkWellFormed.tensor_formulaData with
            ⟨leftFormula, rightFormula, _leftEquation, _rightEquation,
              conclusionEquation⟩
          have impossible :
              Formula.tensor leftFormula rightFormula =
                Formula.atom name positive := by
            exact Option.some.inj
              (conclusionEquation.symm.trans rootFormula)
          cases impossible
      | par left right conclusion =>
          have conclusionEq : conclusion = root := by
            simpa [Link.produces] using produces
          subst conclusion
          rcases linkWellFormed.par_formulaData with
            ⟨leftFormula, rightFormula, _leftEquation, _rightEquation,
              conclusionEquation⟩
          have impossible :
              Formula.par leftFormula rightFormula =
                Formula.atom name positive := by
            exact Option.some.inj
              (conclusionEquation.symm.trans rootFormula)
          cases impossible
  | tensor leftFormula rightFormula leftIH rightIH =>
      rcases structural.uniqueTensorProducerData rootInBounds rootFormula with
        ⟨left, right, selected, leftFormulaAt, rightFormulaAt⟩
      rw [occurrenceWalk, selected] at producedMember
      simp only [List.mem_cons, List.mem_append] at producedMember
      rcases producedMember with atRoot | inLeft | inRight
      · subst produced
        have rootNode := structural.2.2.2.2.2 root rootInBounds
        have count : certificate.producerCount root = 1 := by
          simpa [NodeWellFormed, rootFormula] using rootNode.1
        have actualSelected :=
          uniqueProducer?_eq_some_of_count
            (certificate := certificate) count linkMember produces
        have linkEq : link = .tensor left right root := by
          exact Option.some.inj (actualSelected.symm.trans selected)
        subst link
        simp [Link.premises] at premiseMember
        rcases premiseMember with rfl | rfl
        · rw [occurrenceWalk, selected]
          simp [certificate.occurrenceWalk_root_mem]
        · rw [occurrenceWalk, selected]
          simp [certificate.occurrenceWalk_root_mem]
      · have premiseInLeft :=
          leftIH
            (inBounds_of_formula?_eq_some leftFormulaAt)
            leftFormulaAt linkMember produces premiseMember inLeft
        simp only [occurrenceWalk, selected, List.mem_cons, List.mem_append]
        exact Or.inr (Or.inl premiseInLeft)
      · have premiseInRight :=
          rightIH
            (inBounds_of_formula?_eq_some rightFormulaAt)
            rightFormulaAt linkMember produces premiseMember inRight
        simp only [occurrenceWalk, selected, List.mem_cons, List.mem_append]
        exact Or.inr (Or.inr premiseInRight)
  | par leftFormula rightFormula leftIH rightIH =>
      rcases structural.uniqueParProducerData rootInBounds rootFormula with
        ⟨left, right, selected, leftFormulaAt, rightFormulaAt⟩
      rw [occurrenceWalk, selected] at producedMember
      simp only [List.mem_cons, List.mem_append] at producedMember
      rcases producedMember with atRoot | inLeft | inRight
      · subst produced
        have rootNode := structural.2.2.2.2.2 root rootInBounds
        have count : certificate.producerCount root = 1 := by
          simpa [NodeWellFormed, rootFormula] using rootNode.1
        have actualSelected :=
          uniqueProducer?_eq_some_of_count
            (certificate := certificate) count linkMember produces
        have linkEq : link = .par left right root := by
          exact Option.some.inj (actualSelected.symm.trans selected)
        subst link
        simp [Link.premises] at premiseMember
        rcases premiseMember with rfl | rfl
        · rw [occurrenceWalk, selected]
          simp [certificate.occurrenceWalk_root_mem]
        · rw [occurrenceWalk, selected]
          simp [certificate.occurrenceWalk_root_mem]
      · have premiseInLeft :=
          leftIH
            (inBounds_of_formula?_eq_some leftFormulaAt)
            leftFormulaAt linkMember produces premiseMember inLeft
        simp only [occurrenceWalk, selected, List.mem_cons, List.mem_append]
        exact Or.inr (Or.inl premiseInLeft)
      · have premiseInRight :=
          rightIH
            (inBounds_of_formula?_eq_some rightFormulaAt)
            rightFormulaAt linkMember produces premiseMember inRight
        simp only [occurrenceWalk, selected, List.mem_cons, List.mem_append]
        exact Or.inr (Or.inr premiseInRight)

@[simp] theorem occurrenceWalk_reindex (certificate : Certificate)
    (r : VertexRenaming certificate.formulas.size)
    (vertex : Vertex) (formula : Formula) :
    (certificate.reindex r).occurrenceWalk (r.forward vertex) formula =
      (certificate.occurrenceWalk vertex formula).map r.forward := by
  induction formula generalizing vertex with
  | atom name positive =>
      rfl
  | tensor leftFormula rightFormula leftIH rightIH =>
      rw [occurrenceWalk, certificate.uniqueProducer?_reindex]
      cases equation : certificate.uniqueProducer? vertex with
      | none =>
          simp [equation, occurrenceWalk]
      | some link =>
          cases link <;>
            simp [equation, occurrenceWalk, Link.reindex, leftIH, rightIH]
  | par leftFormula rightFormula leftIH rightIH =>
      rw [occurrenceWalk, certificate.uniqueProducer?_reindex]
      cases equation : certificate.uniqueProducer? vertex with
      | none =>
          simp [equation, occurrenceWalk]
      | some link =>
          cases link <;>
            simp [equation, occurrenceWalk, Link.reindex, leftIH, rightIH]

@[simp] theorem occurrenceWalk?_reindex (certificate : Certificate)
    (r : VertexRenaming certificate.formulas.size) (vertex : Vertex) :
    (certificate.reindex r).occurrenceWalk? (r.forward vertex) =
      (certificate.occurrenceWalk? vertex).map r.forward := by
  unfold occurrenceWalk?
  rw [certificate.reindex_formula?_forward r vertex]
  cases certificate.formula? vertex <;>
    simp

theorem LinkPermutationEquivalent.occurrenceWalk_eq
    {left right : Certificate}
    (equivalent : left.LinkPermutationEquivalent right)
    (vertex : Vertex) (formula : Formula) :
    left.occurrenceWalk vertex formula =
      right.occurrenceWalk vertex formula := by
  induction formula generalizing vertex with
  | atom name positive =>
      rfl
  | tensor leftFormula rightFormula leftIH rightIH =>
      rw [occurrenceWalk, occurrenceWalk,
        equivalent.uniqueProducer?_eq vertex]
      cases right.uniqueProducer? vertex with
      | none => rfl
      | some link =>
        cases link <;>
          simp [leftIH, rightIH]
  | par leftFormula rightFormula leftIH rightIH =>
      rw [occurrenceWalk, occurrenceWalk,
        equivalent.uniqueProducer?_eq vertex]
      cases right.uniqueProducer? vertex with
      | none => rfl
      | some link =>
        cases link <;>
          simp [leftIH, rightIH]

theorem LinkPermutationEquivalent.occurrenceWalk?_eq
    {left right : Certificate}
    (equivalent : left.LinkPermutationEquivalent right)
    (vertex : Vertex) :
    left.occurrenceWalk? vertex = right.occurrenceWalk? vertex := by
  unfold occurrenceWalk?
  rw [equivalent.formula?_eq vertex]
  cases right.formula? vertex with
  | none => rfl
  | some formula =>
      exact equivalent.occurrenceWalk_eq vertex formula

/-- Raw ordered formula-forest traversal from the ordered conclusions. -/
def intrinsicTraversalRaw (certificate : Certificate) : List Vertex :=
  certificate.conclusions.flatMap certificate.occurrenceWalk?

/-- Deduplicated intrinsic occurrence order.  Deduplication only affects
malformed inputs; the structural completeness theorem establishes exact
coverage on the supported domain. -/
def intrinsicTraversalVertices (certificate : Certificate) : List Vertex :=
  certificate.intrinsicTraversalRaw.eraseDups

@[simp] theorem intrinsicTraversalRaw_reindex (certificate : Certificate)
    (r : VertexRenaming certificate.formulas.size) :
    (certificate.reindex r).intrinsicTraversalRaw =
      certificate.intrinsicTraversalRaw.map r.forward := by
  unfold intrinsicTraversalRaw
  simp only [reindex_conclusions, List.flatMap_map]
  induction certificate.conclusions with
  | nil => rfl
  | cons head tail ih =>
      rw [List.flatMap_cons, List.flatMap_cons,
        certificate.occurrenceWalk?_reindex r, ih, List.map_append]

@[simp] theorem intrinsicTraversalVertices_reindex
    (certificate : Certificate)
    (r : VertexRenaming certificate.formulas.size) :
    (certificate.reindex r).intrinsicTraversalVertices =
      certificate.intrinsicTraversalVertices.map r.forward := by
  simp [intrinsicTraversalVertices]

theorem LinkPermutationEquivalent.intrinsicTraversalRaw_eq
    {left right : Certificate}
    (equivalent : left.LinkPermutationEquivalent right) :
    left.intrinsicTraversalRaw = right.intrinsicTraversalRaw := by
  unfold intrinsicTraversalRaw
  rw [equivalent.conclusions]
  induction right.conclusions with
  | nil => rfl
  | cons head tail ih =>
      rw [List.flatMap_cons, List.flatMap_cons,
        equivalent.occurrenceWalk?_eq head, ih]

theorem LinkPermutationEquivalent.intrinsicTraversalVertices_eq
    {left right : Certificate}
    (equivalent : left.LinkPermutationEquivalent right) :
    left.intrinsicTraversalVertices =
      right.intrinsicTraversalVertices := by
  simp [intrinsicTraversalVertices,
    equivalent.intrinsicTraversalRaw_eq]

theorem StructurallyWellFormed.intrinsicTraversalVertices_closed_under_premises
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {produced premise : Vertex} {link : Link}
    (linkMember : link ∈ certificate.links)
    (produces : link.produces produced = true)
    (premiseMember : premise ∈ link.premises)
    (producedMember : produced ∈ certificate.intrinsicTraversalVertices) :
    premise ∈ certificate.intrinsicTraversalVertices := by
  rw [intrinsicTraversalVertices, List.mem_eraseDups,
    intrinsicTraversalRaw, List.mem_flatMap] at producedMember ⊢
  rcases producedMember with
    ⟨root, rootBoundary, producedInWalk⟩
  have rootInBounds :=
    structural.2.2.1 root rootBoundary
  have rootFormula :
      certificate.formula? root =
        some certificate.formulas[root] := by
    rw [formula?, Array.getElem?_eq_getElem rootInBounds]
  have producedInFormulaWalk :
      produced ∈ certificate.occurrenceWalk root
        certificate.formulas[root] := by
    simpa [occurrenceWalk?, rootFormula] using producedInWalk
  have premiseInFormulaWalk :=
    structural.occurrenceWalk_closed_under_premises
      rootInBounds rootFormula linkMember produces premiseMember
      producedInFormulaWalk
  refine ⟨root, rootBoundary, ?_⟩
  simpa [occurrenceWalk?, rootFormula] using premiseInFormulaWalk

/-- Sum of all stored occurrence complexities.  It supplies a finite global
budget for the strictly increasing parent chain used in the coverage proof. -/
def intrinsicComplexityBudget (certificate : Certificate) : Nat :=
  ((List.range certificate.formulas.size).map
    certificate.formulaComplexityAt).sum

private theorem nat_le_sum_of_mem {value : Nat} {values : List Nat}
    (member : value ∈ values) :
    value ≤ values.sum := by
  induction values with
  | nil => simp at member
  | cons head tail ih =>
      simp only [List.mem_cons] at member
      rcases member with rfl | tailMember
      · simp
      · have tailBound := ih tailMember
        simp only [List.sum_cons]
        omega

private theorem filter_length_le_of_imp {α : Type}
    (values : List α) (left right : α → Bool)
    (implies : ∀ value ∈ values,
      left value = true → right value = true) :
    (values.filter left).length ≤ (values.filter right).length := by
  induction values with
  | nil => simp
  | cons head tail ih =>
      have tailImplies : ∀ value ∈ tail,
          left value = true → right value = true := by
        intro value member
        exact implies value (by simp [member])
      have tailBound := ih tailImplies
      cases leftEquation : left head <;>
      cases rightEquation : right head
      · simpa [leftEquation, rightEquation] using tailBound
      · simp [leftEquation, rightEquation]
        exact Nat.le_succ_of_le tailBound
      · have impossible : right head = true :=
          implies head (by simp) leftEquation
        simp [rightEquation] at impossible
      · simpa [leftEquation, rightEquation] using
          Nat.succ_le_succ tailBound

theorem formulaComplexityAt_le_intrinsicComplexityBudget
    (certificate : Certificate) {vertex : Vertex}
    (inBounds : vertex < certificate.formulas.size) :
    certificate.formulaComplexityAt vertex ≤
      certificate.intrinsicComplexityBudget := by
  unfold intrinsicComplexityBudget
  apply nat_le_sum_of_mem
  rw [List.mem_map]
  exact ⟨vertex, by simpa using inBounds, rfl⟩

/-- Every in-bounds occurrence of a structurally well-formed proof structure
is reached from the ordered conclusion forest.  A non-boundary occurrence has
one parent; local typing strictly increases formula complexity toward that
parent, so the global complexity budget makes the recursive ascent
well-founded. -/
theorem StructurallyWellFormed.vertex_mem_intrinsicTraversalVertices
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    (vertex : Vertex) (inBounds : vertex < certificate.formulas.size) :
    vertex ∈ certificate.intrinsicTraversalVertices := by
  by_cases boundary : vertex ∈ certificate.conclusions
  · rw [intrinsicTraversalVertices, List.mem_eraseDups,
      intrinsicTraversalRaw, List.mem_flatMap]
    exact ⟨vertex, boundary,
      certificate.occurrenceWalk?_root_mem vertex⟩
  · have node := structural.2.2.2.2.2 vertex inBounds
    have parentCount : certificate.parentUseCount vertex = 1 := by
      simpa [NodeWellFormed, boundary] using node.2
    unfold parentUseCount at parentCount
    rcases List.length_eq_one_iff.mp parentCount with
      ⟨parentLink, parentFilter⟩
    have filtered : parentLink ∈
        certificate.links.filter (·.usesAsPremise vertex) := by
      rw [parentFilter]
      simp
    rcases List.mem_filter.mp filtered with
      ⟨parentMember, parentUses⟩
    have premiseMember : vertex ∈ parentLink.premises := by
      simpa [Link.usesAsPremise] using parentUses
    have parentWellFormed :=
      structural.2.2.2.2.1 parentLink parentMember
    have strictGrowth :=
      parentWellFormed.premise_complexity_lt_conclusion premiseMember
    cases parentLink with
    | «axiom» left right =>
        simp [Link.premises] at premiseMember
    | tensor left right conclusion =>
        have conclusionInBounds :
            conclusion < certificate.formulas.size :=
          parentWellFormed.2.2.2.2.2.1
        have strictComplexity :
            certificate.formulaComplexityAt vertex <
              certificate.formulaComplexityAt conclusion := by
          simpa [linkConclusionComplexity] using strictGrowth
        have conclusionBudget :=
          certificate.formulaComplexityAt_le_intrinsicComplexityBudget
            conclusionInBounds
        have vertexBelowBudget :
            certificate.formulaComplexityAt vertex <
              certificate.intrinsicComplexityBudget :=
          Nat.lt_of_lt_of_le strictComplexity conclusionBudget
        have rankDecrease :
            certificate.intrinsicComplexityBudget -
                certificate.formulaComplexityAt conclusion <
              certificate.intrinsicComplexityBudget -
                certificate.formulaComplexityAt vertex :=
          Nat.sub_lt_sub_left vertexBelowBudget strictComplexity
        have conclusionMember :=
          structural.vertex_mem_intrinsicTraversalVertices
            conclusion conclusionInBounds
        exact
          structural.intrinsicTraversalVertices_closed_under_premises
            parentMember (by simp [Link.produces]) premiseMember
            conclusionMember
    | par left right conclusion =>
        have conclusionInBounds :
            conclusion < certificate.formulas.size :=
          parentWellFormed.2.2.2.2.2.1
        have strictComplexity :
            certificate.formulaComplexityAt vertex <
              certificate.formulaComplexityAt conclusion := by
          simpa [linkConclusionComplexity] using strictGrowth
        have conclusionBudget :=
          certificate.formulaComplexityAt_le_intrinsicComplexityBudget
            conclusionInBounds
        have vertexBelowBudget :
            certificate.formulaComplexityAt vertex <
              certificate.intrinsicComplexityBudget :=
          Nat.lt_of_lt_of_le strictComplexity conclusionBudget
        have rankDecrease :
            certificate.intrinsicComplexityBudget -
                certificate.formulaComplexityAt conclusion <
              certificate.intrinsicComplexityBudget -
                certificate.formulaComplexityAt vertex :=
          Nat.sub_lt_sub_left vertexBelowBudget strictComplexity
        have conclusionMember :=
          structural.vertex_mem_intrinsicTraversalVertices
            conclusion conclusionInBounds
        exact
          structural.intrinsicTraversalVertices_closed_under_premises
            parentMember (by simp [Link.produces]) premiseMember
            conclusionMember
termination_by
  certificate.intrinsicComplexityBudget -
    certificate.formulaComplexityAt vertex
decreasing_by
  · exact rankDecrease
  · exact rankDecrease

theorem StructurallyWellFormed.occurrenceWalk_mem_inBounds
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {root : Vertex} {formula : Formula}
    (rootInBounds : root < certificate.formulas.size)
    (rootFormula : certificate.formula? root = some formula)
    {vertex : Vertex}
    (member : vertex ∈ certificate.occurrenceWalk root formula) :
    vertex < certificate.formulas.size := by
  induction formula generalizing root vertex with
  | atom name positive =>
      simp only [occurrenceWalk, List.mem_singleton] at member
      subst vertex
      exact rootInBounds
  | tensor leftFormula rightFormula leftIH rightIH =>
      rcases structural.uniqueTensorProducerData rootInBounds rootFormula with
        ⟨left, right, selected, leftFormulaAt, rightFormulaAt⟩
      rw [occurrenceWalk, selected] at member
      simp only [List.mem_cons, List.mem_append] at member
      rcases member with rfl | inLeft | inRight
      · exact rootInBounds
      · exact leftIH
          (inBounds_of_formula?_eq_some leftFormulaAt)
          leftFormulaAt inLeft
      · exact rightIH
          (inBounds_of_formula?_eq_some rightFormulaAt)
          rightFormulaAt inRight
  | par leftFormula rightFormula leftIH rightIH =>
      rcases structural.uniqueParProducerData rootInBounds rootFormula with
        ⟨left, right, selected, leftFormulaAt, rightFormulaAt⟩
      rw [occurrenceWalk, selected] at member
      simp only [List.mem_cons, List.mem_append] at member
      rcases member with rfl | inLeft | inRight
      · exact rootInBounds
      · exact leftIH
          (inBounds_of_formula?_eq_some leftFormulaAt)
          leftFormulaAt inLeft
      · exact rightIH
          (inBounds_of_formula?_eq_some rightFormulaAt)
          rightFormulaAt inRight

theorem StructurallyWellFormed.intrinsicTraversalVertices_mem_inBounds
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {vertex : Vertex}
    (member : vertex ∈ certificate.intrinsicTraversalVertices) :
    vertex < certificate.formulas.size := by
  rw [intrinsicTraversalVertices, List.mem_eraseDups,
    intrinsicTraversalRaw, List.mem_flatMap] at member
  rcases member with ⟨root, rootBoundary, inWalk⟩
  have rootInBounds := structural.2.2.1 root rootBoundary
  have rootFormula :
      certificate.formula? root =
        some certificate.formulas[root] := by
    rw [formula?, Array.getElem?_eq_getElem rootInBounds]
  apply structural.occurrenceWalk_mem_inBounds rootInBounds rootFormula
  simpa [occurrenceWalk?, rootFormula] using inWalk

/-- The intrinsic order contains exactly every formula-array vertex once on
the structurally well-formed domain. -/
structure IntrinsicTraversalComplete (certificate : Certificate) : Prop where
  length_eq :
    certificate.intrinsicTraversalVertices.length =
      certificate.formulas.size
  mem_iff : ∀ vertex,
    vertex < certificate.formulas.size ↔
      vertex ∈ certificate.intrinsicTraversalVertices

/-- Structural well-formedness makes the intrinsic traversal an exact
enumeration of the formula array. -/
theorem StructurallyWellFormed.intrinsicTraversalComplete
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed) :
    certificate.IntrinsicTraversalComplete := by
  have complete : ∀ vertex,
      vertex < certificate.formulas.size ↔
        vertex ∈ certificate.intrinsicTraversalVertices := by
    intro vertex
    exact ⟨structural.vertex_mem_intrinsicTraversalVertices vertex,
      structural.intrinsicTraversalVertices_mem_inBounds⟩
  have nodup : certificate.intrinsicTraversalVertices.Nodup := by
    unfold intrinsicTraversalVertices
    exact VertexRenaming.eraseDups_nodup _
  exact {
    length_eq := VertexRenaming.length_eq_of_nodup_complete
      certificate.formulas.size certificate.intrinsicTraversalVertices
      nodup complete
    mem_iff := complete }

theorem StructurallyWellFormed.ownedLinkFilter_length_eq_one
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {link : Link} (linkMember : link ∈ certificate.links) :
    (certificate.links.filter (·.ownedBy link.owner)).length = 1 := by
  have linkWellFormed :=
    structural.2.2.2.2.1 link linkMember
  cases link with
  | «axiom» left right =>
      rcases linkWellFormed.axiom_endpointFormula (Or.inl rfl) with
        ⟨name, positive, ownerFormula⟩
      have leftInBounds := inBounds_of_formula?_eq_some ownerFormula
      have node := structural.2.2.2.2.2 left leftInBounds
      have sourceCount : certificate.axiomCount left = 1 := by
        simpa [NodeWellFormed, ownerFormula] using node.1
      have upper :
          (certificate.links.filter (·.ownedBy left)).length ≤
            (certificate.links.filter
              (·.containsAxiomEndpoint left)).length := by
        apply filter_length_le_of_imp
        intro candidate candidateMember owned
        have candidateWellFormed :=
          structural.2.2.2.2.1 candidate candidateMember
        cases candidate with
        | «axiom» candidateLeft candidateRight =>
            have candidateLeftEq : candidateLeft = left := by
              simpa [Link.ownedBy] using owned
            subst candidateLeft
            simp [Link.containsAxiomEndpoint]
        | tensor candidateLeft candidateRight candidateConclusion =>
            have conclusionEq : candidateConclusion = left := by
              simpa [Link.ownedBy] using owned
            subst candidateConclusion
            rcases candidateWellFormed.tensor_formulaData with
              ⟨leftFormula, rightFormula, _leftEquation, _rightEquation,
                conclusionFormula⟩
            have impossible :
                Formula.tensor leftFormula rightFormula =
                  Formula.atom name positive := by
              exact Option.some.inj
                (conclusionFormula.symm.trans ownerFormula)
            cases impossible
        | par candidateLeft candidateRight candidateConclusion =>
            have conclusionEq : candidateConclusion = left := by
              simpa [Link.ownedBy] using owned
            subst candidateConclusion
            rcases candidateWellFormed.par_formulaData with
              ⟨leftFormula, rightFormula, _leftEquation, _rightEquation,
                conclusionFormula⟩
            have impossible :
                Formula.par leftFormula rightFormula =
                  Formula.atom name positive := by
              exact Option.some.inj
                (conclusionFormula.symm.trans ownerFormula)
            cases impossible
      have ownerMember :
          Link.axiom left right ∈
            certificate.links.filter (·.ownedBy left) :=
        List.mem_filter.mpr ⟨linkMember, by simp [Link.ownedBy]⟩
      have positiveLength := List.length_pos_of_mem ownerMember
      have upperOne :
          (certificate.links.filter (·.ownedBy left)).length ≤ 1 := by
        rw [← sourceCount]
        exact upper
      exact Nat.le_antisymm upperOne positiveLength
  | tensor left right conclusion =>
      rcases linkWellFormed.tensor_formulaData with
        ⟨leftFormula, rightFormula, _leftEquation, _rightEquation,
          ownerFormula⟩
      have conclusionInBounds :=
        inBounds_of_formula?_eq_some ownerFormula
      have node :=
        structural.2.2.2.2.2 conclusion conclusionInBounds
      have sourceCount : certificate.producerCount conclusion = 1 := by
        simpa [NodeWellFormed, ownerFormula] using node.1
      have upper :
          (certificate.links.filter (·.ownedBy conclusion)).length ≤
            (certificate.links.filter (·.produces conclusion)).length := by
        apply filter_length_le_of_imp
        intro candidate candidateMember owned
        have candidateWellFormed :=
          structural.2.2.2.2.1 candidate candidateMember
        cases candidate with
        | «axiom» candidateLeft candidateRight =>
            have candidateLeftEq : candidateLeft = conclusion := by
              simpa [Link.ownedBy] using owned
            subst candidateLeft
            rcases candidateWellFormed.axiom_endpointFormula (Or.inl rfl) with
              ⟨name, positive, candidateFormula⟩
            have impossible :
                Formula.atom name positive =
                  Formula.tensor leftFormula rightFormula := by
              exact Option.some.inj
                (candidateFormula.symm.trans ownerFormula)
            cases impossible
        | tensor candidateLeft candidateRight candidateConclusion =>
            simpa [Link.ownedBy, Link.produces] using owned
        | par candidateLeft candidateRight candidateConclusion =>
            simpa [Link.ownedBy, Link.produces] using owned
      have ownerMember :
          Link.tensor left right conclusion ∈
            certificate.links.filter (·.ownedBy conclusion) :=
        List.mem_filter.mpr ⟨linkMember, by simp [Link.ownedBy]⟩
      have positiveLength := List.length_pos_of_mem ownerMember
      have upperOne :
          (certificate.links.filter (·.ownedBy conclusion)).length ≤ 1 := by
        rw [← sourceCount]
        exact upper
      exact Nat.le_antisymm upperOne positiveLength
  | par left right conclusion =>
      rcases linkWellFormed.par_formulaData with
        ⟨leftFormula, rightFormula, _leftEquation, _rightEquation,
          ownerFormula⟩
      have conclusionInBounds :=
        inBounds_of_formula?_eq_some ownerFormula
      have node :=
        structural.2.2.2.2.2 conclusion conclusionInBounds
      have sourceCount : certificate.producerCount conclusion = 1 := by
        simpa [NodeWellFormed, ownerFormula] using node.1
      have upper :
          (certificate.links.filter (·.ownedBy conclusion)).length ≤
            (certificate.links.filter (·.produces conclusion)).length := by
        apply filter_length_le_of_imp
        intro candidate candidateMember owned
        have candidateWellFormed :=
          structural.2.2.2.2.1 candidate candidateMember
        cases candidate with
        | «axiom» candidateLeft candidateRight =>
            have candidateLeftEq : candidateLeft = conclusion := by
              simpa [Link.ownedBy] using owned
            subst candidateLeft
            rcases candidateWellFormed.axiom_endpointFormula (Or.inl rfl) with
              ⟨name, positive, candidateFormula⟩
            have impossible :
                Formula.atom name positive =
                  Formula.par leftFormula rightFormula := by
              exact Option.some.inj
                (candidateFormula.symm.trans ownerFormula)
            cases impossible
        | tensor candidateLeft candidateRight candidateConclusion =>
            simpa [Link.ownedBy, Link.produces] using owned
        | par candidateLeft candidateRight candidateConclusion =>
            simpa [Link.ownedBy, Link.produces] using owned
      have ownerMember :
          Link.par left right conclusion ∈
            certificate.links.filter (·.ownedBy conclusion) :=
        List.mem_filter.mpr ⟨linkMember, by simp [Link.ownedBy]⟩
      have positiveLength := List.length_pos_of_mem ownerMember
      have upperOne :
          (certificate.links.filter (·.ownedBy conclusion)).length ≤ 1 := by
        rw [← sourceCount]
        exact upper
      exact Nat.le_antisymm upperOne positiveLength

theorem StructurallyWellFormed.uniqueOwnedLink?_eq_some
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {link : Link} (linkMember : link ∈ certificate.links) :
    certificate.uniqueOwnedLink? link.owner = some link :=
  uniqueOwnedLink?_eq_some_of_count
    (structural.ownedLinkFilter_length_eq_one linkMember)
    linkMember link.ownedBy_owner

private theorem nodup_of_owned_filter_length_eq_one
    (links : List Link)
    (unique : ∀ link ∈ links,
      (links.filter (·.ownedBy link.owner)).length = 1) :
    links.Nodup := by
  induction links with
  | nil => exact .nil
  | cons head tail ih =>
      have headNotTail : head ∉ tail := by
        intro headInTail
        have equation := unique head (by simp)
        have filteredTailMember :
            head ∈ tail.filter (·.ownedBy head.owner) :=
          List.mem_filter.mpr ⟨headInTail, head.ownedBy_owner⟩
        have positiveTail :=
          List.length_pos_of_mem filteredTailMember
        have filteredCons :
            ((head :: tail).filter (·.ownedBy head.owner)) =
              head :: tail.filter (·.ownedBy head.owner) := by
          simp
        rw [filteredCons] at equation
        simp only [List.length_cons] at equation
        omega
      have tailUnique : ∀ link ∈ tail,
          (tail.filter (·.ownedBy link.owner)).length = 1 := by
        intro link linkInTail
        have fullEquation := unique link (by simp [linkInTail])
        cases ownerEquation : head.ownedBy link.owner
        · simpa [List.filter_cons, ownerEquation] using fullEquation
        · have linkFiltered :
              link ∈ tail.filter (·.ownedBy link.owner) :=
            List.mem_filter.mpr ⟨linkInTail, link.ownedBy_owner⟩
          have positiveTail := List.length_pos_of_mem linkFiltered
          have filteredCons :
              ((head :: tail).filter (·.ownedBy link.owner)) =
                head :: tail.filter (·.ownedBy link.owner) := by
            simp [ownerEquation]
          rw [filteredCons] at fullEquation
          simp only [List.length_cons] at fullEquation
          omega
      refine .cons ?_ (ih tailUnique)
      intro value valueMember same
      subst value
      exact headNotTail valueMember

theorem StructurallyWellFormed.links_nodup
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed) :
    certificate.links.Nodup := by
  apply nodup_of_owned_filter_length_eq_one
  intro link linkMember
  exact structural.ownedLinkFilter_length_eq_one linkMember

/-- Links emitted in occurrence order, once per orientation-sensitive owner. -/
def intrinsicOrderedLinks (certificate : Certificate) : List Link :=
  certificate.intrinsicTraversalVertices.filterMap
    certificate.uniqueOwnedLink?

theorem StructurallyWellFormed.mem_intrinsicOrderedLinks_iff
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    (link : Link) :
    link ∈ certificate.intrinsicOrderedLinks ↔
      link ∈ certificate.links := by
  constructor
  · intro member
    rw [intrinsicOrderedLinks, List.mem_filterMap] at member
    rcases member with ⟨vertex, _vertexMember, selected⟩
    have filtered :=
      ExactOne.mem_of_select?_eq_some selected
    exact (List.mem_filter.mp filtered).1
  · intro linkMember
    rw [intrinsicOrderedLinks, List.mem_filterMap]
    have linkWellFormed :=
      structural.2.2.2.2.1 link linkMember
    have ownerInBounds :=
      certificate.vertex_inBounds_of_linkWellFormed
        linkWellFormed link.owner_mem_vertices
    exact ⟨link.owner,
      structural.vertex_mem_intrinsicTraversalVertices
        link.owner ownerInBounds,
      structural.uniqueOwnedLink?_eq_some linkMember⟩

theorem intrinsicOrderedLinks_nodup
    (certificate : Certificate) :
    certificate.intrinsicOrderedLinks.Nodup := by
  unfold intrinsicOrderedLinks
  rw [List.nodup_iff_pairwise_ne, List.pairwise_filterMap]
  have traversalNodup :
      certificate.intrinsicTraversalVertices.Nodup := by
    unfold intrinsicTraversalVertices
    exact VertexRenaming.eraseDups_nodup _
  rw [List.nodup_iff_pairwise_ne] at traversalNodup
  apply traversalNodup.imp
  intro first second different output firstSelected
    secondOutput secondSelected
  intro sameOutput
  subst secondOutput
  have firstFiltered :=
    ExactOne.mem_of_select?_eq_some firstSelected
  have secondFiltered :=
    ExactOne.mem_of_select?_eq_some secondSelected
  have firstOwned :=
    (List.mem_filter.mp firstFiltered).2
  have secondOwned :=
    (List.mem_filter.mp secondFiltered).2
  apply different
  exact
    (output.ownedBy_eq_true_iff_owner_eq first).mp firstOwned |>.symm.trans
      ((output.ownedBy_eq_true_iff_owner_eq second).mp secondOwned)

private theorem perm_of_nodup_of_mem_iff
    {α : Type} [BEq α] [LawfulBEq α]
    {left right : List α}
    (leftNodup : left.Nodup) (rightNodup : right.Nodup)
    (sameMembers : ∀ value, value ∈ left ↔ value ∈ right) :
    left.Perm right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => exact .nil
      | cons head tail =>
          have impossible : head ∈ ([] : List α) :=
            (sameMembers head).mpr (by simp)
          simp at impossible
  | cons head tail ih =>
      cases leftNodup with
      | @cons _ _ headDifferent tailNodup =>
          have headNotTail : head ∉ tail := by
            intro member
            exact headDifferent head member rfl
          have headRight : head ∈ right :=
            (sameMembers head).mp (by simp)
          have sameTail : ∀ value,
              value ∈ tail ↔ value ∈ right.erase head := by
            intro value
            by_cases sameHead : value = head
            · subst value
              simp [headNotTail, rightNodup.not_mem_erase]
            · rw [List.mem_erase_of_ne sameHead]
              simpa [sameHead] using sameMembers value
          exact List.cons_perm_iff_perm_erase.mpr
            ⟨headRight,
              ih tailNodup (rightNodup.erase head) sameTail⟩

/-- On structurally well-formed certificates the intrinsic owner emission is
exactly a permutation of the submitted link multiset. -/
theorem StructurallyWellFormed.intrinsicOrderedLinks_perm
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed) :
    certificate.intrinsicOrderedLinks.Perm certificate.links := by
  apply perm_of_nodup_of_mem_iff
  · exact certificate.intrinsicOrderedLinks_nodup
  · exact structural.links_nodup
  · intro link
    exact structural.mem_intrinsicOrderedLinks_iff link

@[simp] theorem intrinsicOrderedLinks_reindex (certificate : Certificate)
    (r : VertexRenaming certificate.formulas.size) :
    (certificate.reindex r).intrinsicOrderedLinks =
      certificate.intrinsicOrderedLinks.map (Link.reindex r) := by
  unfold intrinsicOrderedLinks
  rw [certificate.intrinsicTraversalVertices_reindex r,
    List.filterMap_map]
  induction certificate.intrinsicTraversalVertices with
  | nil => rfl
  | cons head tail ih =>
      rw [List.filterMap_cons, List.filterMap_cons]
      simp only [Function.comp_apply]
      rw [certificate.uniqueOwnedLink?_reindex r head]
      cases certificate.uniqueOwnedLink? head <;>
        simp [ih]

theorem LinkPermutationEquivalent.intrinsicOrderedLinks_eq
    {left right : Certificate}
    (equivalent : left.LinkPermutationEquivalent right) :
    left.intrinsicOrderedLinks = right.intrinsicOrderedLinks := by
  unfold intrinsicOrderedLinks
  rw [equivalent.intrinsicTraversalVertices_eq]
  induction right.intrinsicTraversalVertices with
  | nil => rfl
  | cons head tail ih =>
      rw [List.filterMap_cons, List.filterMap_cons,
        equivalent.uniqueOwnedLink?_eq head, ih]

/-- Non-factorial normalization.  The intrinsic order fixes link storage
before the already proved v0.3 reindex-normalizer removes submitted vertex
numbers. -/
def intrinsicCanonicalize (certificate : Certificate) : Certificate :=
  Certificate.equivalenceCanonicalize
    ({ certificate with links := certificate.intrinsicOrderedLinks } :
      Certificate)

@[simp] theorem intrinsicCanonicalize_reindex (certificate : Certificate)
    (r : VertexRenaming certificate.formulas.size) :
    (certificate.reindex r).intrinsicCanonicalize =
      certificate.intrinsicCanonicalize := by
  unfold intrinsicCanonicalize
  have updated :
      ({ certificate.reindex r with
          links := (certificate.reindex r).intrinsicOrderedLinks } :
        Certificate) =
        (({ certificate with links := certificate.intrinsicOrderedLinks } :
          Certificate).reindex r) := by
    apply Certificate.ext_fields
    · rfl
    · simp
    · rfl
  rw [updated]
  exact
    ({ certificate with links := certificate.intrinsicOrderedLinks } :
      Certificate).equivalenceCanonicalize_reindex r

theorem LinkPermutationEquivalent.intrinsicCanonicalize_eq
    {left right : Certificate}
    (equivalent : left.LinkPermutationEquivalent right) :
    left.intrinsicCanonicalize = right.intrinsicCanonicalize := by
  unfold intrinsicCanonicalize
  have updated :
      ({ left with links := left.intrinsicOrderedLinks } : Certificate) =
        ({ right with links := right.intrinsicOrderedLinks } :
          Certificate) := by
    apply Certificate.ext_fields
    · exact equivalent.formulas
    · exact equivalent.intrinsicOrderedLinks_eq
    · exact equivalent.conclusions
  rw [updated]

/-- The non-factorial normalization is invariant under the exact public
proof-net identity relation. -/
theorem ProofNetEquivalent.intrinsicCanonicalize_eq
    {left right : Certificate}
    (equivalent : left.ProofNetEquivalent right) :
    left.intrinsicCanonicalize = right.intrinsicCanonicalize := by
  rcases equivalent.toDirect with ⟨r, linkPermutation⟩
  exact (left.intrinsicCanonicalize_reindex r).symm.trans
    linkPermutation.intrinsicCanonicalize_eq

/-- On the supported structural domain, intrinsic normalization stays inside
the input's exact `ProofNetEquivalent` class. -/
theorem StructurallyWellFormed.intrinsicCanonicalize_proofNetEquivalent
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed) :
    certificate.ProofNetEquivalent certificate.intrinsicCanonicalize := by
  let reordered : Certificate :=
    { certificate with links := certificate.intrinsicOrderedLinks }
  have reorderedToInput :
      reordered.LinkPermutationEquivalent certificate :=
    ⟨rfl, structural.intrinsicOrderedLinks_perm, rfl⟩
  have reorderedStructural : reordered.StructurallyWellFormed :=
    reorderedToInput.structurallyWellFormed_iff.mpr structural
  have reorderedToNormal :
      reordered.ReindexEquivalent certificate.intrinsicCanonicalize := by
    simpa [intrinsicCanonicalize, reordered] using
      reorderedStructural.equivalenceCanonicalize_reindexEquivalent
  exact reorderedToInput.symm.toProofNetEquivalent.trans
    reorderedToNormal.toProofNetEquivalent

/-- The non-factorial intrinsic canonical form is a complete invariant for
exactly `ProofNetEquivalent` on structurally well-formed certificates. -/
theorem proofNetEquivalent_iff_intrinsicCanonicalize_eq
    {left right : Certificate}
    (leftStructural : left.StructurallyWellFormed)
    (rightStructural : right.StructurallyWellFormed) :
    left.ProofNetEquivalent right ↔
      left.intrinsicCanonicalize = right.intrinsicCanonicalize := by
  constructor
  · exact fun equivalent => equivalent.intrinsicCanonicalize_eq
  · intro sameCanonical
    have leftToCanonical :=
      leftStructural.intrinsicCanonicalize_proofNetEquivalent
    have rightToCanonical :=
      rightStructural.intrinsicCanonicalize_proofNetEquivalent
    rw [sameCanonical] at leftToCanonical
    exact leftToCanonical.trans rightToCanonical.symm

/-- Checker acceptance supplies the structural premises of the exact
non-factorial canonical-form theorem. -/
theorem proofNetEquivalent_iff_intrinsicCanonicalize_eq_of_check
    {left right : Certificate}
    (leftAccepted : left.check = true)
    (rightAccepted : right.check = true) :
    left.ProofNetEquivalent right ↔
      left.intrinsicCanonicalize = right.intrinsicCanonicalize :=
  proofNetEquivalent_iff_intrinsicCanonicalize_eq
    (left.check_sound_declarative leftAccepted).1
    (right.check_sound_declarative rightAccepted).1

/-- Polynomially generated, injective structural token code for the intrinsic
canonical form. -/
def intrinsicCanonicalCode (certificate : Certificate) : List String :=
  certificate.intrinsicCanonicalize.structuralCode

theorem ProofNetEquivalent.intrinsicCanonicalCode_eq
    {left right : Certificate}
    (equivalent : left.ProofNetEquivalent right) :
    left.intrinsicCanonicalCode = right.intrinsicCanonicalCode := by
  simp [intrinsicCanonicalCode, equivalent.intrinsicCanonicalize_eq]

/-- On structurally well-formed certificates, intrinsic-code equality is
equivalent to exactly `ProofNetEquivalent`. -/
theorem proofNetEquivalent_iff_intrinsicCanonicalCode_eq
    {left right : Certificate}
    (leftStructural : left.StructurallyWellFormed)
    (rightStructural : right.StructurallyWellFormed) :
    left.ProofNetEquivalent right ↔
      left.intrinsicCanonicalCode = right.intrinsicCanonicalCode := by
  rw [proofNetEquivalent_iff_intrinsicCanonicalize_eq
    leftStructural rightStructural]
  constructor
  · intro same
    simp [intrinsicCanonicalCode, same]
  · intro same
    exact structuralCode_injective same

/-- Checker acceptance supplies the structural premises of the exact
intrinsic-code theorem. -/
theorem proofNetEquivalent_iff_intrinsicCanonicalCode_eq_of_check
    {left right : Certificate}
    (leftAccepted : left.check = true)
    (rightAccepted : right.check = true) :
    left.ProofNetEquivalent right ↔
      left.intrinsicCanonicalCode = right.intrinsicCanonicalCode :=
  proofNetEquivalent_iff_intrinsicCanonicalCode_eq
    (left.check_sound_declarative leftAccepted).1
    (right.check_sound_declarative rightAccepted).1

end Certificate

end ProofNetIR
