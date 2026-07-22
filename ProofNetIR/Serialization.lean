import Lean.Data.Json
import ProofNetIR.Reindex

namespace ProofNetIR

namespace Link

def relabel (rename : Vertex → Vertex) : Link → Link
  | .axiom left right => .axiom (rename left) (rename right)
  | .tensor left right conclusion =>
      .tensor (rename left) (rename right) (rename conclusion)
  | .par left right conclusion =>
      .par (rename left) (rename right) (rename conclusion)

theorem mem_vertices_of_containsAxiomEndpoint {link : Link} {vertex : Vertex}
    (contains : link.containsAxiomEndpoint vertex = true) :
    vertex ∈ link.vertices := by
  cases link with
  | «axiom» left right =>
      simp only [containsAxiomEndpoint, Bool.or_eq_true, beq_iff_eq] at contains
      rcases contains with leftEq | rightEq
      · simp [vertices, leftEq]
      · simp [vertices, rightEq]
  | tensor left right conclusion =>
      simp [containsAxiomEndpoint] at contains
  | par left right conclusion =>
      simp [containsAxiomEndpoint] at contains

theorem mem_vertices_of_produces {link : Link} {vertex : Vertex}
    (produced : link.produces vertex = true) :
    vertex ∈ link.vertices := by
  cases link with
  | «axiom» left right =>
      simp [Link.produces] at produced
  | tensor left right conclusion =>
      simp only [Link.produces, beq_iff_eq] at produced
      simp [vertices, produced]
  | par left right conclusion =>
      simp only [Link.produces, beq_iff_eq] at produced
      simp [vertices, produced]

/-- Canonicalize the symmetric endpoints of an axiom link. Tensor and par
premise order remains significant in the formula syntax. -/
def canonicalize : Link → Link
  | .axiom left right =>
      if left ≤ right then .axiom left right else .axiom right left
  | link => link

def sortKey : Link → List Nat
  | .axiom left right => [0, left, right]
  | .tensor left right conclusion => [1, conclusion, left, right]
  | .par left right conclusion => [2, conclusion, left, right]

end Link

namespace Certificate

theorem vertex_inBounds_of_linkWellFormed (certificate : Certificate)
    {link : Link} (wellFormed : certificate.LinkWellFormed link)
    {vertex : Vertex} (member : vertex ∈ link.vertices) :
    vertex < certificate.formulas.size := by
  cases link with
  | «axiom» left right =>
      rcases wellFormed with ⟨_, leftInBounds, rightInBounds, _⟩
      simp [Link.vertices] at member
      rcases member with rfl | rfl
      · exact leftInBounds
      · exact rightInBounds
  | tensor left right conclusion =>
      rcases wellFormed with
        ⟨_, _, _, leftInBounds, rightInBounds, conclusionInBounds, _⟩
      simp [Link.vertices] at member
      rcases member with rfl | rfl | rfl
      · exact leftInBounds
      · exact rightInBounds
      · exact conclusionInBounds
  | par left right conclusion =>
      rcases wellFormed with
        ⟨_, _, _, leftInBounds, rightInBounds, conclusionInBounds, _⟩
      simp [Link.vertices] at member
      rcases member with rfl | rfl | rfl
      · exact leftInBounds
      · exact rightInBounds
      · exact conclusionInBounds

private theorem exists_mem_filter_of_length_eq_one (links : List Link)
    (predicate : Link → Bool)
    (count : (links.filter predicate).length = 1) :
    ∃ link ∈ links, predicate link = true := by
  have positive : 0 < (links.filter predicate).length := by omega
  rcases List.exists_mem_of_length_pos positive with ⟨link, member⟩
  have filtered := List.mem_filter.mp member
  exact ⟨link, filtered.1, filtered.2⟩

/-- Deterministic vertex discovery order for `ReindexEquivalent`. That
relation preserves conclusion and link order, so first occurrence is stable
under every admissible vertex renaming. -/
def traversalVertices (certificate : Certificate) : List Vertex :=
  (certificate.conclusions ++ certificate.links.flatMap Link.vertices).eraseDups

theorem vertex_mem_traversal_of_nodeWellFormed (certificate : Certificate)
    {vertex : Vertex} (inBounds : vertex < certificate.formulas.size)
    (wellFormed : certificate.NodeWellFormed vertex) :
    vertex ∈ certificate.traversalVertices := by
  have formulaAt : certificate.formula? vertex =
      some certificate.formulas[vertex] := by
    rw [formula?, Array.getElem?_eq_getElem inBounds]
  have source := wellFormed.1
  cases formulaValue : certificate.formulas[vertex] with
  | atom name positive =>
      have count : (certificate.links.filter
          (·.containsAxiomEndpoint vertex)).length = 1 := by
        simpa [formulaAt, formulaValue, axiomCount] using source
      rcases exists_mem_filter_of_length_eq_one certificate.links
        (·.containsAxiomEndpoint vertex) count with
        ⟨link, linkMember, contains⟩
      apply (List.mem_eraseDups).mpr
      simp only [List.mem_append, List.mem_flatMap]
      exact Or.inr ⟨link, linkMember,
        Link.mem_vertices_of_containsAxiomEndpoint contains⟩
  | tensor left right =>
      have count : (certificate.links.filter
          (·.produces vertex)).length = 1 := by
        simpa [formulaAt, formulaValue, producerCount] using source
      rcases exists_mem_filter_of_length_eq_one certificate.links
        (·.produces vertex) count with ⟨link, linkMember, produces⟩
      apply (List.mem_eraseDups).mpr
      simp only [List.mem_append, List.mem_flatMap]
      exact Or.inr ⟨link, linkMember, Link.mem_vertices_of_produces produces⟩
  | par left right =>
      have count : (certificate.links.filter
          (·.produces vertex)).length = 1 := by
        simpa [formulaAt, formulaValue, producerCount] using source
      rcases exists_mem_filter_of_length_eq_one certificate.links
        (·.produces vertex) count with ⟨link, linkMember, produces⟩
      apply (List.mem_eraseDups).mpr
      simp only [List.mem_append, List.mem_flatMap]
      exact Or.inr ⟨link, linkMember, Link.mem_vertices_of_produces produces⟩

/-- The traversal enumerates every in-bounds formula vertex exactly once and
contains no out-of-bounds references. -/
structure TraversalComplete (certificate : Certificate) : Prop where
  length_eq : certificate.traversalVertices.length = certificate.formulas.size
  mem_iff : ∀ vertex,
    vertex < certificate.formulas.size ↔
      vertex ∈ certificate.traversalVertices

theorem traversalComplete_of_structurallyWellFormed
    (certificate : Certificate)
    (wellFormed : certificate.StructurallyWellFormed) :
    certificate.TraversalComplete := by
  rcases wellFormed with
    ⟨_, _, conclusionsInBounds, _, linksWellFormed, nodesWellFormed⟩
  have complete : ∀ vertex,
      vertex < certificate.formulas.size ↔
        vertex ∈ certificate.traversalVertices := by
    intro vertex
    constructor
    · intro inBounds
      exact certificate.vertex_mem_traversal_of_nodeWellFormed inBounds
        (nodesWellFormed vertex inBounds)
    · intro member
      rw [traversalVertices, List.mem_eraseDups] at member
      simp only [List.mem_append, List.mem_flatMap] at member
      rcases member with conclusionMember |
          ⟨link, linkMember, vertexMember⟩
      · exact conclusionsInBounds vertex conclusionMember
      · exact certificate.vertex_inBounds_of_linkWellFormed
          (linksWellFormed link linkMember) vertexMember
  have nodup : certificate.traversalVertices.Nodup := by
    unfold traversalVertices
    exact VertexRenaming.eraseDups_nodup _
  exact {
    length_eq := VertexRenaming.length_eq_of_nodup_complete
      certificate.formulas.size certificate.traversalVertices nodup complete
    mem_iff := complete }

def traversalRenaming (certificate : Certificate)
    (complete : certificate.TraversalComplete) :
    VertexRenaming certificate.formulas.size :=
  VertexRenaming.ofOrder certificate.formulas.size
    certificate.traversalVertices complete.length_eq
    (by
      unfold traversalVertices
      exact VertexRenaming.eraseDups_nodup _) complete.mem_iff

@[simp] theorem traversalRenaming_forward
    (certificate : Certificate) (complete : certificate.TraversalComplete)
    {vertex : Vertex} (inBounds : vertex < certificate.formulas.size) :
    (certificate.traversalRenaming complete).forward vertex =
      certificate.traversalVertices.idxOf vertex := by
  exact VertexRenaming.ofOrder_forward_inBounds _ _ _ _ _ inBounds

@[simp] theorem traversalRenaming_inverse
    (certificate : Certificate) (complete : certificate.TraversalComplete)
    {vertex : Vertex} (inBounds : vertex < certificate.formulas.size) :
    (certificate.traversalRenaming complete).inverse vertex =
      certificate.traversalVertices[vertex]'(
        by simpa [complete.length_eq] using inBounds) := by
  exact VertexRenaming.ofOrder_inverse_inBounds _ _ _ _ _ inBounds

theorem filterMapFormula_eq_mapGetD (certificate : Certificate)
    (vertices : List Vertex)
    (allInBounds : ∀ vertex ∈ vertices,
      vertex < certificate.formulas.size) (fallback : Formula) :
    vertices.filterMap certificate.formula? =
      vertices.map (fun vertex => certificate.formulas.getD vertex fallback) := by
  induction vertices with
  | nil => rfl
  | cons head tail ih =>
      have headInBounds : head < certificate.formulas.size :=
        allInBounds head (by simp)
      have tailInBounds : ∀ vertex ∈ tail,
          vertex < certificate.formulas.size := by
        intro vertex member
        exact allInBounds vertex (by simp [member])
      have formulaAtHead : certificate.formula? head =
          some (certificate.formulas.getD head fallback) := by
        rw [formula?, Array.getElem?_eq_getElem headInBounds,
          ← Array.getElem_eq_getD fallback]
      simp [formulaAtHead, ih tailInBounds]

theorem linkRelabel_traversal_eq_reindex (certificate : Certificate)
    (complete : certificate.TraversalComplete) (link : Link)
    (linkMember : link ∈ certificate.links) :
    link.relabel (fun vertex => certificate.traversalVertices.idxOf vertex) =
      link.reindex (certificate.traversalRenaming complete) := by
  have vertexInBounds : ∀ vertex ∈ link.vertices,
      vertex < certificate.formulas.size := by
    intro vertex vertexMember
    apply (complete.mem_iff vertex).mpr
    simp only [traversalVertices, List.mem_eraseDups, List.mem_append,
      List.mem_flatMap]
    exact Or.inr ⟨link, linkMember, vertexMember⟩
  cases link with
  | «axiom» left right =>
      have leftInBounds := vertexInBounds left (by simp [Link.vertices])
      have rightInBounds := vertexInBounds right (by simp [Link.vertices])
      simp [Link.relabel, Link.reindex,
        certificate.traversalRenaming_forward complete leftInBounds,
        certificate.traversalRenaming_forward complete rightInBounds]
  | tensor left right conclusion =>
      have leftInBounds := vertexInBounds left (by simp [Link.vertices])
      have rightInBounds := vertexInBounds right (by simp [Link.vertices])
      have conclusionInBounds := vertexInBounds conclusion
        (by simp [Link.vertices])
      simp [Link.relabel, Link.reindex,
        certificate.traversalRenaming_forward complete leftInBounds,
        certificate.traversalRenaming_forward complete rightInBounds,
        certificate.traversalRenaming_forward complete conclusionInBounds]
  | par left right conclusion =>
      have leftInBounds := vertexInBounds left (by simp [Link.vertices])
      have rightInBounds := vertexInBounds right (by simp [Link.vertices])
      have conclusionInBounds := vertexInBounds conclusion
        (by simp [Link.vertices])
      simp [Link.relabel, Link.reindex,
        certificate.traversalRenaming_forward complete leftInBounds,
        certificate.traversalRenaming_forward complete rightInBounds,
        certificate.traversalRenaming_forward complete conclusionInBounds]

/-- Replace submitted vertex numbers by their first-occurrence positions.
Malformed certificates are still serialized deterministically. Coverage and
representative-membership theorems for structurally well-formed certificates
remain separate proof obligations. -/
def traversalRelabel (certificate : Certificate) : Certificate :=
  let order := certificate.traversalVertices
  let rename := fun vertex => order.idxOf vertex
  { formulas := (order.filterMap certificate.formula?).toArray
    links := certificate.links.map (Link.relabel rename)
    conclusions := certificate.conclusions.map rename }

theorem traversalRelabel_formulas_eq_reindex (certificate : Certificate)
    (nonempty : 0 < certificate.formulas.size)
    (complete : certificate.TraversalComplete) :
    certificate.traversalRelabel.formulas =
      (certificate.reindex
        (certificate.traversalRenaming complete)).formulas := by
  let fallback : Formula := certificate.formulas[0]'nonempty
  have allInBounds : ∀ vertex ∈ certificate.traversalVertices,
      vertex < certificate.formulas.size := by
    intro vertex member
    exact (complete.mem_iff vertex).mpr member
  have ordered := certificate.filterMapFormula_eq_mapGetD
    certificate.traversalVertices allInBounds fallback
  apply Array.ext
  · simp [traversalRelabel, ordered, complete.length_eq]
  · intro index leftInBounds rightInBounds
    have indexInBounds : index < certificate.formulas.size := by
      simpa [traversalRelabel, ordered, complete.length_eq] using leftInBounds
    have indexInOrder : index < certificate.traversalVertices.length := by
      simpa [complete.length_eq] using indexInBounds
    have valueInBounds : certificate.traversalVertices[index] <
        certificate.formulas.size :=
      allInBounds certificate.traversalVertices[index]
        (List.getElem_mem indexInOrder)
    simp [traversalRelabel, ordered, reindex,
      Array.getElem_eq_getD fallback]
    rw [List.getElem?_eq_getElem indexInOrder]
    simp [indexInBounds, valueInBounds]

/-- On a nonempty certificate whose ordered traversal contains exactly its
formula vertices, first-occurrence normalization is literally a bounded vertex
reindexing of the source certificate. -/
theorem traversalRelabel_eq_reindex (certificate : Certificate)
    (nonempty : 0 < certificate.formulas.size)
    (complete : certificate.TraversalComplete) :
    certificate.traversalRelabel =
      certificate.reindex (certificate.traversalRenaming complete) := by
  apply ext_fields
  · exact certificate.traversalRelabel_formulas_eq_reindex nonempty complete
  · simp only [traversalRelabel, reindex_links]
    apply List.map_congr_left
    intro link linkMember
    exact certificate.linkRelabel_traversal_eq_reindex complete link linkMember
  · simp only [traversalRelabel, reindex_conclusions]
    apply List.map_congr_left
    intro conclusion conclusionMember
    have traversalMember : conclusion ∈ certificate.traversalVertices := by
      simp [traversalVertices, conclusionMember]
    have inBounds : conclusion < certificate.formulas.size :=
      (complete.mem_iff conclusion).mpr traversalMember
    exact (certificate.traversalRenaming_forward complete inBounds).symm

theorem traversalRelabel_reindexEquivalent (certificate : Certificate)
    (nonempty : 0 < certificate.formulas.size)
    (complete : certificate.TraversalComplete) :
    certificate.ReindexEquivalent certificate.traversalRelabel :=
  ⟨certificate.traversalRenaming complete,
    certificate.traversalRelabel_eq_reindex nonempty complete⟩

theorem StructurallyWellFormed.traversalRelabel_reindexEquivalent
    {certificate : Certificate}
    (wellFormed : certificate.StructurallyWellFormed) :
    certificate.ReindexEquivalent certificate.traversalRelabel :=
  certificate.traversalRelabel_reindexEquivalent wellFormed.1
    (certificate.traversalComplete_of_structurallyWellFormed wellFormed)

@[simp] theorem traversalVertices_reindex (certificate : Certificate)
    (r : VertexRenaming certificate.formulas.size) :
    (certificate.reindex r).traversalVertices =
      certificate.traversalVertices.map r.forward := by
  simp only [traversalVertices, reindex_conclusions, reindex_links,
    List.flatMap_map]
  have links :
      List.flatMap (fun link => (link.reindex r).vertices) certificate.links =
        (certificate.links.flatMap Link.vertices).map r.forward := by
    induction certificate.links with
    | nil => rfl
    | cons head tail ih =>
        rw [List.flatMap_cons, List.flatMap_cons, List.map_append,
          Link.vertices_reindex, ih]
  rw [links, ← List.map_append, r.eraseDups_map_forward]

theorem formulasAtTraversal_reindex (certificate : Certificate)
    (r : VertexRenaming certificate.formulas.size) :
    ((certificate.reindex r).traversalVertices.filterMap
      (certificate.reindex r).formula?) =
      certificate.traversalVertices.filterMap certificate.formula? := by
  rw [certificate.traversalVertices_reindex, List.filterMap_map]
  have functions : (certificate.reindex r).formula? ∘ r.forward =
      certificate.formula? := by
    funext vertex
    exact certificate.reindex_formula?_forward r vertex
  rw [functions]

theorem linkRelabel_reindex_traversal (certificate : Certificate)
    (r : VertexRenaming certificate.formulas.size) (link : Link) :
    (link.reindex r).relabel
        (fun vertex =>
          (certificate.reindex r).traversalVertices.idxOf vertex) =
      link.relabel
        (fun vertex => certificate.traversalVertices.idxOf vertex) := by
  cases link <;>
    simp only [Link.relabel, Link.reindex,
      certificate.traversalVertices_reindex,
      VertexRenaming.idxOf_map_forward]

/-- First-occurrence relabeling removes every submitted vertex name. -/
@[simp] theorem traversalRelabel_reindex (certificate : Certificate)
    (r : VertexRenaming certificate.formulas.size) :
    (certificate.reindex r).traversalRelabel =
      certificate.traversalRelabel := by
  apply ext_fields
  · change
      ((certificate.reindex r).traversalVertices.filterMap
        (certificate.reindex r).formula?).toArray =
      (certificate.traversalVertices.filterMap certificate.formula?).toArray
    exact congrArg List.toArray (certificate.formulasAtTraversal_reindex r)
  · simp only [traversalRelabel, reindex_links]
    induction certificate.links with
    | nil => rfl
    | cons head tail ih =>
        simp only [List.map_cons, List.cons.injEq]
        exact ⟨certificate.linkRelabel_reindex_traversal r head, ih⟩
  · simp only [traversalRelabel, reindex_conclusions]
    induction certificate.conclusions with
    | nil => rfl
    | cons head tail ih =>
        simp only [List.map_cons, List.cons.injEq]
        exact ⟨by
          rw [certificate.traversalVertices_reindex,
            r.idxOf_map_forward], ih⟩

def natListLess : List Nat → List Nat → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | left :: leftRest, right :: rightRest =>
      if left < right then true
      else if right < left then false
      else natListLess leftRest rightRest

def insertLink (link : Link) : List Link → List Link
  | [] => [link]
  | head :: tail =>
      if natListLess link.sortKey head.sortKey then
        link :: head :: tail
      else
        head :: insertLink link tail

def sortLinks (links : List Link) : List Link :=
  links.foldr insertLink []

def insertNat (value : Nat) : List Nat → List Nat
  | [] => [value]
  | head :: tail =>
      if value < head then value :: head :: tail
      else head :: insertNat value tail

def sortNats (values : List Nat) : List Nat :=
  values.foldr insertNat []

/-- Canonical v0.2 normalization. Vertex numbers remain the formula-array
indices by contract; link order, conclusion order, and axiom orientation are
normalized. This is intentionally not graph-isomorphism canonicalization. -/
def canonicalize (certificate : Certificate) : Certificate :=
  { formulas := certificate.formulas
    links := certificate.links.map Link.canonicalize |> sortLinks
    conclusions := certificate.conclusions |> sortNats }

/-- A deterministic normal-form key for bounded vertex reindexing. It preserves
link order, conclusion order, tensor/par premise order, and axiom endpoint
order, exactly as `ReindexEquivalent` does. The theorem below proves invariance
under that relation. A converse/completeness theorem for structurally
well-formed certificates is intentionally a separate obligation. -/
def equivalenceCanonicalize (certificate : Certificate) : Certificate :=
  certificate.traversalRelabel

@[simp] theorem equivalenceCanonicalize_reindex (certificate : Certificate)
    (r : VertexRenaming certificate.formulas.size) :
    (certificate.reindex r).equivalenceCanonicalize =
      certificate.equivalenceCanonicalize := by
  simp [equivalenceCanonicalize]

theorem ReindexEquivalent.equivalenceCanonicalize_eq
    {left right : Certificate} (equivalent : left.ReindexEquivalent right) :
    left.equivalenceCanonicalize = right.equivalenceCanonicalize := by
  rcases equivalent with ⟨r, rfl⟩
  exact (left.equivalenceCanonicalize_reindex r).symm

theorem StructurallyWellFormed.equivalenceCanonicalize_reindexEquivalent
    {certificate : Certificate}
    (wellFormed : certificate.StructurallyWellFormed) :
    certificate.ReindexEquivalent certificate.equivalenceCanonicalize := by
  simpa [equivalenceCanonicalize] using
    wellFormed.traversalRelabel_reindexEquivalent

/-- For structurally well-formed certificates, the v0.3 certificate normal
form is a complete invariant for the exact order-preserving
`ReindexEquivalent` relation. -/
theorem reindexEquivalent_iff_equivalenceCanonicalize_eq
    {left right : Certificate}
    (leftWellFormed : left.StructurallyWellFormed)
    (rightWellFormed : right.StructurallyWellFormed) :
    left.ReindexEquivalent right ↔
      left.equivalenceCanonicalize = right.equivalenceCanonicalize := by
  constructor
  · exact fun equivalent => equivalent.equivalenceCanonicalize_eq
  · intro sameNormalForm
    have leftToNormal :=
      leftWellFormed.equivalenceCanonicalize_reindexEquivalent
    have normalToRight :=
      rightWellFormed.equivalenceCanonicalize_reindexEquivalent.symm
    rw [← sameNormalForm] at normalToRight
    exact leftToNormal.trans normalToRight

/-- Executable comparison of v0.3 certificate normal forms. Its correctness
theorem requires structural well-formedness, exactly the domain on which the
normal forms are proved to be in-class representatives. -/
def reindexEquivalent? (left right : Certificate) : Bool :=
  decide (left.equivalenceCanonicalize = right.equivalenceCanonicalize)

theorem reindexEquivalent?_eq_true_iff {left right : Certificate}
    (leftWellFormed : left.StructurallyWellFormed)
    (rightWellFormed : right.StructurallyWellFormed) :
    reindexEquivalent? left right = true ↔ left.ReindexEquivalent right := by
  rw [reindexEquivalent_iff_equivalenceCanonicalize_eq
    leftWellFormed rightWellFormed]
  simp [reindexEquivalent?]

/-- On checker-accepted inputs, the Boolean comparison decides exactly the
order-preserving bounded-reindex equivalence relation. -/
theorem reindexEquivalent?_eq_true_iff_of_check {left right : Certificate}
    (leftAccepted : left.check = true) (rightAccepted : right.check = true) :
    reindexEquivalent? left right = true ↔ left.ReindexEquivalent right :=
  reindexEquivalent?_eq_true_iff
    (left.check_sound_declarative leftAccepted).1
    (right.check_sound_declarative rightAccepted).1

theorem check_equivalenceCanonicalize (certificate : Certificate)
    (wellFormed : certificate.StructurallyWellFormed) :
    certificate.equivalenceCanonicalize.check = certificate.check :=
  wellFormed.equivalenceCanonicalize_reindexEquivalent.check_eq.symm

theorem equivalenceCanonicalize_check_of_check (certificate : Certificate)
    (accepted : certificate.check = true) :
    certificate.equivalenceCanonicalize.check = true := by
  rw [certificate.check_equivalenceCanonicalize
    (certificate.check_sound_declarative accepted).1]
  exact accepted

def formulaJson : Formula → Lean.Json
  | .atom name positive => Lean.Json.mkObj [
      ("kind", "atom"), ("name", name), ("positive", positive)]
  | .tensor left right => Lean.Json.mkObj [
      ("kind", "tensor"), ("left", formulaJson left),
      ("right", formulaJson right)]
  | .par left right => Lean.Json.mkObj [
      ("kind", "par"), ("left", formulaJson left),
      ("right", formulaJson right)]

def linkJson : Link → Lean.Json
  | .axiom left right => Lean.Json.mkObj [
      ("kind", "axiom"), ("left", left), ("right", right)]
  | .tensor left right conclusion => Lean.Json.mkObj [
      ("kind", "tensor"), ("left", left), ("right", right),
      ("conclusion", conclusion)]
  | .par left right conclusion => Lean.Json.mkObj [
      ("kind", "par"), ("left", left), ("right", right),
      ("conclusion", conclusion)]

/-- Versioned deterministic JSON value for a canonically normalized
certificate. -/
def canonicalJson (certificate : Certificate) : Lean.Json :=
  let normalized := certificate.canonicalize
  Lean.Json.mkObj [
    ("version", "0.2"),
    ("canonical", true),
    ("formulas", .arr (normalized.formulas.map formulaJson)),
    ("links", .arr (normalized.links.toArray.map linkJson)),
    ("conclusions", .arr (normalized.conclusions.toArray.map
      (fun value : Vertex => .num (Lean.JsonNumber.fromNat value))))]

/-- Compact v0.2 canonical JSON under fixed submitted occurrence numbering. -/
def canonicalString (certificate : Certificate) : String :=
  certificate.canonicalJson.compress

/-- Version 0.3 wire value. Vertex numbers are first normalized by
`equivalenceCanonicalize`, so every `ReindexEquivalent` certificate has the
same serialized representation. -/
def equivalenceCanonicalJson (certificate : Certificate) : Lean.Json :=
  let normalized := certificate.equivalenceCanonicalize
  Lean.Json.mkObj [
    ("version", "0.3"),
    ("canonical", true),
    ("canonicalization", "reindex-v1"),
    ("formulas", .arr (normalized.formulas.map formulaJson)),
    ("links", .arr (normalized.links.toArray.map linkJson)),
    ("conclusions", .arr (normalized.conclusions.toArray.map
      (fun value : Vertex => .num (Lean.JsonNumber.fromNat value))))]

/-- Compact v0.3 `reindex-v1` JSON key, invariant under the documented
order-preserving bounded vertex-renaming relation. -/
def equivalenceCanonicalString (certificate : Certificate) : String :=
  certificate.equivalenceCanonicalJson.compress

@[simp] theorem equivalenceCanonicalJson_reindex (certificate : Certificate)
    (r : VertexRenaming certificate.formulas.size) :
    (certificate.reindex r).equivalenceCanonicalJson =
      certificate.equivalenceCanonicalJson := by
  simp [equivalenceCanonicalJson]

@[simp] theorem equivalenceCanonicalString_reindex
    (certificate : Certificate)
    (r : VertexRenaming certificate.formulas.size) :
    (certificate.reindex r).equivalenceCanonicalString =
      certificate.equivalenceCanonicalString := by
  simp [equivalenceCanonicalString]

theorem ReindexEquivalent.equivalenceCanonicalString_eq
    {left right : Certificate} (equivalent : left.ReindexEquivalent right) :
    left.equivalenceCanonicalString = right.equivalenceCanonicalString := by
  rcases equivalent with ⟨r, rfl⟩
  exact (left.equivalenceCanonicalString_reindex r).symm

end Certificate

end ProofNetIR
