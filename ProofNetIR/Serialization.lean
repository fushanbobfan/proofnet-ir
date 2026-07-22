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

/-- Deterministic vertex discovery order for `ReindexEquivalent`. That
relation preserves conclusion and link order, so first occurrence is stable
under every admissible vertex renaming. -/
def traversalVertices (certificate : Certificate) : List Vertex :=
  (certificate.conclusions ++ certificate.links.flatMap Link.vertices).eraseDups

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
