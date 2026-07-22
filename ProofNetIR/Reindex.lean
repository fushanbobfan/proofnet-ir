import ProofNetIR.Certificate

namespace ProofNetIR

/-- A bijective renaming of natural-number vertices that preserves exactly the
vertices below `bound`. Vertices outside the certificate remain outside, so
renaming cannot turn a malformed out-of-bounds reference into a valid one. -/
structure VertexRenaming (bound : Nat) where
  forward : Vertex → Vertex
  inverse : Vertex → Vertex
  inverse_forward : ∀ vertex, inverse (forward vertex) = vertex
  forward_inverse : ∀ vertex, forward (inverse vertex) = vertex
  forward_lt_iff : ∀ vertex, forward vertex < bound ↔ vertex < bound

namespace VertexRenaming

@[simp] theorem inverse_lt_iff {bound : Nat}
    (r : VertexRenaming bound) (vertex : Vertex) :
    r.inverse vertex < bound ↔ vertex < bound := by
  simpa only [r.forward_inverse] using
    (r.forward_lt_iff (r.inverse vertex)).symm

theorem forward_injective {bound : Nat} (r : VertexRenaming bound) :
    Function.Injective r.forward := by
  intro left right same
  simpa only [r.inverse_forward] using congrArg r.inverse same

@[simp] theorem forward_eq_iff {bound : Nat} (r : VertexRenaming bound)
    (left right : Vertex) : r.forward left = r.forward right ↔ left = right :=
  ⟨fun same => r.forward_injective same, congrArg r.forward⟩

@[simp] theorem forward_bne {bound : Nat} (r : VertexRenaming bound)
    (left right : Vertex) :
    (r.forward left != r.forward right) = (left != right) := by
  apply Bool.eq_iff_iff.mpr
  simp only [bne_iff_ne]
  exact not_congr (r.forward_eq_iff left right)

@[simp] theorem forward_beq {bound : Nat} (r : VertexRenaming bound)
    (left right : Vertex) :
    (r.forward left == r.forward right) = (left == right) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  exact r.forward_eq_iff left right

@[simp] theorem contains_map_forward {bound : Nat}
    (r : VertexRenaming bound) (vertices : List Vertex) (vertex : Vertex) :
    (vertices.map r.forward).contains (r.forward vertex) =
      vertices.contains vertex := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.contains_iff_mem, List.mem_map]
  constructor
  · rintro ⟨original, membership, same⟩
    exact (r.forward_injective same).symm ▸ membership
  · intro membership
    exact ⟨vertex, membership, rfl⟩

@[simp] theorem all_map_forward_lt {bound : Nat}
    (r : VertexRenaming bound) (vertices : List Vertex) :
    (vertices.map r.forward).all (fun vertex => vertex < bound) =
      vertices.all (fun vertex => vertex < bound) := by
  induction vertices with
  | nil => rfl
  | cons head tail ih =>
      simp [ih, r.forward_lt_iff]

def symm {bound : Nat} (r : VertexRenaming bound) :
    VertexRenaming bound where
  forward := r.inverse
  inverse := r.forward
  inverse_forward := r.forward_inverse
  forward_inverse := r.inverse_forward
  forward_lt_iff := r.inverse_lt_iff

/-- Transport only the type-level bound along an equality. -/
def changeBound {oldBound newBound : Nat} (same : oldBound = newBound)
    (r : VertexRenaming oldBound) : VertexRenaming newBound := by
  subst newBound
  exact r

@[simp] theorem changeBound_forward {oldBound newBound : Nat}
    (same : oldBound = newBound) (r : VertexRenaming oldBound) :
    (r.changeBound same).forward = r.forward := by
  subst newBound
  rfl

@[simp] theorem changeBound_inverse {oldBound newBound : Nat}
    (same : oldBound = newBound) (r : VertexRenaming oldBound) :
    (r.changeBound same).inverse = r.inverse := by
  subst newBound
  rfl

def refl (bound : Nat) : VertexRenaming bound where
  forward := id
  inverse := id
  inverse_forward := by simp
  forward_inverse := by simp
  forward_lt_iff := by simp

/-- Swap two in-bounds vertices and fix every other natural number. -/
def swap (bound left right : Nat) (leftInBounds : left < bound)
    (rightInBounds : right < bound) : VertexRenaming bound where
  forward vertex :=
    if vertex = left then right else if vertex = right then left else vertex
  inverse vertex :=
    if vertex = left then right else if vertex = right then left else vertex
  inverse_forward := by
    intro vertex
    by_cases same : left = right
    · by_cases atLeft : vertex = left
      · simp [atLeft, same]
      · have atRight : vertex ≠ right := fun equality =>
          atLeft (Eq.trans equality (Eq.symm same))
        simp [atLeft, atRight]
    · have different : right ≠ left := fun equality => same (Eq.symm equality)
      by_cases atLeft : vertex = left
      · subst vertex
        simp [different]
      · by_cases atRight : vertex = right
        · subst vertex
          simp [different]
        · simp [atLeft, atRight]
  forward_inverse := by
    intro vertex
    by_cases same : left = right
    · by_cases atLeft : vertex = left
      · simp [atLeft, same]
      · have atRight : vertex ≠ right := fun equality =>
          atLeft (Eq.trans equality (Eq.symm same))
        simp [atLeft, atRight]
    · have different : right ≠ left := fun equality => same (Eq.symm equality)
      by_cases atLeft : vertex = left
      · subst vertex
        simp [different]
      · by_cases atRight : vertex = right
        · subst vertex
          simp [different]
        · simp [atLeft, atRight]
  forward_lt_iff := by
    intro vertex
    by_cases atLeft : vertex = left
    · subst vertex
      simp [rightInBounds, leftInBounds]
    · by_cases atRight : vertex = right
      · subst vertex
        simp [atLeft, leftInBounds, rightInBounds]
      · simp [atLeft, atRight]

@[simp] theorem symm_forward {bound : Nat}
    (r : VertexRenaming bound) :
    r.symm.forward = r.inverse := rfl

@[simp] theorem symm_inverse {bound : Nat}
    (r : VertexRenaming bound) :
    r.symm.inverse = r.forward := rfl

end VertexRenaming

namespace Link

/-- Rename every occurrence reference while preserving link kind and ordered
tensor/par premises. -/
def reindex {bound : Nat} (r : VertexRenaming bound) : Link → Link
  | .axiom left right => .axiom (r.forward left) (r.forward right)
  | .tensor left right conclusion =>
      .tensor (r.forward left) (r.forward right)
        (r.forward conclusion)
  | .par left right conclusion =>
      .par (r.forward left) (r.forward right)
        (r.forward conclusion)

@[simp] theorem reindex_symm {bound : Nat}
    (r : VertexRenaming bound) (link : Link) :
    (link.reindex r).reindex r.symm = link := by
  cases link <;> simp [reindex, VertexRenaming.symm,
    r.inverse_forward]

@[simp] theorem produces_reindex {bound : Nat}
    (r : VertexRenaming bound) (vertex : Vertex) (link : Link) :
    (link.reindex r).produces (r.forward vertex) = link.produces vertex := by
  cases link <;> simp [reindex, produces, r.forward_beq]

@[simp] theorem containsAxiomEndpoint_reindex {bound : Nat}
    (r : VertexRenaming bound) (vertex : Vertex) (link : Link) :
    (link.reindex r).containsAxiomEndpoint (r.forward vertex) =
      link.containsAxiomEndpoint vertex := by
  cases link <;>
    simp [reindex, containsAxiomEndpoint, r.forward_beq]

@[simp] theorem usesAsPremise_reindex {bound : Nat}
    (r : VertexRenaming bound) (vertex : Vertex) (link : Link) :
    (link.reindex r).usesAsPremise (r.forward vertex) =
      link.usesAsPremise vertex := by
  cases link <;>
    simp [reindex, usesAsPremise, premises]

end Link

namespace Certificate

theorem ext_fields {left right : Certificate}
    (formulas : left.formulas = right.formulas)
    (links : left.links = right.links)
    (conclusions : left.conclusions = right.conclusions) : left = right := by
  cases left
  cases right
  simp_all

/-- Transport a certificate along a bijective vertex renaming. The formula at
new vertex `forward old` is definitionally copied from `old`; link and
conclusion list order are deliberately preserved. -/
def reindex (certificate : Certificate)
    (r : VertexRenaming certificate.formulas.size) : Certificate where
  formulas := Array.ofFn fun vertex =>
    certificate.formulas[r.inverse vertex.val]'(
      (r.inverse_lt_iff vertex.val).mpr vertex.isLt)
  links := certificate.links.map (Link.reindex r)
  conclusions := certificate.conclusions.map r.forward

@[simp] theorem reindex_formulas_size (certificate : Certificate)
    (r : VertexRenaming certificate.formulas.size) :
    (certificate.reindex r).formulas.size =
      certificate.formulas.size := by
  simp [reindex]

@[simp] theorem reindex_links (certificate : Certificate)
    (r : VertexRenaming certificate.formulas.size) :
    (certificate.reindex r).links =
      certificate.links.map (Link.reindex r) := rfl

@[simp] theorem reindex_conclusions (certificate : Certificate)
    (r : VertexRenaming certificate.formulas.size) :
    (certificate.reindex r).conclusions =
      certificate.conclusions.map r.forward := rfl

/-- Formula lookup commutes with renaming, including for malformed
out-of-bounds vertices. -/
theorem reindex_formula?_forward (certificate : Certificate)
    (r : VertexRenaming certificate.formulas.size) (vertex : Vertex) :
    (certificate.reindex r).formula? (r.forward vertex) =
      certificate.formula? vertex := by
  by_cases inBounds : vertex < certificate.formulas.size
  · have renamedInBounds :
        r.forward vertex < (certificate.reindex r).formulas.size :=
      by simpa using (r.forward_lt_iff vertex).mpr inBounds
    rw [formula?, Array.getElem?_eq_getElem renamedInBounds,
      formula?, Array.getElem?_eq_getElem inBounds]
    simp [reindex, r.inverse_forward]
  · have renamedOutOfBounds :
        (certificate.reindex r).formulas.size ≤
          r.forward vertex := by
      simp only [reindex_formulas_size]
      exact Nat.le_of_not_gt fun renamedInBounds =>
        inBounds ((r.forward_lt_iff vertex).mp renamedInBounds)
    have originalOutOfBounds : certificate.formulas.size ≤ vertex :=
      Nat.le_of_not_gt inBounds
    rw [formula?, Array.getElem?_eq_none_iff.mpr renamedOutOfBounds,
      formula?, Array.getElem?_eq_none_iff.mpr originalOutOfBounds]

/-- Local formula/link typing is invariant under any bounded bijective vertex
renaming. -/
theorem linkLocallyWellFormed_reindex (certificate : Certificate)
    (r : VertexRenaming certificate.formulas.size) (link : Link) :
    (certificate.reindex r).linkLocallyWellFormed (link.reindex r) =
      certificate.linkLocallyWellFormed link := by
  cases link <;>
    simp [linkLocallyWellFormed, Link.reindex, inBounds,
      reindex_formula?_forward, r.forward_lt_iff, r.forward_bne]

theorem linkWellFormed_reindex_iff (certificate : Certificate)
    (r : VertexRenaming certificate.formulas.size) (link : Link) :
    (certificate.reindex r).LinkWellFormed (link.reindex r) ↔
      certificate.LinkWellFormed link := by
  rw [← (certificate.reindex r).linkLocallyWellFormed_iff,
    certificate.linkLocallyWellFormed_reindex,
    certificate.linkLocallyWellFormed_iff]

@[simp] theorem axiomCount_reindex (certificate : Certificate)
    (r : VertexRenaming certificate.formulas.size) (vertex : Vertex) :
    (certificate.reindex r).axiomCount (r.forward vertex) =
      certificate.axiomCount vertex := by
  simp only [axiomCount, reindex_links]
  induction certificate.links with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.map_cons]
      rw [List.filter_cons, List.filter_cons]
      rw [Link.containsAxiomEndpoint_reindex]
      cases endpoint : head.containsAxiomEndpoint vertex <;>
        simp [ih]

@[simp] theorem producerCount_reindex (certificate : Certificate)
    (r : VertexRenaming certificate.formulas.size) (vertex : Vertex) :
    (certificate.reindex r).producerCount (r.forward vertex) =
      certificate.producerCount vertex := by
  simp only [producerCount, reindex_links]
  induction certificate.links with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.map_cons]
      rw [List.filter_cons, List.filter_cons]
      rw [Link.produces_reindex]
      cases produces : head.produces vertex <;>
        simp [ih]

@[simp] theorem parentUseCount_reindex (certificate : Certificate)
    (r : VertexRenaming certificate.formulas.size) (vertex : Vertex) :
    (certificate.reindex r).parentUseCount (r.forward vertex) =
      certificate.parentUseCount vertex := by
  simp only [parentUseCount, reindex_links]
  induction certificate.links with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.map_cons]
      rw [List.filter_cons, List.filter_cons]
      rw [Link.usesAsPremise_reindex]
      cases premise : head.usesAsPremise vertex <;>
        simp [ih]

@[simp] theorem nodeWellFormed_reindex (certificate : Certificate)
    (r : VertexRenaming certificate.formulas.size) (vertex : Vertex) :
    (certificate.reindex r).nodeWellFormed (r.forward vertex) =
      certificate.nodeWellFormed vertex := by
  simp [nodeWellFormed, reindex_formula?_forward]

theorem nodeWellFormed_reindex_iff (certificate : Certificate)
    (r : VertexRenaming certificate.formulas.size) (vertex : Vertex) :
    (certificate.reindex r).NodeWellFormed (r.forward vertex) ↔
      certificate.NodeWellFormed vertex := by
  rw [← (certificate.reindex r).nodeWellFormed_iff,
    certificate.nodeWellFormed_reindex,
    certificate.nodeWellFormed_iff]

/-- The inverse renaming, transported to the definitionally new formula-array
size produced by `reindex`. -/
def inverseReindexing (certificate : Certificate)
    (r : VertexRenaming certificate.formulas.size) :
    VertexRenaming (certificate.reindex r).formulas.size :=
  r.symm.changeBound (certificate.reindex_formulas_size r).symm

@[simp] theorem inverseReindexing_forward (certificate : Certificate)
    (r : VertexRenaming certificate.formulas.size) :
    (certificate.inverseReindexing r).forward = r.inverse := by
  simp [inverseReindexing]

@[simp] theorem inverseReindexing_inverse (certificate : Certificate)
    (r : VertexRenaming certificate.formulas.size) :
    (certificate.inverseReindexing r).inverse = r.forward := by
  simp [inverseReindexing]

@[simp] theorem link_reindex_inverseReindexing (certificate : Certificate)
    (r : VertexRenaming certificate.formulas.size) (link : Link) :
    (link.reindex r).reindex (certificate.inverseReindexing r) = link := by
  cases link <;>
    simp [Link.reindex, inverseReindexing, r.inverse_forward]

/-- Reindexing is lossless: applying the transported inverse recovers the
literal original certificate, including link and conclusion order. -/
theorem reindex_inverse (certificate : Certificate)
    (r : VertexRenaming certificate.formulas.size) :
    (certificate.reindex r).reindex (certificate.inverseReindexing r) =
      certificate := by
  apply ext_fields
  · apply Array.ext
    · simp
    · intro vertex leftInBounds rightInBounds
      simp [reindex, inverseReindexing, r.inverse_forward]
  · change List.map (Link.reindex (certificate.inverseReindexing r))
      (List.map (Link.reindex r) certificate.links) = certificate.links
    induction certificate.links with
    | nil => rfl
    | cons head tail ih =>
        simp only [List.map_cons]
        rw [certificate.link_reindex_inverseReindexing r head, ih]
  · simp [reindex, inverseReindexing, List.map_map, Function.comp_def,
      r.inverse_forward]

end Certificate

end ProofNetIR
