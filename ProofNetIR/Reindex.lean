import ProofNetIR.Checker

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

@[simp] theorem idxOf_map_forward {bound : Nat}
    (r : VertexRenaming bound) (vertices : List Vertex) (vertex : Vertex) :
    (vertices.map r.forward).idxOf (r.forward vertex) =
      vertices.idxOf vertex := by
  induction vertices with
  | nil => rfl
  | cons head tail ih =>
      simp [List.idxOf_cons, r.forward_beq, ih]

theorem getElem_idxOf (vertices : List Vertex) (vertex : Vertex)
    (member : vertex ∈ vertices) :
    vertices[vertices.idxOf vertex]'(
      vertices.idxOf_lt_length_of_mem member) = vertex := by
  induction vertices with
  | nil => simp at member
  | cons head tail ih =>
      by_cases same : head = vertex
      · subst head
        simp
      · have memberTail : vertex ∈ tail := by
          simp only [List.mem_cons] at member
          exact member.resolve_left (fun atHead => same atHead.symm)
        have unequal : (head == vertex) = false := by simp [same]
        simp [List.idxOf_cons, unequal, ih memberTail]

theorem idxOf_getElem_of_nodup (vertices : List Vertex)
    (nodup : vertices.Nodup) (index : Nat) (inBounds : index < vertices.length) :
    vertices.idxOf vertices[index] = index := by
  have member : vertices[index] ∈ vertices := List.getElem_mem inBounds
  apply (List.getElem_inj nodup).mp
  exact getElem_idxOf vertices vertices[index] member

/-- `eraseDups` really produces a duplicate-free list. This basic fact is
proved here because the Lean core verification API currently exposes only the
membership theorem. -/
theorem eraseDups_nodup (vertices : List Vertex) :
    vertices.eraseDups.Nodup := by
  match vertices with
  | [] => simp
  | head :: tail =>
      rw [List.eraseDups_cons, List.nodup_cons]
      exact ⟨by simp, eraseDups_nodup
        (tail.filter fun vertex => !vertex == head)⟩
termination_by vertices.length
decreasing_by
  exact Nat.lt_succ_of_le (List.length_filter_le _ _)

theorem perm_range_of_nodup_complete (bound : Nat) (order : List Vertex)
    (nodup : order.Nodup)
    (complete : ∀ vertex, vertex < bound ↔ vertex ∈ order) :
    order.Perm (List.range bound) := by
  rw [List.perm_iff_count]
  intro vertex
  rw [nodup.count, List.nodup_range.count]
  simp [complete vertex]

theorem length_eq_of_nodup_complete (bound : Nat) (order : List Vertex)
    (nodup : order.Nodup)
    (complete : ∀ vertex, vertex < bound ↔ vertex ∈ order) :
    order.length = bound := by
  have permutation := perm_range_of_nodup_complete bound order nodup complete
  simpa using permutation.length_eq

/-- Turn a duplicate-free enumeration of exactly the in-bounds vertices into
a total bounded vertex renaming. Out-of-bounds naturals are fixed. -/
def ofOrder (bound : Nat) (order : List Vertex)
    (length_eq : order.length = bound) (nodup : order.Nodup)
    (complete : ∀ vertex, vertex < bound ↔ vertex ∈ order) :
    VertexRenaming bound where
  forward vertex := if vertex < bound then order.idxOf vertex else vertex
  inverse vertex := if inBounds : vertex < bound then
      order[vertex]'(by simpa [length_eq] using inBounds)
    else vertex
  inverse_forward := by
    intro vertex
    by_cases inBounds : vertex < bound
    · have member : vertex ∈ order := (complete vertex).mp inBounds
      have indexInOrder : order.idxOf vertex < order.length :=
        order.idxOf_lt_length_of_mem member
      have indexInBounds : order.idxOf vertex < bound := by
        simpa [length_eq] using indexInOrder
      simp only [inBounds, if_pos, indexInBounds, dif_pos]
      exact getElem_idxOf order vertex member
    · simp [inBounds]
  forward_inverse := by
    intro vertex
    by_cases inBounds : vertex < bound
    · have indexInOrder : vertex < order.length := by
        simpa [length_eq] using inBounds
      have member : order[vertex] ∈ order := List.getElem_mem indexInOrder
      have valueInBounds : order[vertex] < bound :=
        (complete order[vertex]).mpr member
      simp only [inBounds, dif_pos, valueInBounds, if_pos]
      exact idxOf_getElem_of_nodup order nodup vertex indexInOrder
    · simp [inBounds]
  forward_lt_iff := by
    intro vertex
    by_cases inBounds : vertex < bound
    · have member : vertex ∈ order := (complete vertex).mp inBounds
      have indexInOrder : order.idxOf vertex < order.length :=
        order.idxOf_lt_length_of_mem member
      have indexInBounds : order.idxOf vertex < bound := by
        simpa [length_eq] using indexInOrder
      simp [inBounds, indexInBounds]
    · simp [inBounds]

@[simp] theorem ofOrder_forward_inBounds (bound : Nat) (order : List Vertex)
    (length_eq : order.length = bound) (nodup : order.Nodup)
    (complete : ∀ vertex, vertex < bound ↔ vertex ∈ order)
    {vertex : Vertex} (inBounds : vertex < bound) :
    (ofOrder bound order length_eq nodup complete).forward vertex =
      order.idxOf vertex := by
  simp [ofOrder, inBounds]

@[simp] theorem ofOrder_inverse_inBounds (bound : Nat) (order : List Vertex)
    (length_eq : order.length = bound) (nodup : order.Nodup)
    (complete : ∀ vertex, vertex < bound ↔ vertex ∈ order)
    {vertex : Vertex} (inBounds : vertex < bound) :
    (ofOrder bound order length_eq nodup complete).inverse vertex =
      order[vertex]'(by simpa [length_eq] using inBounds) := by
  simp [ofOrder, inBounds]

@[simp] theorem all_map_forward_lt {bound : Nat}
    (r : VertexRenaming bound) (vertices : List Vertex) :
    (vertices.map r.forward).all (fun vertex => vertex < bound) =
      vertices.all (fun vertex => vertex < bound) := by
  induction vertices with
  | nil => rfl
  | cons head tail ih =>
      simp [ih, r.forward_lt_iff]

/-- Deduplication commutes with an injective vertex renaming. This theorem is
stronger than the length fact needed by structural validation and records the
preserved conclusion order explicitly. -/
@[simp] theorem eraseDups_map_forward {bound : Nat}
    (r : VertexRenaming bound) (vertices : List Vertex) :
    (vertices.map r.forward).eraseDups =
      vertices.eraseDups.map r.forward := by
  match vertices with
  | [] => rfl
  | head :: tail =>
      rw [List.map_cons, List.eraseDups_cons, List.eraseDups_cons,
        List.filter_map]
      have predicates :
          ((fun vertex => !vertex == r.forward head) ∘ r.forward) =
            (fun vertex => !vertex == head) := by
        funext vertex
        simp
      rw [predicates]
      rw [eraseDups_map_forward r
        (tail.filter fun vertex => !vertex == head)]
      rfl
termination_by vertices.length
decreasing_by
  exact Nat.lt_succ_of_le (List.length_filter_le _ _)

def symm {bound : Nat} (r : VertexRenaming bound) :
    VertexRenaming bound where
  forward := r.inverse
  inverse := r.forward
  inverse_forward := r.forward_inverse
  forward_inverse := r.inverse_forward
  forward_lt_iff := r.inverse_lt_iff

def trans {bound : Nat} (first second : VertexRenaming bound) :
    VertexRenaming bound where
  forward := second.forward ∘ first.forward
  inverse := first.inverse ∘ second.inverse
  inverse_forward := by
    intro vertex
    simp [first.inverse_forward,
      second.inverse_forward]
  forward_inverse := by
    intro vertex
    simp [first.forward_inverse,
      second.forward_inverse]
  forward_lt_iff := by
    intro vertex
    simp [second.forward_lt_iff,
      first.forward_lt_iff]

@[simp] theorem trans_forward {bound : Nat}
    (first second : VertexRenaming bound) :
    (first.trans second).forward = second.forward ∘ first.forward := rfl

@[simp] theorem trans_inverse {bound : Nat}
    (first second : VertexRenaming bound) :
    (first.trans second).inverse = first.inverse ∘ second.inverse := rfl

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

/-- Extend a bounded renaming by fixing one newly appended final vertex.
Only the old in-bounds action is retained; all vertices above the new bound
are fixed, independently of how the original total bijection acted there. -/
def extendLast {oldBound : Nat} (r : VertexRenaming oldBound) :
    VertexRenaming (oldBound + 1) where
  forward vertex :=
    if oldVertex : vertex < oldBound then r.forward vertex
    else if vertex = oldBound then oldBound else vertex
  inverse vertex :=
    if oldVertex : vertex < oldBound then r.inverse vertex
    else if vertex = oldBound then oldBound else vertex
  inverse_forward := by
    intro vertex
    by_cases oldVertex : vertex < oldBound
    · have mappedOld : r.forward vertex < oldBound :=
        (r.forward_lt_iff vertex).mpr oldVertex
      simp [oldVertex, mappedOld, r.inverse_forward]
    · by_cases atLast : vertex = oldBound
      · subst vertex
        simp
      · simp [oldVertex, atLast]
  forward_inverse := by
    intro vertex
    by_cases oldVertex : vertex < oldBound
    · have mappedOld : r.inverse vertex < oldBound :=
        (r.inverse_lt_iff vertex).mpr oldVertex
      simp [oldVertex, mappedOld, r.forward_inverse]
    · by_cases atLast : vertex = oldBound
      · subst vertex
        simp
      · simp [oldVertex, atLast]
  forward_lt_iff := by
    intro vertex
    by_cases oldVertex : vertex < oldBound
    · have mappedOld : r.forward vertex < oldBound :=
        (r.forward_lt_iff vertex).mpr oldVertex
      simp [oldVertex, Nat.lt_succ_of_lt oldVertex,
        Nat.lt_succ_of_lt mappedOld]
    · by_cases atLast : vertex = oldBound
      · subst vertex
        simp
      · have outside : ¬vertex < oldBound + 1 := by
          intro inBounds
          have atMost : vertex ≤ oldBound :=
            Nat.lt_succ_iff.mp (by simpa using inBounds)
          exact (Nat.lt_or_eq_of_le atMost).elim oldVertex atLast
        simp [oldVertex, atLast, outside]

@[simp] theorem extendLast_forward_old {oldBound : Nat}
    (r : VertexRenaming oldBound) {vertex : Vertex}
    (oldVertex : vertex < oldBound) :
    r.extendLast.forward vertex = r.forward vertex := by
  simp [extendLast, oldVertex]

@[simp] theorem extendLast_forward_last {oldBound : Nat}
    (r : VertexRenaming oldBound) :
    r.extendLast.forward oldBound = oldBound := by
  simp [extendLast]

@[simp] theorem extendLast_inverse_old {oldBound : Nat}
    (r : VertexRenaming oldBound) {vertex : Vertex}
    (oldVertex : vertex < oldBound) :
    r.extendLast.inverse vertex = r.inverse vertex := by
  simp [extendLast, oldVertex]

@[simp] theorem extendLast_inverse_last {oldBound : Nat}
    (r : VertexRenaming oldBound) :
    r.extendLast.inverse oldBound = oldBound := by
  simp [extendLast]

/-- Extend an `oldBound`-vertex numbering by one final source vertex and move
that new vertex to `removed` in the target numbering. Existing source
vertices below `removed` stay fixed; the rest shift up by one. -/
def insertLastAt (oldBound removed : Nat)
    (removedInBounds : removed < oldBound + 1) :
    VertexRenaming (oldBound + 1) where
  forward vertex :=
    if oldVertex : vertex < oldBound then
      if vertex < removed then vertex else vertex + 1
    else if vertex = oldBound then removed else vertex
  inverse vertex :=
    if targetVertex : vertex < oldBound + 1 then
      if vertex = removed then oldBound
      else if vertex < removed then vertex else vertex - 1
    else vertex
  inverse_forward := by
    intro vertex
    have removedLe : removed ≤ oldBound :=
      Nat.lt_succ_iff.mp (by simpa using removedInBounds)
    by_cases oldVertex : vertex < oldBound
    · by_cases before : vertex < removed
      · have targetVertex : vertex < oldBound + 1 := by
          exact Nat.lt_succ_of_lt oldVertex
        have different : vertex ≠ removed := Nat.ne_of_lt before
        simp [oldVertex, before, targetVertex, different]
      · have targetVertex : vertex + 1 < oldBound + 1 :=
          Nat.add_lt_add_right oldVertex 1
        have different : vertex + 1 ≠ removed := by
          intro same
          apply before
          calc
            vertex < vertex + 1 := Nat.lt_succ_self vertex
            _ = removed := same
        have notBefore : ¬vertex + 1 < removed := by
          intro shiftedBefore
          exact before (Nat.lt_trans (Nat.lt_succ_self vertex) shiftedBefore)
        simp [oldVertex, before, targetVertex, different, notBefore]
    · by_cases atLast : vertex = oldBound
      · subst vertex
        simp [removedInBounds]
      · have outside : ¬vertex < oldBound + 1 := by
          intro inBounds
          have atMost : vertex ≤ oldBound :=
            Nat.lt_succ_iff.mp (by simpa using inBounds)
          exact (Nat.lt_or_eq_of_le atMost).elim oldVertex atLast
        simp [oldVertex, atLast, outside]
  forward_inverse := by
    intro vertex
    have removedLe : removed ≤ oldBound :=
      Nat.lt_succ_iff.mp (by simpa using removedInBounds)
    by_cases targetVertex : vertex < oldBound + 1
    · by_cases inserted : vertex = removed
      · subst vertex
        simp [removedInBounds]
      · by_cases before : vertex < removed
        · have oldVertex : vertex < oldBound :=
            Nat.lt_of_lt_of_le before removedLe
          simp [targetVertex, inserted, before, oldVertex]
        · have positive : 0 < vertex := by
            apply Nat.pos_of_ne_zero
            intro zero
            subst vertex
            apply inserted
            exact (Nat.eq_zero_of_not_pos before).symm
          have atMost : vertex ≤ oldBound :=
            Nat.lt_succ_iff.mp (by simpa using targetVertex)
          have oldVertex : vertex - 1 < oldBound :=
            Nat.lt_of_lt_of_le (Nat.sub_one_lt (Nat.ne_zero_of_lt positive)) atMost
          have removedLt : removed < vertex :=
            Nat.lt_of_le_of_ne (Nat.le_of_not_gt before)
              (fun same => inserted same.symm)
          have shiftedNotBefore : ¬vertex - 1 < removed :=
            Nat.not_lt_of_ge (Nat.le_sub_one_of_lt removedLt)
          have restore : vertex - 1 + 1 = vertex :=
            Nat.sub_add_cancel positive
          simp [targetVertex, inserted, before, oldVertex,
            shiftedNotBefore, restore]
    · have oldVertex : ¬vertex < oldBound := by
        exact fun inOldBounds => targetVertex (Nat.lt_succ_of_lt inOldBounds)
      have notLast : vertex ≠ oldBound := by
        intro atLast
        subst vertex
        exact targetVertex (Nat.lt_succ_self oldBound)
      simp [targetVertex, oldVertex, notLast]
  forward_lt_iff := by
    intro vertex
    have removedLe : removed ≤ oldBound :=
      Nat.lt_succ_iff.mp (by simpa using removedInBounds)
    by_cases oldVertex : vertex < oldBound
    · by_cases before : vertex < removed
      · simp [oldVertex, before]
      · simp [oldVertex, before, Nat.lt_succ_of_lt oldVertex,
          Nat.add_lt_add_iff_right]
    · by_cases atLast : vertex = oldBound
      · subst vertex
        simp [removedInBounds]
      · simp [oldVertex, atLast]

@[simp] theorem insertLastAt_forward_old
    (oldBound removed : Nat) (removedInBounds : removed < oldBound + 1)
    {vertex : Vertex} (oldVertex : vertex < oldBound) :
    (insertLastAt oldBound removed removedInBounds).forward vertex =
      if vertex < removed then vertex else vertex + 1 := by
  simp [insertLastAt, oldVertex]

@[simp] theorem insertLastAt_forward_last
    (oldBound removed : Nat) (removedInBounds : removed < oldBound + 1) :
    (insertLastAt oldBound removed removedInBounds).forward oldBound =
      removed := by
  simp [insertLastAt]

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

/-- Extending a renaming by a new final occurrence does not change the action
on a link whose endpoints all belong to the old occurrence interval. -/
theorem reindex_extendLast {bound : Nat} (r : VertexRenaming bound)
    (link : Link)
    (inBounds : ∀ vertex ∈ link.vertices, vertex < bound) :
    link.reindex r.extendLast = link.reindex r := by
  cases link with
  | «axiom» left right =>
      have leftBound := inBounds left (by simp [vertices])
      have rightBound := inBounds right (by simp [vertices])
      simp [reindex, leftBound, rightBound]
  | tensor left right conclusion =>
      have leftBound := inBounds left (by simp [vertices])
      have rightBound := inBounds right (by simp [vertices])
      have conclusionBound := inBounds conclusion (by simp [vertices])
      simp [reindex, leftBound, rightBound, conclusionBound]
  | par left right conclusion =>
      have leftBound := inBounds left (by simp [vertices])
      have rightBound := inBounds right (by simp [vertices])
      have conclusionBound := inBounds conclusion (by simp [vertices])
      simp [reindex, leftBound, rightBound, conclusionBound]

@[simp] theorem vertices_reindex {bound : Nat}
    (r : VertexRenaming bound) (link : Link) :
    (link.reindex r).vertices = link.vertices.map r.forward := by
  cases link <;> simp [reindex, vertices]

@[simp] theorem reindex_symm {bound : Nat}
    (r : VertexRenaming bound) (link : Link) :
    (link.reindex r).reindex r.symm = link := by
  cases link <;> simp [reindex, VertexRenaming.symm,
    r.inverse_forward]

@[simp] theorem reindex_trans {bound : Nat}
    (first second : VertexRenaming bound) (link : Link) :
    (link.reindex first).reindex second =
      link.reindex (first.trans second) := by
  cases link <;>
    simp [reindex, VertexRenaming.trans, Function.comp_def]

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

namespace Edge

def reindex {bound : Nat} (r : VertexRenaming bound) (edge : Edge) : Edge :=
  { first := r.forward edge.first, second := r.forward edge.second }

@[simp] theorem reindex_first {bound : Nat} (r : VertexRenaming bound)
    (edge : Edge) : (edge.reindex r).first = r.forward edge.first := rfl

@[simp] theorem reindex_second {bound : Nat} (r : VertexRenaming bound)
    (edge : Edge) : (edge.reindex r).second = r.forward edge.second := rfl

@[simp] theorem reindex_symm {bound : Nat} (r : VertexRenaming bound)
    (edge : Edge) : (edge.reindex r).reindex r.symm = edge := by
  cases edge
  simp [reindex, VertexRenaming.symm, r.inverse_forward]

def reindexPair {bound : Nat} (r : VertexRenaming bound)
    (choice : Edge × Edge) : Edge × Edge :=
  (choice.1.reindex r, choice.2.reindex r)

@[simp] theorem reindexPair_symm {bound : Nat}
    (r : VertexRenaming bound) (choice : Edge × Edge) :
    Edge.reindexPair r.symm (Edge.reindexPair r choice) = choice := by
  rcases choice with ⟨left, right⟩
  simp [reindexPair]

end Edge

namespace Graph

def reindex (graph : Graph)
    (r : VertexRenaming graph.vertexCount) : Graph where
  vertexCount := graph.vertexCount
  edges := graph.edges.map (Edge.reindex r)

@[simp] theorem reindex_vertexCount (graph : Graph)
    (r : VertexRenaming graph.vertexCount) :
    (graph.reindex r).vertexCount = graph.vertexCount := rfl

@[simp] theorem reindex_edges (graph : Graph)
    (r : VertexRenaming graph.vertexCount) :
    (graph.reindex r).edges = graph.edges.map (Edge.reindex r) := rfl

@[simp] theorem reindex_symm (graph : Graph)
    (r : VertexRenaming graph.vertexCount) :
    (graph.reindex r).reindex r.symm = graph := by
  cases graph with
  | mk vertexCount edges =>
      simp [reindex, List.map_map, Function.comp_def]

namespace DirectedEdge

/-- Transport an exact oriented edge occurrence through a vertex renaming.
The stored-list index and orientation are unchanged; only the edge endpoints
are renamed. -/
def reindex {graph : Graph}
    (directed : graph.DirectedEdge)
    (r : VertexRenaming graph.vertexCount) :
    (graph.reindex r).DirectedEdge where
  index := directed.index
  edge := directed.edge.reindex r
  lookup := by
    simp [Graph.reindex, directed.lookup]
  forward := directed.forward

@[simp] theorem reindex_index {graph : Graph}
    (directed : graph.DirectedEdge)
    (r : VertexRenaming graph.vertexCount) :
    (directed.reindex r).index = directed.index := rfl

@[simp] theorem reindex_source {graph : Graph}
    (directed : graph.DirectedEdge)
    (r : VertexRenaming graph.vertexCount) :
    (directed.reindex r).source = r.forward directed.source := by
  rcases directed with ⟨index, edge, lookup, forward⟩
  cases forward <;> rfl

@[simp] theorem reindex_target {graph : Graph}
    (directed : graph.DirectedEdge)
    (r : VertexRenaming graph.vertexCount) :
    (directed.reindex r).target = r.forward directed.target := by
  rcases directed with ⟨index, edge, lookup, forward⟩
  cases forward <;> rfl

end DirectedEdge

theorem adjacent_reindex_iff (graph : Graph)
    (r : VertexRenaming graph.vertexCount) (left right : Vertex) :
    (graph.reindex r).Adjacent (r.forward left) (r.forward right) ↔
      graph.Adjacent left right := by
  constructor
  · rintro ⟨renamedEdge, membership, direction⟩
    rcases List.mem_map.mp membership with ⟨edge, edgeMembership, same⟩
    subst renamedEdge
    refine ⟨edge, edgeMembership, ?_⟩
    rcases direction with forward | backward
    · exact .inl ⟨r.forward_injective forward.1,
        r.forward_injective forward.2⟩
    · exact .inr ⟨r.forward_injective backward.1,
        r.forward_injective backward.2⟩
  · rintro ⟨edge, edgeMembership, direction⟩
    refine ⟨edge.reindex r, List.mem_map.mpr ⟨edge, edgeMembership, rfl⟩, ?_⟩
    rcases direction with forward | backward
    · exact .inl ⟨congrArg r.forward forward.1,
        congrArg r.forward forward.2⟩
    · exact .inr ⟨congrArg r.forward backward.1,
        congrArg r.forward backward.2⟩

theorem adjacent_unreindex_iff (graph : Graph)
    (r : VertexRenaming graph.vertexCount) (left right : Vertex) :
    (graph.reindex r).Adjacent left right ↔
      graph.Adjacent (r.inverse left) (r.inverse right) := by
  simpa only [r.forward_inverse] using
    graph.adjacent_reindex_iff r (r.inverse left) (r.inverse right)

namespace Walk

theorem trans {graph : Graph} {start middle finish : Vertex}
    (first : graph.Walk start middle) (second : graph.Walk middle finish) :
    graph.Walk start finish := by
  induction second with
  | refl => exact first
  | step prior adjacency ih => exact .step ih adjacency

theorem reverse {graph : Graph} {start finish : Vertex}
    (walk : graph.Walk start finish) : graph.Walk finish start := by
  induction walk with
  | refl => exact .refl start
  | @step middle finish prior adjacency ih =>
      have backward : graph.Adjacent finish middle := by
        rcases adjacency with ⟨edge, membership, direction⟩
        exact ⟨edge, membership, direction.elim .inr .inl⟩
      exact (Graph.Walk.step (Graph.Walk.refl finish) backward).trans ih

theorem reindex {graph : Graph} {start finish : Vertex}
    (r : VertexRenaming graph.vertexCount)
    (walk : graph.Walk start finish) :
    (graph.reindex r).Walk (r.forward start) (r.forward finish) := by
  induction walk with
  | refl => exact .refl (r.forward start)
  | step prior adjacency ih =>
      exact .step ih ((graph.adjacent_reindex_iff r _ _).mpr adjacency)

theorem unreindex {graph : Graph} {start finish : Vertex}
    (r : VertexRenaming graph.vertexCount)
    (walk : (graph.reindex r).Walk start finish) :
    graph.Walk (r.inverse start) (r.inverse finish) := by
  induction walk with
  | refl => exact .refl (r.inverse start)
  | step prior adjacency ih =>
      exact .step ih ((graph.adjacent_unreindex_iff r _ _).mp adjacency)

end Walk

theorem Bounded.reindex {graph : Graph}
    (bounded : graph.Bounded) (r : VertexRenaming graph.vertexCount) :
    (graph.reindex r).Bounded := by
  intro renamedEdge membership
  rcases List.mem_map.mp membership with ⟨edge, edgeMembership, same⟩
  subst renamedEdge
  have bounds := bounded edge edgeMembership
  exact ⟨(r.forward_lt_iff edge.first).mpr bounds.1,
    (r.forward_lt_iff edge.second).mpr bounds.2.1,
    fun equality => bounds.2.2 (r.forward_injective equality)⟩

theorem bounded_reindex_iff (graph : Graph)
    (r : VertexRenaming graph.vertexCount) :
    (graph.reindex r).Bounded ↔ graph.Bounded := by
  constructor
  · intro bounded
    have restored := bounded.reindex r.symm
    simpa only [graph.reindex_symm r] using restored
  · exact fun bounded => bounded.reindex r

theorem Connected.reindex {graph : Graph}
    (connected : graph.Connected) (r : VertexRenaming graph.vertexCount) :
    (graph.reindex r).Connected := by
  refine ⟨by simpa using connected.1, ?_⟩
  intro vertex inBounds
  have zeroInBounds : 0 < graph.vertexCount := connected.1
  have inverseZeroInBounds : r.inverse 0 < graph.vertexCount :=
    (r.inverse_lt_iff 0).mpr zeroInBounds
  have inverseVertexInBounds : r.inverse vertex < graph.vertexCount :=
    (r.inverse_lt_iff vertex).mpr (by simpa using inBounds)
  have fromZero := connected.2 (r.inverse 0) inverseZeroInBounds
  have toVertex := connected.2 (r.inverse vertex) inverseVertexInBounds
  have between := fromZero.reverse.trans toVertex
  simpa only [r.forward_inverse] using between.reindex r

theorem connected_reindex_iff (graph : Graph)
    (r : VertexRenaming graph.vertexCount) :
    (graph.reindex r).Connected ↔ graph.Connected := by
  constructor
  · intro connected
    have restored := connected.reindex r.symm
    simpa only [graph.reindex_symm r] using restored
  · exact fun connected => connected.reindex r

theorem IsTree.reindex {graph : Graph}
    (tree : graph.IsTree) (r : VertexRenaming graph.vertexCount) :
    (graph.reindex r).IsTree :=
  ⟨tree.1.reindex r, tree.2.1.reindex r, by simpa using tree.2.2⟩

theorem isTree_reindex_iff (graph : Graph)
    (r : VertexRenaming graph.vertexCount) :
    (graph.reindex r).IsTree ↔ graph.IsTree := by
  constructor
  · intro tree
    have restored := tree.reindex r.symm
    simpa only [graph.reindex_symm r] using restored
  · exact fun tree => tree.reindex r

@[simp] theorem isTree_reindex (graph : Graph)
    (r : VertexRenaming graph.vertexCount) :
    (graph.reindex r).isTree = graph.isTree := by
  apply Bool.eq_iff_iff.mpr
  rw [(graph.reindex r).isTree_iff_isTree, graph.isTree_iff_isTree]
  exact graph.isTree_reindex_iff r

namespace EdgeWalk

/-- Exact edge-aware walks are preserved by a bounded vertex renaming. -/
theorem reindex {graph : Graph} {start finish : Vertex}
    {traversed : List graph.DirectedEdge}
    (walk : graph.EdgeWalk start traversed finish)
    (r : VertexRenaming graph.vertexCount) :
    (graph.reindex r).EdgeWalk (r.forward start)
      (traversed.map fun directed => directed.reindex r)
      (r.forward finish) := by
  induction walk with
  | refl =>
      exact .refl _
  | @step start finish traversed prior directed starts finishes ih =>
      rw [List.map_append]
      exact .step ih (directed.reindex r)
        (by simpa using congrArg r.forward starts)
        (by simpa using congrArg r.forward finishes)

end EdgeWalk

namespace EdgeSimpleCycle

/-- Exact occurrence-aware simple cycles are preserved by a bounded vertex
renaming. -/
def reindex {graph : Graph} (cycle : graph.EdgeSimpleCycle)
    (r : VertexRenaming graph.vertexCount) :
    (graph.reindex r).EdgeSimpleCycle where
  start := r.forward cycle.start
  traversed := cycle.traversed.map fun directed => directed.reindex r
  nonempty := by simpa using cycle.nonempty
  walk := cycle.walk.reindex r
  edgeIndicesNodup := by
    simpa [List.map_map, Function.comp_def] using cycle.edgeIndicesNodup
  interiorNodup := by
    have renamed :
        ((cycle.start ::
          cycle.traversed.dropLast.map DirectedEdge.target).map
            r.forward).Nodup :=
      cycle.interiorNodup.map r.forward
        (fun _ _ unequal same => unequal (r.forward_injective same))
    simpa [List.map_dropLast, List.map_map, Function.comp_def] using renamed

end EdgeSimpleCycle

/-- Occurrence-aware acyclicity is preserved by a bounded vertex renaming. -/
theorem Acyclic.reindex {graph : Graph} (acyclic : graph.Acyclic)
    (r : VertexRenaming graph.vertexCount) :
    (graph.reindex r).Acyclic := by
  intro renamedCycle
  have restored : graph.EdgeSimpleCycle := by
    simpa only [graph.reindex_symm r] using renamedCycle.reindex r.symm
  exact acyclic restored

/-- Occurrence-aware acyclicity is invariant under bounded vertex
renaming. -/
theorem acyclic_reindex_iff (graph : Graph)
    (r : VertexRenaming graph.vertexCount) :
    (graph.reindex r).Acyclic ↔ graph.Acyclic := by
  constructor
  · intro acyclic
    have restored := acyclic.reindex r.symm
    simpa only [graph.reindex_symm r] using restored
  · exact fun acyclic => acyclic.reindex r

end Graph

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

/-- Regard a second renaming of an already-reindexed certificate at the
original certificate's (provably equal) bound. -/
def alignNextRenaming (certificate : Certificate)
    (first : VertexRenaming certificate.formulas.size)
    (second : VertexRenaming (certificate.reindex first).formulas.size) :
    VertexRenaming certificate.formulas.size :=
  second.changeBound (certificate.reindex_formulas_size first)

@[simp] theorem alignNextRenaming_forward (certificate : Certificate)
    (first : VertexRenaming certificate.formulas.size)
    (second : VertexRenaming (certificate.reindex first).formulas.size) :
    (certificate.alignNextRenaming first second).forward = second.forward := by
  simp [alignNextRenaming]

@[simp] theorem alignNextRenaming_inverse (certificate : Certificate)
    (first : VertexRenaming certificate.formulas.size)
    (second : VertexRenaming (certificate.reindex first).formulas.size) :
    (certificate.alignNextRenaming first second).inverse = second.inverse := by
  simp [alignNextRenaming]

@[simp] theorem reindex_trans (certificate : Certificate)
    (first : VertexRenaming certificate.formulas.size)
    (second : VertexRenaming (certificate.reindex first).formulas.size) :
    (certificate.reindex first).reindex second =
      certificate.reindex
        (first.trans (certificate.alignNextRenaming first second)) := by
  apply ext_fields
  · apply Array.ext
    · simp
    · intro vertex leftInBounds rightInBounds
      simp [reindex, alignNextRenaming, VertexRenaming.trans,
        Function.comp_def]
  · change List.map (Link.reindex second)
      (List.map (Link.reindex first) certificate.links) =
        List.map
          (Link.reindex
            (first.trans (certificate.alignNextRenaming first second)))
          certificate.links
    induction certificate.links with
    | nil => rfl
    | cons head tail ih =>
        simp only [List.map_cons, List.cons.injEq]
        exact ⟨by
          cases head <;>
            simp [Link.reindex, VertexRenaming.trans, alignNextRenaming,
              Function.comp_def], ih⟩
  · simp [reindex, List.map_map, VertexRenaming.trans,
      Function.comp_def]

@[simp] theorem reindex_links (certificate : Certificate)
    (r : VertexRenaming certificate.formulas.size) :
    (certificate.reindex r).links =
      certificate.links.map (Link.reindex r) := rfl

@[simp] theorem reindex_conclusions (certificate : Certificate)
    (r : VertexRenaming certificate.formulas.size) :
    (certificate.reindex r).conclusions =
      certificate.conclusions.map r.forward := rfl

@[simp] theorem fixedEdges_reindex (certificate : Certificate)
    (r : VertexRenaming certificate.formulas.size) :
    (certificate.reindex r).fixedEdges =
      certificate.fixedEdges.map (Edge.reindex r) := by
  simp only [fixedEdges, reindex_links]
  induction certificate.links with
  | nil => rfl
  | cons head tail ih =>
      cases head <;> simp [Link.reindex, Edge.reindex, ih]

@[simp] theorem parChoices_reindex (certificate : Certificate)
    (r : VertexRenaming certificate.formulas.size) :
    (certificate.reindex r).parChoices =
      certificate.parChoices.map (Edge.reindexPair r) := by
  simp only [parChoices, reindex_links]
  induction certificate.links with
  | nil => rfl
  | cons head tail ih =>
      cases head <;> simp [Link.reindex, Edge.reindex, Edge.reindexPair, ih]

theorem ChoiceSelection.reindex {bound : Nat}
    {choices : List (Edge × Edge)} {selected : List Edge}
    (selection : ChoiceSelection choices selected)
    (r : VertexRenaming bound) :
    ChoiceSelection (choices.map (Edge.reindexPair r))
      (selected.map (Edge.reindex r)) := by
  induction selection with
  | nil => exact .nil
  | left prior ih => exact .left ih
  | right prior ih => exact .right ih

@[simp] theorem graphForSelection_reindex (certificate : Certificate)
    (r : VertexRenaming certificate.formulas.size) (selected : List Edge) :
    (certificate.reindex r).graphForSelection
        (selected.map (Edge.reindex r)) =
      (certificate.graphForSelection selected).reindex r := by
  simp [graphForSelection, Graph.reindex, List.map_append]

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

@[simp] theorem inBounds_reindex_forward (certificate : Certificate)
    (r : VertexRenaming certificate.formulas.size) (vertex : Vertex) :
    (certificate.reindex r).inBounds (r.forward vertex) =
      certificate.inBounds vertex := by
  simp [inBounds, r.forward_lt_iff]

/-- Local formula/link typing is invariant under any bounded bijective vertex
renaming. -/
@[simp] theorem linkLocallyWellFormed_reindex (certificate : Certificate)
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

@[simp] theorem linksAll_reindex (certificate : Certificate)
    (r : VertexRenaming certificate.formulas.size) :
    (certificate.reindex r).links.all
        (certificate.reindex r).linkLocallyWellFormed =
      certificate.links.all certificate.linkLocallyWellFormed := by
  simp only [reindex_links]
  induction certificate.links with
  | nil => rfl
  | cons head tail ih =>
      simp [certificate.linkLocallyWellFormed_reindex, ih]

@[simp] theorem conclusionsAllInBounds_reindex (certificate : Certificate)
    (r : VertexRenaming certificate.formulas.size) :
    (certificate.reindex r).conclusions.all
        (certificate.reindex r).inBounds =
      certificate.conclusions.all certificate.inBounds := by
  simp only [reindex_conclusions]
  induction certificate.conclusions with
  | nil => rfl
  | cons head tail ih =>
      simp [certificate.inBounds_reindex_forward, ih]

@[simp] theorem nodesAll_reindex (certificate : Certificate)
    (r : VertexRenaming certificate.formulas.size) :
    (List.range (certificate.reindex r).formulas.size).all
        (certificate.reindex r).nodeWellFormed =
      (List.range certificate.formulas.size).all
        certificate.nodeWellFormed := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true, List.mem_range]
  constructor
  · intro allRenamed vertex inBounds
    have renamedInBounds := (r.forward_lt_iff vertex).mpr inBounds
    have accepted := allRenamed (r.forward vertex) (by simpa using renamedInBounds)
    rw [certificate.nodeWellFormed_reindex] at accepted
    exact accepted
  · intro allOriginal vertex inBounds
    have originalInBounds := (r.inverse_lt_iff vertex).mpr (by simpa using inBounds)
    have accepted := allOriginal (r.inverse vertex) originalInBounds
    have transported := certificate.nodeWellFormed_reindex r (r.inverse vertex)
    rw [← transported] at accepted
    simpa only [r.forward_inverse] using accepted

/-- The complete executable structural checker is invariant under arbitrary
bounded vertex reindexing, including malformed-certificate rejection. -/
@[simp] theorem wellFormed_reindex (certificate : Certificate)
    (r : VertexRenaming certificate.formulas.size) :
    (certificate.reindex r).wellFormed = certificate.wellFormed := by
  unfold wellFormed
  rw [certificate.conclusionsAllInBounds_reindex,
    certificate.linksAll_reindex, certificate.nodesAll_reindex]
  simp

theorem structurallyWellFormed_reindex_iff (certificate : Certificate)
    (r : VertexRenaming certificate.formulas.size) :
    (certificate.reindex r).StructurallyWellFormed ↔
      certificate.StructurallyWellFormed := by
  rw [← (certificate.reindex r).wellFormed_iff_structurallyWellFormed,
    certificate.wellFormed_reindex,
    certificate.wellFormed_iff_structurallyWellFormed]

/-- The inverse renaming, transported to the definitionally new formula-array
size produced by `reindex`. -/
def inverseReindexing (certificate : Certificate)
    (r : VertexRenaming certificate.formulas.size) :
    VertexRenaming (certificate.reindex r).formulas.size :=
  r.symm.changeBound (certificate.reindex_formulas_size r).symm

@[simp] theorem reindex_refl (certificate : Certificate) :
    certificate.reindex (VertexRenaming.refl certificate.formulas.size) =
      certificate := by
  apply ext_fields
  · apply Array.ext
    · simp
    · intro vertex leftInBounds rightInBounds
      simp [reindex, VertexRenaming.refl]
  · change List.map
      (Link.reindex (VertexRenaming.refl certificate.formulas.size))
        certificate.links = certificate.links
    induction certificate.links with
    | nil => rfl
    | cons head tail ih =>
        cases head <;>
          simp only [List.map_cons, List.cons.injEq]
        all_goals exact ⟨rfl, ih⟩
  · simp [reindex, VertexRenaming.refl]

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

theorem DeclarativelyCorrect.reindex {certificate : Certificate}
    (correct : certificate.DeclarativelyCorrect)
    (r : VertexRenaming certificate.formulas.size) :
    (certificate.reindex r).DeclarativelyCorrect := by
  let renamed := certificate.reindex r
  let inverse := certificate.inverseReindexing r
  refine ⟨(certificate.structurallyWellFormed_reindex_iff r).mpr correct.1,
    ?_⟩
  intro graph switching
  rcases switching with ⟨selected, selection, rfl⟩
  have restoredCertificate : renamed.reindex inverse = certificate :=
    certificate.reindex_inverse r
  have restoredSelection := selection.reindex inverse
  rw [← renamed.parChoices_reindex inverse, restoredCertificate] at restoredSelection
  have graphTransport := renamed.graphForSelection_reindex inverse selected
  rw [restoredCertificate] at graphTransport
  have restoredSwitching :
      certificate.SwitchingGraph
        ((renamed.graphForSelection selected).reindex inverse) :=
    ⟨selected.map (Edge.reindex inverse), restoredSelection,
      graphTransport.symm⟩
  have restoredTree := correct.2 _ restoredSwitching
  exact ((renamed.graphForSelection selected).isTree_reindex_iff inverse).mp
    restoredTree

theorem declarativelyCorrect_reindex_iff (certificate : Certificate)
    (r : VertexRenaming certificate.formulas.size) :
    (certificate.reindex r).DeclarativelyCorrect ↔
      certificate.DeclarativelyCorrect := by
  constructor
  · intro correct
    have restored := correct.reindex (certificate.inverseReindexing r)
    simpa only [certificate.reindex_inverse r] using restored
  · exact fun correct => correct.reindex r

/-- The public Boolean proof-net checker is independent of all admissible
vertex names, not merely for known-valid examples but for every certificate. -/
@[simp] theorem check_reindex (certificate : Certificate)
    (r : VertexRenaming certificate.formulas.size) :
    (certificate.reindex r).check = certificate.check := by
  apply Bool.eq_iff_iff.mpr
  rw [(certificate.reindex r).check_iff_declarativelyCorrect,
    certificate.check_iff_declarativelyCorrect]
  exact certificate.declarativelyCorrect_reindex_iff r

theorem correct_reindex_iff (certificate : Certificate)
    (r : VertexRenaming certificate.formulas.size) :
    (certificate.reindex r).Correct ↔ certificate.Correct := by
  rw [← (certificate.reindex r).check_iff_correct,
    certificate.check_reindex, certificate.check_iff_correct]

/-- Certificate equality modulo an explicit bounded vertex bijection. Formula
syntax, ordered tensor/par premises, link order, and conclusion order are all
preserved; only vertex names change. -/
def ReindexEquivalent (left right : Certificate) : Prop :=
  ∃ r : VertexRenaming left.formulas.size, right = left.reindex r

theorem ReindexEquivalent.refl (certificate : Certificate) :
    certificate.ReindexEquivalent certificate :=
  ⟨VertexRenaming.refl certificate.formulas.size,
    certificate.reindex_refl.symm⟩

theorem ReindexEquivalent.symm {left right : Certificate}
    (equivalent : left.ReindexEquivalent right) :
    right.ReindexEquivalent left := by
  rcases equivalent with ⟨r, rfl⟩
  exact ⟨left.inverseReindexing r, (left.reindex_inverse r).symm⟩

theorem ReindexEquivalent.trans {left middle right : Certificate}
    (first : left.ReindexEquivalent middle)
    (second : middle.ReindexEquivalent right) :
    left.ReindexEquivalent right := by
  rcases first with ⟨firstRenaming, rfl⟩
  rcases second with ⟨secondRenaming, rfl⟩
  exact ⟨firstRenaming.trans
      (left.alignNextRenaming firstRenaming secondRenaming),
    left.reindex_trans firstRenaming secondRenaming⟩

theorem reindexEquivalent_equivalence : Equivalence ReindexEquivalent :=
  ⟨ReindexEquivalent.refl, ReindexEquivalent.symm,
    ReindexEquivalent.trans⟩

theorem ReindexEquivalent.check_eq {left right : Certificate}
    (equivalent : left.ReindexEquivalent right) :
    left.check = right.check := by
  rcases equivalent with ⟨r, rfl⟩
  exact (left.check_reindex r).symm

theorem ReindexEquivalent.declarativelyCorrect_iff
    {left right : Certificate} (equivalent : left.ReindexEquivalent right) :
    left.DeclarativelyCorrect ↔ right.DeclarativelyCorrect := by
  rcases equivalent with ⟨r, rfl⟩
  exact (left.declarativelyCorrect_reindex_iff r).symm

theorem ReindexEquivalent.correct_iff {left right : Certificate}
    (equivalent : left.ReindexEquivalent right) :
    left.Correct ↔ right.Correct := by
  rcases equivalent with ⟨r, rfl⟩
  exact (left.correct_reindex_iff r).symm

end Certificate

end ProofNetIR
