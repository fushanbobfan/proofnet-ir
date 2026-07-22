import Lean.Elab.Tactic.Omega
import ProofNetIR.DerivationTree
import ProofNetIR.NetEquivalence

namespace ProofNetIR

private theorem eq_of_mem_filter_length_one {α : Type}
    {values : List α} {predicate : α → Bool} {first second : α}
    (count : (values.filter predicate).length = 1)
    (firstMembership : first ∈ values) (firstAccepted : predicate first = true)
    (secondMembership : second ∈ values)
    (secondAccepted : predicate second = true) :
    first = second := by
  have firstFiltered : first ∈ values.filter predicate := by
    simp [firstMembership, firstAccepted]
  have secondFiltered : second ∈ values.filter predicate := by
    simp [secondMembership, secondAccepted]
  rcases List.length_eq_one_iff.mp count with ⟨only, filterEquation⟩
  rw [filterEquation] at firstFiltered secondFiltered
  simp at firstFiltered secondFiltered
  exact firstFiltered.trans secondFiltered.symm

private theorem false_of_mem_filter_length_zero {α : Type}
    {values : List α} {predicate : α → Bool} {value : α}
    (count : (values.filter predicate).length = 0)
    (membership : value ∈ values) (accepted : predicate value = true) :
    False := by
  have filtered : value ∈ values.filter predicate := by
    simp [membership, accepted]
  have positive := List.length_pos_of_mem filtered
  rw [count] at positive
  exact Nat.not_lt_zero 0 positive

private theorem length_eraseDups_le [BEq α] (values : List α) :
    values.eraseDups.length ≤ values.length := by
  cases values with
  | nil => simp
  | cons head tail =>
      rw [List.eraseDups_cons]
      simp only [List.length_cons, Nat.add_le_add_iff_right]
      exact Nat.le_trans
        (length_eraseDups_le (tail.filter fun value => !value == head))
        (List.length_filter_le _ tail)
termination_by values.length
decreasing_by
  exact Nat.lt_add_one_of_le (List.length_filter_le _ tail)

private theorem nodup_of_eraseDups_length_eq [BEq α] [LawfulBEq α]
    {values : List α}
    (sameLength : values.eraseDups.length = values.length) :
    values.Nodup := by
  induction values with
  | nil => exact .nil
  | cons head tail ih =>
      rw [List.eraseDups_cons] at sameLength
      simp only [List.length_cons] at sameLength
      let retained := tail.filter fun value => !value == head
      have erasedEqualsTail : retained.eraseDups.length = tail.length := by
        change (tail.filter fun value => !value == head).eraseDups.length =
          tail.length
        exact Nat.add_right_cancel sameLength
      have retainedAtMost : retained.length ≤ tail.length :=
        List.length_filter_le _ tail
      have erasedAtMost : retained.eraseDups.length ≤ retained.length :=
        length_eraseDups_le retained
      have retainedAtLeast : tail.length ≤ retained.length := by
        rw [← erasedEqualsTail]
        exact erasedAtMost
      have retainedLength : retained.length = tail.length :=
        Nat.le_antisymm retainedAtMost retainedAtLeast
      have allRetained : ∀ value ∈ tail, value != head :=
        List.length_filter_eq_length_iff.mp retainedLength
      have retainedEquation : retained = tail :=
        List.filter_eq_self.mpr allRetained
      have headFresh : head ∉ tail := by
        intro membership
        have rejected := allRetained head membership
        simp at rejected
      apply List.nodup_cons.mpr
      refine ⟨headFresh, ih ?_⟩
      simpa only [retainedEquation] using erasedEqualsTail

private theorem eraseDups_eq_self_of_nodup [BEq α] [LawfulBEq α]
    {values : List α} (nodup : values.Nodup) :
    values.eraseDups = values := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
      rcases List.nodup_cons.mp nodup with ⟨headFresh, tailNodup⟩
      rw [List.eraseDups_cons]
      have allDifferent : ∀ value ∈ tail, !(value == head) := by
        intro value membership
        have different : value ≠ head := by
          intro same
          subst value
          exact headFresh membership
        simp [beq_eq_false_iff_ne.mpr different]
      rw [List.filter_eq_self.mpr allDifferent, ih tailNodup]

private theorem nodup_map_of_injective_on {α β : Type}
    {values : List α} {function : α → β}
    (nodup : values.Nodup)
    (injectiveOn : ∀ first ∈ values, ∀ second ∈ values,
      function first = function second → first = second) :
    (values.map function).Nodup := by
  induction values with
  | nil => exact .nil
  | cons head tail ih =>
      rcases List.nodup_cons.mp nodup with ⟨headFresh, tailNodup⟩
      apply List.nodup_cons.mpr
      constructor
      · intro headImageInTail
        rcases List.mem_map.mp headImageInTail with
          ⟨value, valueMembership, imageEqual⟩
        have same := injectiveOn value (by simp [valueMembership]) head
          (by simp) imageEqual
        subst value
        exact headFresh valueMembership
      · apply ih tailNodup
        intro first firstMembership second secondMembership same
        exact injectiveOn first (by simp [firstMembership]) second
          (by simp [secondMembership]) same

private theorem length_le_of_nodup_subset' [BEq α] [LawfulBEq α]
    {values ambient : List α} (nodup : values.Nodup)
    (subset : ∀ value ∈ values, value ∈ ambient) :
    values.length ≤ ambient.length := by
  induction values generalizing ambient with
  | nil => simp
  | cons head tail ih =>
      have headMembership : head ∈ ambient := subset head (by simp)
      have tailSubset : ∀ value ∈ tail, value ∈ ambient.erase head := by
        intro value membership
        have valueMembership := subset value (by simp [membership])
        have different : value ≠ head := by
          intro same
          subst value
          exact (List.nodup_cons.mp nodup).1 membership
        exact (List.mem_erase_of_ne different).mpr valueMembership
      have tailBound := ih (List.nodup_cons.mp nodup).2 tailSubset
      rw [List.length_erase_of_mem headMembership] at tailBound
      have ambientPositive : 0 < ambient.length :=
        List.length_pos_of_mem headMembership
      simp only [List.length_cons]
      omega

private theorem exists_least_nat_up_to (property : Nat → Prop) :
    ∀ bound, (∃ value, value ≤ bound ∧ property value) →
      ∃ least, property least ∧ ∀ value, property value → least ≤ value := by
  intro bound
  induction bound with
  | zero =>
      rintro ⟨value, valueBound, propertyValue⟩
      have valueZero : value = 0 := by omega
      subst value
      exact ⟨0, propertyValue, by intro; omega⟩
  | succ bound ih =>
      intro existsBounded
      by_cases existsEarlier : ∃ value, value ≤ bound ∧ property value
      · exact ih existsEarlier
      · rcases existsBounded with ⟨value, valueBound, propertyValue⟩
        have notEarlier : ¬ value ≤ bound := by
          intro earlier
          exact existsEarlier ⟨value, earlier, propertyValue⟩
        have valueLast : value = bound + 1 := by omega
        subst value
        refine ⟨bound + 1, propertyValue, ?_⟩
        intro other propertyOther
        have otherNotEarlier : ¬ other ≤ bound := by
          intro earlier
          exact existsEarlier ⟨other, earlier, propertyOther⟩
        omega

private theorem exists_least_nat (property : Nat → Prop)
    (existsProperty : ∃ value, property value) :
    ∃ least, property least ∧ ∀ value, property value → least ≤ value := by
  rcases existsProperty with ⟨bound, propertyBound⟩
  exact exists_least_nat_up_to property bound ⟨bound, by omega, propertyBound⟩

private theorem exists_maximal_measure {α : Type}
    (head : α) (tail : List α) (measure : α → Nat) :
    ∃ maximal ∈ head :: tail,
      ∀ value ∈ head :: tail, measure value ≤ measure maximal := by
  induction tail generalizing head with
  | nil =>
      refine ⟨head, by simp, ?_⟩
      intro value membership
      simp at membership
      subst value
      exact Nat.le_refl _
  | cons second rest ih =>
      rcases ih second with ⟨maximal, maximalMembership, maximalBound⟩
      by_cases headBound : measure head ≤ measure maximal
      · refine ⟨maximal, by simp [maximalMembership], ?_⟩
        intro value membership
        simp at membership
        rcases membership with rfl | tailMembership
        · exact headBound
        · exact maximalBound value (by simpa using tailMembership)
      · have maximalBelowHead : measure maximal ≤ measure head := by omega
        refine ⟨head, by simp, ?_⟩
        intro value membership
        simp at membership
        rcases membership with rfl | tailMembership
        · exact Nat.le_refl _
        · exact Nat.le_trans
            (maximalBound value (by simpa using tailMembership))
            maximalBelowHead

private theorem exists_minimal_measure {α : Type}
    (head : α) (tail : List α) (measure : α → Nat) :
    ∃ minimal ∈ head :: tail,
      ∀ value ∈ head :: tail, measure minimal ≤ measure value := by
  let property : Nat → Prop := fun candidate =>
    ∃ value ∈ head :: tail, measure value = candidate
  have existsProperty : ∃ candidate, property candidate :=
    ⟨measure head, head, by simp, rfl⟩
  rcases exists_least_nat property existsProperty with
    ⟨least, ⟨minimal, minimalMembership, minimalMeasure⟩, leastBound⟩
  refine ⟨minimal, minimalMembership, ?_⟩
  intro value valueMembership
  rw [minimalMeasure]
  exact leastBound (measure value) ⟨value, valueMembership, rfl⟩

private theorem length_filter_filterMap_eq {α β : Type}
    (values : List α) (transform : α → Option β)
    (after : β → Bool) (before : α → Bool)
    (compatible : ∀ value ∈ values,
      match transform value with
      | none => before value = false
      | some transformed => after transformed = before value) :
    ((values.filterMap transform).filter after).length =
      (values.filter before).length := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
      have headCompatible := compatible head (by simp)
      have tailCompatible : ∀ value ∈ tail,
          match transform value with
          | none => before value = false
          | some transformed => after transformed = before value := by
        intro value membership
        exact compatible value (by simp [membership])
      cases equation : transform head with
      | none =>
          have rejected : before head = false := by
            simpa [equation] using headCompatible
          simp [equation, rejected, ih tailCompatible]
      | some transformed =>
          have agrees : after transformed = before head := by
            simpa [equation] using headCompatible
          cases accepted : before head with
          | false =>
              have afterRejected : after transformed = false :=
                agrees.trans accepted
              simp [equation, accepted, afterRejected, ih tailCompatible]
          | true =>
              have afterAccepted : after transformed = true :=
                agrees.trans accepted
              simp [equation, accepted, afterAccepted, ih tailCompatible]

private theorem length_filter_three_partition {α : Type}
    (values : List α) (first second third : α → Bool)
    (partition : ∀ value ∈ values,
      (first value = true ∧ second value = false ∧ third value = false) ∨
      (first value = false ∧ second value = true ∧ third value = false) ∨
      (first value = false ∧ second value = false ∧ third value = true)) :
    (values.filter first).length + (values.filter second).length +
      (values.filter third).length = values.length := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
      have tailPartition : ∀ value ∈ tail,
          (first value = true ∧ second value = false ∧ third value = false) ∨
          (first value = false ∧ second value = true ∧ third value = false) ∨
          (first value = false ∧ second value = false ∧ third value = true) := by
        intro value membership
        exact partition value (by simp [membership])
      rcases partition head (by simp) with firstCase | secondCase | thirdCase
      · simp [firstCase.1, firstCase.2.1, firstCase.2.2]
        have count := ih tailPartition
        omega
      · simp [secondCase.1, secondCase.2.1, secondCase.2.2]
        have count := ih tailPartition
        omega
      · simp [thirdCase.1, thirdCase.2.1, thirdCase.2.2]
        have count := ih tailPartition
        omega

private theorem length_filter_eq_vertex_of_lt (count vertex : Nat)
    (inBounds : vertex < count) :
    ((List.range count).filter (fun candidate => candidate == vertex)).length =
      1 := by
  induction count with
  | zero => omega
  | succ count ih =>
      rw [List.range_succ]
      by_cases same : count = vertex
      · subst count
        have none : (List.range vertex).filter
            (fun candidate => candidate == vertex) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro candidate membership accepted
          have candidateBound := List.mem_range.mp membership
          simp at accepted
          omega
        simp [none]
      · have earlier : vertex < count := by omega
        simp [List.filter_append, same, ih earlier]

private theorem list_mapM_eq_some_of_forall {α β : Type}
    (values : List α) (function : α → Option β)
    (defined : ∀ value ∈ values, ∃ result, function value = some result) :
    ∃ results, values.mapM function = some results := by
  induction values with
  | nil => exact ⟨[], rfl⟩
  | cons head tail ih =>
      rcases defined head (by simp) with ⟨headResult, headEquation⟩
      have tailDefined : ∀ value ∈ tail,
          ∃ result, function value = some result := by
        intro value membership
        exact defined value (by simp [membership])
      rcases ih tailDefined with ⟨tailResults, tailEquation⟩
      exact ⟨headResult :: tailResults, by
        simp [headEquation, tailEquation]⟩

private theorem list_mapM_length_of_eq_some {α β : Type}
    {values : List α} {function : α → Option β} {results : List β}
    (equation : values.mapM function = some results) :
    results.length = values.length := by
  induction values generalizing results with
  | nil =>
      simp at equation
      subst results
      rfl
  | cons head tail ih =>
      cases headEquation : function head with
      | none => simp [headEquation] at equation
      | some headResult =>
          cases tailEquation : tail.mapM function with
          | none => simp [headEquation, tailEquation] at equation
          | some tailResults =>
              simp [headEquation, tailEquation] at equation
              subst results
              simp [ih tailEquation]

private theorem list_mapM_eq_some_map_of_forall {α β : Type}
    (values : List α) (function : α → Option β) (result : α → β)
    (defined : ∀ value ∈ values, function value = some (result value)) :
    values.mapM function = some (values.map result) := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
      have headDefined := defined head (by simp)
      have tailDefined : ∀ value ∈ tail,
          function value = some (result value) := by
        intro value membership
        exact defined value (by simp [membership])
      simp [headDefined, ih tailDefined]

private theorem idxOf?_eq_some_idxOf_of_mem [BEq α] [LawfulBEq α]
    {values : List α} {value : α} (membership : value ∈ values) :
    values.idxOf? value = some (values.idxOf value) := by
  unfold List.idxOf? List.idxOf
  apply List.findIdx?_eq_some_of_exists
  exact ⟨value, membership, by simp⟩

private theorem mem_of_idxOf?_eq_some [BEq α] [LawfulBEq α]
    {values : List α} {value : α} {index : Nat}
    (equation : values.idxOf? value = some index) : value ∈ values := by
  rw [← List.isSome_idxOf?]
  simp [equation]

private theorem list_map_getElem?_idxOf_eq_some
    [BEq α] [LawfulBEq α]
    (values : List α) (function : α → β) {value : α}
    (membership : value ∈ values) :
    (values.map function)[values.idxOf value]? = some (function value) := by
  have found := (List.idxOf?_eq_some_iff).mp
    (idxOf?_eq_some_idxOf_of_mem membership)
  rcases found with ⟨indexInBounds, valueAtIndex, _⟩
  have mappedInBounds : values.idxOf value < (values.map function).length := by
    simpa using indexInBounds
  rw [List.getElem?_eq_getElem mappedInBounds]
  simp [valueAtIndex]

private theorem idxOf_injective_of_mem
    [BEq α] [LawfulBEq α]
    {values : List α} {left right : α}
    (leftMembership : left ∈ values) (rightMembership : right ∈ values)
    (sameIndex : values.idxOf left = values.idxOf right) : left = right := by
  have leftFound := list_map_getElem?_idxOf_eq_some values id leftMembership
  have rightFound := list_map_getElem?_idxOf_eq_some values id rightMembership
  rw [sameIndex, rightFound] at leftFound
  simpa using leftFound.symm

private theorem idxOf_getElem_eq_index
    [BEq α] [LawfulBEq α]
    {values : List α} (nodup : values.Nodup)
    (index : Nat) (inBounds : index < values.length) :
    values.idxOf values[index] = index := by
  have membership : values[index] ∈ values := List.getElem_mem inBounds
  have firstInBounds := List.idxOf_lt_length_of_mem membership
  have firstOccurrence :
      values[values.idxOf values[index]]? = some values[index] := by
    simpa using list_map_getElem?_idxOf_eq_some values id membership
  apply (List.getElem?_inj firstInBounds nodup).mp
  rw [firstOccurrence, List.getElem?_eq_getElem inBounds]

private theorem list_mapM_getElem?_idxOf_eq_some
    [BEq α] [LawfulBEq α]
    (source target : List α)
    (contained : ∀ value ∈ target, value ∈ source) :
    (target.map source.idxOf).mapM (fun index => source[index]?) =
      some target := by
  induction target with
  | nil => rfl
  | cons head tail ih =>
      have headMembership : head ∈ source := contained head (by simp)
      have tailContained : ∀ value ∈ tail, value ∈ source := by
        intro value membership
        exact contained value (by simp [membership])
      have headFound : source[source.idxOf head]? = some head := by
        simpa using list_map_getElem?_idxOf_eq_some source id headMembership
      simp [headFound, ih tailContained]

/-- For duplicate-free occurrence data, the target's source indices form a
valid executable exchange order whenever the target is a permutation of the
source. This is occurrence-aware: callers may use formula/root pairs rather
than formula equality alone. -/
theorem CutFreeDerivation.reorder?_idxOf_of_nodup_perm
    [BEq α] [LawfulBEq α] [DecidableEq α]
    {source target : List α}
    (sourceNodup : source.Nodup) (permutation : source.Perm target) :
    CutFreeDerivation.reorder? source (target.map source.idxOf) =
      some target := by
  have targetNodup : target.Nodup := permutation.nodup_iff.mp sourceNodup
  have contained : ∀ value ∈ target, value ∈ source := by
    intro value membership
    exact permutation.mem_iff.mpr membership
  have orderNodup : (target.map source.idxOf).Nodup := by
    suffices general : ∀ values : List α, values.Nodup →
        (∀ value ∈ values, value ∈ source) →
        (values.map source.idxOf).Nodup by
      exact general target targetNodup contained
    intro values nodup valuesContained
    induction values with
    | nil => exact .nil
    | cons head tail ih =>
        rcases List.nodup_cons.mp nodup with ⟨headFresh, tailNodup⟩
        have headMembership : head ∈ source := valuesContained head (by simp)
        have tailContained : ∀ value ∈ tail, value ∈ source := by
          intro value membership
          exact valuesContained value (by simp [membership])
        apply List.nodup_cons.mpr
        refine ⟨?_, ih tailNodup tailContained⟩
        intro indexMembership
        rcases List.mem_map.mp indexMembership with
          ⟨value, valueMembership, sameIndex⟩
        have sameValue := idxOf_injective_of_mem headMembership
          (tailContained value valueMembership) sameIndex.symm
        exact headFresh (sameValue ▸ valueMembership)
  have orderBounds : (target.map source.idxOf).all
      (fun index => index < source.length) = true := by
    rw [List.all_eq_true]
    intro index indexMembership
    rcases List.mem_map.mp indexMembership with
      ⟨value, valueMembership, rfl⟩
    simpa using List.idxOf_lt_length_of_mem
      (contained value valueMembership)
  have candidate : CutFreeDerivation.reorderCandidate? source
      (target.map source.idxOf) = some target := by
    unfold CutFreeDerivation.reorderCandidate?
    have lengthEquation : target.length = source.length :=
      permutation.length_eq.symm
    have eraseEquation :
        (target.map source.idxOf).eraseDups = target.map source.idxOf :=
      eraseDups_eq_self_of_nodup orderNodup
    simp [lengthEquation, eraseEquation, orderBounds,
      list_mapM_getElem?_idxOf_eq_some source target contained]
  unfold CutFreeDerivation.reorder?
  rw [candidate]
  simp [permutation]

/-- Certificate-level effect of introducing one fresh final par occurrence.
The boundary is explicit because a following exchange may place the new
conclusion at any occurrence position. -/
def Certificate.appendParOccurrence (premise : Certificate)
    (left right : Formula) (leftRoot rightRoot : Vertex)
    (boundary : List Vertex) : Certificate where
  formulas := premise.formulas.push (.par left right)
  links := premise.links ++ [
    .par leftRoot rightRoot premise.formulas.size]
  conclusions := boundary

@[simp] theorem Certificate.appendParOccurrence_formulas_size
    (premise : Certificate) (left right : Formula)
    (leftRoot rightRoot : Vertex) (boundary : List Vertex) :
    (premise.appendParOccurrence left right leftRoot rightRoot boundary).formulas.size =
      premise.formulas.size + 1 := by
  simp [Certificate.appendParOccurrence]

/-- Type-align the insertion which moves a freshly appended par occurrence to
an arbitrary target vertex of the rebuilt certificate. -/
def Certificate.appendParPlacement (premise : Certificate)
    (left right : Formula) (leftRoot rightRoot : Vertex)
    (boundary : List Vertex) (removed : Vertex)
    (removedInBounds : removed < premise.formulas.size + 1) :
    VertexRenaming
      ((premise.appendParOccurrence left right leftRoot rightRoot boundary).formulas.size) :=
  (VertexRenaming.insertLastAt premise.formulas.size removed removedInBounds).changeBound
    (premise.appendParOccurrence_formulas_size left right leftRoot rightRoot
      boundary).symm

@[simp] theorem Certificate.appendParPlacement_forward
    (premise : Certificate) (left right : Formula)
    (leftRoot rightRoot : Vertex) (boundary : List Vertex)
    (removed : Vertex)
    (removedInBounds : removed < premise.formulas.size + 1) :
    (premise.appendParPlacement left right leftRoot rightRoot boundary removed
      removedInBounds).forward =
      (VertexRenaming.insertLastAt premise.formulas.size removed
        removedInBounds).forward := by
  simp [Certificate.appendParPlacement]

@[simp] theorem Certificate.appendParPlacement_inverse
    (premise : Certificate) (left right : Formula)
    (leftRoot rightRoot : Vertex) (boundary : List Vertex)
    (removed : Vertex)
    (removedInBounds : removed < premise.formulas.size + 1) :
    (premise.appendParPlacement left right leftRoot rightRoot boundary removed
      removedInBounds).inverse =
      (VertexRenaming.insertLastAt premise.formulas.size removed
        removedInBounds).inverse := by
  simp [Certificate.appendParPlacement]

/-- The type-aligned extension of an old renaming to the concrete certificate
obtained by appending one par occurrence. -/
def Certificate.appendParRenaming (premise : Certificate)
    (r : VertexRenaming premise.formulas.size)
    (left right : Formula) (leftRoot rightRoot : Vertex)
    (boundary : List Vertex) :
    VertexRenaming
      ((premise.appendParOccurrence left right leftRoot rightRoot boundary).formulas.size) :=
  r.extendLast.changeBound
    (premise.appendParOccurrence_formulas_size left right leftRoot rightRoot
      boundary).symm

@[simp] theorem Certificate.appendParRenaming_forward
    (premise : Certificate) (r : VertexRenaming premise.formulas.size)
    (left right : Formula) (leftRoot rightRoot : Vertex)
    (boundary : List Vertex) :
    (premise.appendParRenaming r left right leftRoot rightRoot boundary).forward =
      r.extendLast.forward := by
  simp [Certificate.appendParRenaming]

@[simp] theorem Certificate.appendParRenaming_inverse
    (premise : Certificate) (r : VertexRenaming premise.formulas.size)
    (left right : Formula) (leftRoot rightRoot : Vertex)
    (boundary : List Vertex) :
    (premise.appendParRenaming r left right leftRoot rightRoot boundary).inverse =
      r.extendLast.inverse := by
  simp [Certificate.appendParRenaming]

/-- Formula storage commutes with extending a vertex renaming across one
fresh final par occurrence. -/
theorem Certificate.appendParOccurrence_reindex_formulas
    (premise : Certificate) (r : VertexRenaming premise.formulas.size)
    (left right : Formula) (leftRoot rightRoot : Vertex)
    (boundary : List Vertex) :
    ((premise.appendParOccurrence left right leftRoot rightRoot boundary).reindex
      (premise.appendParRenaming r left right leftRoot rightRoot boundary)).formulas =
    ((premise.reindex r).appendParOccurrence left right
      (r.forward leftRoot) (r.forward rightRoot)
      (boundary.map r.forward)).formulas := by
  apply Array.ext_getElem?
  intro index
  by_cases oldIndex : index < premise.formulas.size
  · have inverseOld : r.inverse index < premise.formulas.size :=
      (r.inverse_lt_iff index).mpr oldIndex
    have indexNotLast : index ≠ premise.formulas.size := Nat.ne_of_lt oldIndex
    have inverseNotLast : r.inverse index ≠ premise.formulas.size :=
      Nat.ne_of_lt inverseOld
    simp only [Certificate.appendParOccurrence, Certificate.reindex,
      Certificate.appendParRenaming_inverse]
    rw [Array.getElem?_eq_getElem (by
      simp
      exact Nat.lt_succ_of_lt oldIndex)]
    simp [Array.getElem?_push, oldIndex, inverseOld, indexNotLast,
      inverseNotLast]
    rw [Array.getElem_push_lt inverseOld]
  · by_cases atLast : index = premise.formulas.size
    · subst index
      simp only [Certificate.appendParOccurrence, Certificate.reindex,
        Certificate.appendParRenaming_inverse]
      let renamed : Array Formula := Array.ofFn fun vertex =>
        premise.formulas[r.inverse vertex.val]'(
          (r.inverse_lt_iff vertex.val).mpr vertex.isLt)
      have renamedSize : renamed.size = premise.formulas.size := by
        simp [renamed]
      have rightValue :
          (renamed.push (left.par right))[premise.formulas.size]? =
            some (left.par right) := by
        rw [← renamedSize]
        exact Array.getElem?_push_size
      change _ = (renamed.push (left.par right))[premise.formulas.size]?
      rw [rightValue]
      simp [VertexRenaming.extendLast]
    · have outside : premise.formulas.size + 1 ≤ index := by
        omega
      have notBelow : ¬index < premise.formulas.size := oldIndex
      simp [Certificate.appendParOccurrence, Certificate.reindex,
        Array.getElem?_push, oldIndex, atLast, outside, notBelow,
        VertexRenaming.extendLast]

/-- Adding the same typed par rule to equivalent premises preserves direct
proof-net equivalence. Endpoint boundedness is stated explicitly so this
lemma cannot silently repair malformed certificates. -/
theorem Certificate.DirectProofNetEquivalent.appendParOccurrence
    {leftPremise rightPremise : Certificate}
    (vertexMap : VertexRenaming leftPremise.formulas.size)
    (linkPermutation :
      (leftPremise.reindex vertexMap).LinkPermutationEquivalent rightPremise)
    (left right : Formula) (leftRoot rightRoot : Vertex)
    (leftBoundary : List Vertex)
    (linksInBounds : ∀ link ∈ leftPremise.links,
      ∀ vertex ∈ link.vertices,
        vertex < leftPremise.formulas.size)
    (boundaryInBounds : ∀ vertex ∈ leftBoundary,
      vertex < leftPremise.formulas.size)
    (leftRootInBounds : leftRoot < leftPremise.formulas.size)
    (rightRootInBounds : rightRoot < leftPremise.formulas.size) :
    Certificate.DirectProofNetEquivalent
      (leftPremise.appendParOccurrence left right leftRoot rightRoot leftBoundary)
      (rightPremise.appendParOccurrence left right
        (vertexMap.forward leftRoot)
        (vertexMap.forward rightRoot)
        (leftBoundary.map vertexMap.forward)) := by
  refine ⟨leftPremise.appendParRenaming vertexMap left right leftRoot
    rightRoot leftBoundary, ?_⟩
  refine {
    formulas := ?_
    links := ?_
    conclusions := ?_ }
  · rw [Certificate.appendParOccurrence_reindex_formulas]
    exact congrArg (fun formulas => formulas.push (.par left right))
      linkPermutation.formulas
  · have oldLinks :
        leftPremise.links.map (Link.reindex
          (leftPremise.appendParRenaming vertexMap left right leftRoot
            rightRoot leftBoundary)) =
          leftPremise.links.map (Link.reindex vertexMap) := by
      apply List.map_congr_left
      intro link membership
      have extended := Link.reindex_extendLast vertexMap link
        (linksInBounds link membership)
      cases link <;>
        simpa [Link.reindex] using extended
    have newLink :
        Link.reindex
          (leftPremise.appendParRenaming vertexMap left right leftRoot
            rightRoot leftBoundary)
          (.par leftRoot rightRoot leftPremise.formulas.size) =
        .par (vertexMap.forward leftRoot) (vertexMap.forward rightRoot)
          rightPremise.formulas.size := by
      have sizeEquation : leftPremise.formulas.size =
          rightPremise.formulas.size := by
        simpa using congrArg Array.size linkPermutation.formulas
      simp only [Link.reindex]
      rw [Certificate.appendParRenaming_forward]
      rw [VertexRenaming.extendLast_forward_old vertexMap leftRootInBounds,
        VertexRenaming.extendLast_forward_old vertexMap rightRootInBounds,
        VertexRenaming.extendLast_forward_last]
      exact congrArg
        (fun result => Link.par (vertexMap.forward leftRoot)
          (vertexMap.forward rightRoot) result)
        sizeEquation
    rw [Certificate.reindex_links]
    change ((leftPremise.links ++ [
      Link.par leftRoot rightRoot leftPremise.formulas.size]).map
        (Link.reindex
          (leftPremise.appendParRenaming vertexMap left right leftRoot
            rightRoot leftBoundary))).Perm
      (rightPremise.links ++ [
        Link.par (vertexMap.forward leftRoot) (vertexMap.forward rightRoot)
          rightPremise.formulas.size])
    rw [List.map_append, List.map_singleton]
    rw [oldLinks, newLink]
    exact linkPermutation.links.append_right _
  · change leftBoundary.map
        (leftPremise.appendParRenaming vertexMap left right leftRoot
          rightRoot leftBoundary).forward =
        leftBoundary.map vertexMap.forward
    apply List.map_congr_left
    intro vertex membership
    simp [boundaryInBounds vertex membership]

/-- Evidence returned by the future general sequentializer. The result is
deliberately stronger than an `Option CutFreeDerivation`: it connects
first-order inference, desequentialization, ordered boundary labels, and the
semantic proof-net equivalence relation. -/
structure SequentializationResult (input : Certificate) where
  tree : CutFreeDerivation
  sequent : List Formula
  output : Certificate
  inferred : tree.infer? = some sequent
  desequentialized : tree.desequentialize? = some output
  outputLabels : output.conclusionFormulas? = some sequent
  equivalent : output.ProofNetEquivalent input

namespace SequentializationResult

/-- Recover the exact internal fragment behind the public output certificate;
its stored formula boundary is the independently inferred sequent. -/
theorem fragment_exists {input : Certificate}
    (result : SequentializationResult input) :
    ∃ fragment : NetFragment,
      result.tree.build? = some fragment ∧
      fragment.toCertificate = result.output ∧
      fragment.conclusions = result.sequent := by
  rcases CutFreeDerivation.build?_exists_of_desequentialize?
      result.desequentialized with
    ⟨fragment, buildEquation, certificateEquation⟩
  have inferredFromBuild := CutFreeDerivation.infer?_of_build? buildEquation
  have conclusionsEquation : fragment.conclusions = result.sequent := by
    exact Option.some.inj (inferredFromBuild.symm.trans result.inferred)
  exact ⟨fragment, buildEquation, certificateEquation, conclusionsEquation⟩

/-- A sequentialization result always contains a kernel-typed object-logic
derivation; this does not trust the proof-net checker. -/
theorem kernelDerivation {input : Certificate}
    (result : SequentializationResult input) :
    Nonempty (Derivation result.sequent) :=
  result.tree.infer?_sound result.inferred

/-- Proof-net equivalence transports the ordered conclusion formulas from the
desequentialized output back to the input certificate. -/
theorem inputLabels {input : Certificate}
    (result : SequentializationResult input) :
    input.conclusionFormulas? = some result.sequent := by
  calc
    input.conclusionFormulas? = result.output.conclusionFormulas? :=
      result.equivalent.conclusionFormulas?_eq.symm
    _ = some result.sequent := result.outputLabels

/-- If the input was accepted, the reconstructed proof net is accepted as
well. This follows from proved equivalence invariance, not from rerunning and
assuming the checker. -/
theorem outputAccepted {input : Certificate}
    (result : SequentializationResult input)
    (accepted : input.check = true) :
    result.output.check = true := by
  rw [result.equivalent.check_eq]
  exact accepted

/-- Package a successful general sequentialization in the existing checked
derivation/certificate API. -/
def toElaboratedCertificate {input : Certificate}
    (result : SequentializationResult input)
    (accepted : input.check = true) :
    CutFreeDerivation.ElaboratedCertificate where
  sequent := result.sequent
  derivation := result.kernelDerivation
  certificate := result.output
  conclusionLabels := result.outputLabels
  accepted := result.outputAccepted accepted

end SequentializationResult

/-- The exact macro theorem still to be constructed by terminal-par peeling,
splitting-tensor decomposition, and well-founded recursion. Keeping it as a
named proposition prevents a search routine from being mistaken for the
mathematical theorem. -/
def GenerallySequentializable : Prop :=
  ∀ input : Certificate,
    input.check = true → Nonempty (SequentializationResult input)

/-- The purely logical projection of sequentialization.  It records an
independent kernel-typed sequent derivation with exactly the input boundary
labels, while omitting the stronger desequentialized-net equivalence field.
Keeping this intermediate contract explicit lets the recursive rule proof and
the graph-reconstruction proof be audited separately. -/
structure LogicalSequentializationResult (input : Certificate) where
  sequent : List Formula
  derivation : Nonempty (Derivation sequent)
  inputLabels : input.conclusionFormulas? = some sequent

/-- Every checker-accepted certificate has a kernel sequent derivation with
exactly its ordered conclusion formulas.  This intentionally omits the
stronger requirement that desequentializing a first-order tree reconstructs
an equivalent proof net. -/
def LogicallySequentializable : Prop :=
  ∀ input : Certificate,
    input.check = true → Nonempty (LogicalSequentializationResult input)

namespace LogicalSequentializationResult

/-- Forget only the graph-reconstruction fields of a full sequentialization
result; the sequent derivation and exact ordered input boundary are retained. -/
def ofSequentialization {input : Certificate}
    (result : SequentializationResult input) :
    LogicalSequentializationResult input where
  sequent := result.sequent
  derivation := result.kernelDerivation
  inputLabels := result.inputLabels

/-- Logical composition for an inverse terminal-par step.  All occurrence
bookkeeping is summarized by two explicit equations: the premise ends in the
two selected formulas, and the rebuilt par boundary is a permutation of the
target input boundary. -/
def parRule {input premise : Certificate}
    (premiseResult : LogicalSequentializationResult premise)
    (context : List Formula) (left right : Formula)
    (premiseSequent : premiseResult.sequent = context ++ [left, right])
    (inputSequent : List Formula)
    (inputLabels : input.conclusionFormulas? = some inputSequent)
    (rebuiltBoundary :
      (context ++ [Formula.par left right]).Perm inputSequent) :
    LogicalSequentializationResult input := by
  have rebuiltDerivation : Nonempty (Derivation inputSequent) := by
    rcases premiseResult.derivation with ⟨premiseProof⟩
    have focused : Derivation (context ++ [left, right]) :=
      premiseSequent ▸ premiseProof
    let rebuilt : Derivation (context ++ [Formula.par left right]) :=
      Derivation.parTail focused
    exact ⟨Derivation.exchange rebuiltBoundary rebuilt⟩
  exact {
    sequent := inputSequent
    derivation := rebuiltDerivation
    inputLabels }

/-- Logical composition for an inverse splitting-tensor step.  Each child
derivation is focused from its final boundary occurrence to the head, tensor
is applied, and explicit exchange restores the target ordered boundary. -/
def tensorRule {input leftPremise rightPremise : Certificate}
    (leftResult : LogicalSequentializationResult leftPremise)
    (rightResult : LogicalSequentializationResult rightPremise)
    (leftContext rightContext : List Formula) (left right : Formula)
    (leftSequent : leftResult.sequent = leftContext ++ [left])
    (rightSequent : rightResult.sequent = rightContext ++ [right])
    (inputSequent : List Formula)
    (inputLabels : input.conclusionFormulas? = some inputSequent)
    (rebuiltBoundary :
      (.tensor left right :: (leftContext ++ rightContext)).Perm inputSequent) :
    LogicalSequentializationResult input := by
  have rebuiltDerivation : Nonempty (Derivation inputSequent) := by
    rcases leftResult.derivation with ⟨leftProof⟩
    rcases rightResult.derivation with ⟨rightProof⟩
    have leftTail : Derivation (leftContext ++ [left]) :=
      leftSequent ▸ leftProof
    have rightTail : Derivation (rightContext ++ [right]) :=
      rightSequent ▸ rightProof
    have leftToFront : (leftContext ++ [left]).Perm
        (left :: leftContext) := by
      exact List.perm_append_comm
    have rightToFront : (rightContext ++ [right]).Perm
        (right :: rightContext) := by
      exact List.perm_append_comm
    have leftFocused : Derivation (left :: leftContext) :=
      Derivation.exchange leftToFront leftTail
    have rightFocused : Derivation (right :: rightContext) :=
      Derivation.exchange rightToFront rightTail
    let rebuilt : Derivation
        (.tensor left right :: (leftContext ++ rightContext)) :=
      Derivation.tensor leftFocused rightFocused
    exact ⟨Derivation.exchange rebuiltBoundary rebuilt⟩
  exact {
    sequent := inputSequent
    derivation := rebuiltDerivation
    inputLabels }

end LogicalSequentializationResult

namespace Certificate

/-- Structural well-formedness makes every ordered boundary lookup total.
The result is stated using `getD` only to expose a concrete list without
introducing dependent array indices; the fallback is unreachable. -/
theorem StructurallyWellFormed.conclusionFormulas?_eq_getD
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    (fallback : Formula) :
    certificate.conclusionFormulas? = some
      (certificate.conclusions.map fun vertex =>
        certificate.formulas.getD vertex fallback) := by
  unfold conclusionFormulas?
  apply list_mapM_eq_some_map_of_forall
  intro vertex membership
  have inBounds := structural.2.2.1 vertex membership
  simp [formula?, inBounds]

/-- Total compaction map used once the deleted occurrence is known not to be
the input vertex. -/
def compactVertex (removed vertex : Nat) : Nat :=
  if vertex < removed then vertex else vertex - 1

/-- Order-preserving embedding from compacted names back into the original
vertex interval. -/
def expandVertex (removed vertex : Nat) : Nat :=
  if vertex < removed then vertex else vertex + 1

/-- Compact an old vertex name after deleting one formula occurrence. -/
def deleteVertex? (removed vertex : Vertex) : Option Vertex :=
  if vertex = removed then
    none
  else
    some (compactVertex removed vertex)

@[simp] theorem deleteVertex?_self (vertex : Vertex) :
    deleteVertex? vertex vertex = none := by
  simp [deleteVertex?]

theorem deleteVertex?_of_lt {removed vertex : Vertex}
    (before : vertex < removed) :
    deleteVertex? removed vertex = some vertex := by
  simp [deleteVertex?, compactVertex, Nat.ne_of_lt before, before]

theorem deleteVertex?_of_gt {removed vertex : Vertex}
    (after : removed < vertex) :
    deleteVertex? removed vertex = some (vertex - 1) := by
  simp [deleteVertex?, compactVertex, Nat.ne_of_gt after,
    Nat.not_lt.mpr (Nat.le_of_lt after)]

theorem deleteVertex?_eq_some_of_ne {removed vertex : Vertex}
    (different : vertex ≠ removed) :
    deleteVertex? removed vertex = some (compactVertex removed vertex) := by
  simp [deleteVertex?, different]

@[simp] theorem compactVertex_expandVertex (removed vertex : Nat) :
    compactVertex removed (expandVertex removed vertex) = vertex := by
  by_cases before : vertex < removed
  · simp [compactVertex, expandVertex, before]
  · have notBefore : ¬vertex + 1 < removed := by omega
    simp [compactVertex, expandVertex, before, notBefore]

theorem expandVertex_compactVertex_of_ne {removed vertex : Nat}
    (different : vertex ≠ removed) :
    expandVertex removed (compactVertex removed vertex) = vertex := by
  by_cases before : vertex < removed
  · simp [compactVertex, expandVertex, before]
  · have after : removed < vertex := by omega
    have compactNotBefore : ¬vertex - 1 < removed := by omega
    simp [compactVertex, expandVertex, before, compactNotBefore]
    omega

theorem compactVertex_injective_of_ne {removed first second : Nat}
    (firstNotRemoved : first ≠ removed)
    (secondNotRemoved : second ≠ removed)
    (same : compactVertex removed first = compactVertex removed second) :
    first = second := by
  have expanded := congrArg (expandVertex removed) same
  simpa [expandVertex_compactVertex_of_ne firstNotRemoved,
    expandVertex_compactVertex_of_ne secondNotRemoved] using expanded

theorem compactVertex_lt {removed vertex bound : Nat}
    (removedInBounds : removed < bound) (vertexInBounds : vertex < bound)
    (different : vertex ≠ removed) :
    compactVertex removed vertex < bound - 1 := by
  by_cases before : vertex < removed
  · simp [compactVertex, before]
    omega
  · simp [compactVertex, before]
    omega

theorem expandVertex_lt {removed vertex bound : Nat}
    (removedInBounds : removed < bound)
    (vertexInBounds : vertex < bound - 1) :
    expandVertex removed vertex < bound := by
  by_cases before : vertex < removed
  · simp [expandVertex, before]
    omega
  · simp [expandVertex, before]
    omega

theorem expandVertex_ne (removed vertex : Nat) :
    expandVertex removed vertex ≠ removed := by
  by_cases before : vertex < removed
  · simp [expandVertex, before]
    omega
  · simp [expandVertex, before]
    omega

end Certificate

namespace Link

/-- Delete one formula occurrence and compact every remaining endpoint. A
link incident to the deleted occurrence is removed. -/
def deleteVertex? (removed : Vertex) : Link → Option Link
  | .axiom left right => do
      let left' ← Certificate.deleteVertex? removed left
      let right' ← Certificate.deleteVertex? removed right
      pure (.axiom left' right')
  | .tensor left right conclusion => do
      let left' ← Certificate.deleteVertex? removed left
      let right' ← Certificate.deleteVertex? removed right
      let conclusion' ← Certificate.deleteVertex? removed conclusion
      pure (.tensor left' right' conclusion')
  | .par left right conclusion => do
      let left' ← Certificate.deleteVertex? removed left
      let right' ← Certificate.deleteVertex? removed right
      let conclusion' ← Certificate.deleteVertex? removed conclusion
      pure (.par left' right' conclusion')

def compactVertices (removed : Vertex) : Link → Link
  | .axiom first second =>
      .axiom (Certificate.compactVertex removed first)
        (Certificate.compactVertex removed second)
  | .tensor first second result =>
      .tensor (Certificate.compactVertex removed first)
        (Certificate.compactVertex removed second)
        (Certificate.compactVertex removed result)
  | .par first second result =>
      .par (Certificate.compactVertex removed first)
        (Certificate.compactVertex removed second)
        (Certificate.compactVertex removed result)

/-- Inserting the deleted position back at the final compacted vertex restores
every endpoint of a link which avoided that position. -/
theorem reindex_insertLastAt_compactVertices
    {oldBound removed : Nat}
    (removedInBounds : removed < oldBound + 1) (link : Link)
    (inBounds : ∀ vertex ∈ link.vertices, vertex < oldBound + 1)
    (avoids : removed ∉ link.vertices) :
    (link.compactVertices removed).reindex
        (VertexRenaming.insertLastAt oldBound removed removedInBounds) =
      link := by
  let placement := VertexRenaming.insertLastAt oldBound removed removedInBounds
  have restored : ∀ vertex ∈ link.vertices,
      placement.forward (Certificate.compactVertex removed vertex) = vertex := by
    intro vertex membership
    have vertexInBounds := inBounds vertex membership
    have vertexNotRemoved : vertex ≠ removed := by
      intro same
      subst vertex
      exact avoids membership
    have compactInBounds : Certificate.compactVertex removed vertex < oldBound := by
      have compactBound := Certificate.compactVertex_lt removedInBounds
        vertexInBounds vertexNotRemoved
      simpa using compactBound
    rw [VertexRenaming.insertLastAt_forward_old _ _ removedInBounds
      compactInBounds]
    change Certificate.expandVertex removed
      (Certificate.compactVertex removed vertex) = vertex
    exact Certificate.expandVertex_compactVertex_of_ne vertexNotRemoved
  cases link with
  | «axiom» left right =>
      simp only [compactVertices, reindex]
      rw [restored left (by simp [vertices]),
        restored right (by simp [vertices])]
  | tensor left right conclusion =>
      simp only [compactVertices, reindex]
      rw [restored left (by simp [vertices]),
        restored right (by simp [vertices]),
        restored conclusion (by simp [vertices])]
  | par left right conclusion =>
      simp only [compactVertices, reindex]
      rw [restored left (by simp [vertices]),
        restored right (by simp [vertices]),
        restored conclusion (by simp [vertices])]

theorem deleteVertex?_eq_some_iff (link compacted : Link)
    (removed : Vertex) :
    link.deleteVertex? removed = some compacted ↔
      removed ∉ link.vertices ∧ compacted = link.compactVertices removed := by
  cases link with
  | «axiom» first second =>
      by_cases firstRemoved : removed = first <;>
      by_cases secondRemoved : removed = second <;>
        simp [deleteVertex?, Certificate.deleteVertex?, compactVertices,
          vertices, firstRemoved, secondRemoved, eq_comm]
  | tensor first second result =>
      by_cases firstRemoved : removed = first <;>
      by_cases secondRemoved : removed = second <;>
      by_cases resultRemoved : removed = result <;>
        simp [deleteVertex?, Certificate.deleteVertex?, compactVertices,
          vertices, firstRemoved, secondRemoved, resultRemoved, eq_comm]
  | par first second result =>
      by_cases firstRemoved : removed = first <;>
      by_cases secondRemoved : removed = second <;>
      by_cases resultRemoved : removed = result <;>
        simp [deleteVertex?, Certificate.deleteVertex?, compactVertices,
          vertices, firstRemoved, secondRemoved, resultRemoved, eq_comm]

theorem deleteVertex?_eq_none_iff (link : Link) (removed : Vertex) :
    link.deleteVertex? removed = none ↔ removed ∈ link.vertices := by
  cases link with
  | «axiom» first second =>
      by_cases firstRemoved : removed = first <;>
      by_cases secondRemoved : removed = second <;>
        simp [deleteVertex?, Certificate.deleteVertex?, vertices,
          firstRemoved, secondRemoved, eq_comm]
  | tensor first second result =>
      by_cases firstRemoved : removed = first <;>
      by_cases secondRemoved : removed = second <;>
      by_cases resultRemoved : removed = result <;>
        simp [deleteVertex?, Certificate.deleteVertex?, vertices,
          firstRemoved, secondRemoved, resultRemoved, eq_comm]
  | par first second result =>
      by_cases firstRemoved : removed = first <;>
      by_cases secondRemoved : removed = second <;>
      by_cases resultRemoved : removed = result <;>
        simp [deleteVertex?, Certificate.deleteVertex?, vertices,
          firstRemoved, secondRemoved, resultRemoved, eq_comm]

theorem containsAxiomEndpoint_deleteVertex?_eq_some
    {link compacted : Link} {removed vertex : Vertex}
    (vertexNotRemoved : vertex ≠ removed)
    (deleted : link.deleteVertex? removed = some compacted) :
    compacted.containsAxiomEndpoint (Certificate.compactVertex removed vertex) =
      link.containsAxiomEndpoint vertex := by
  rcases (deleteVertex?_eq_some_iff link compacted removed).mp deleted with
    ⟨avoids, rfl⟩
  cases link with
  | «axiom» first second =>
      simp [vertices] at avoids
      have firstNotRemoved : first ≠ removed := Ne.symm avoids.1
      have secondNotRemoved : second ≠ removed := Ne.symm avoids.2
      apply Bool.eq_iff_iff.mpr
      simp only [compactVertices, containsAxiomEndpoint, Bool.or_eq_true,
        beq_iff_eq]
      constructor
      · intro membership
        rcases membership with same | same
        · exact Or.inl (Certificate.compactVertex_injective_of_ne
            firstNotRemoved vertexNotRemoved same)
        · exact Or.inr (Certificate.compactVertex_injective_of_ne
            secondNotRemoved vertexNotRemoved same)
      · intro membership
        rcases membership with rfl | rfl <;> simp
  | tensor first second result => rfl
  | par first second result => rfl

theorem produces_deleteVertex?_eq_some
    {link compacted : Link} {removed vertex : Vertex}
    (vertexNotRemoved : vertex ≠ removed)
    (deleted : link.deleteVertex? removed = some compacted) :
    compacted.produces (Certificate.compactVertex removed vertex) =
      link.produces vertex := by
  rcases (deleteVertex?_eq_some_iff link compacted removed).mp deleted with
    ⟨avoids, rfl⟩
  cases link with
  | «axiom» first second => rfl
  | tensor first second result =>
      simp [vertices] at avoids
      have resultNotRemoved : result ≠ removed := Ne.symm avoids.2.2
      apply Bool.eq_iff_iff.mpr
      simp only [compactVertices, produces, beq_iff_eq]
      constructor
      · exact Certificate.compactVertex_injective_of_ne
          resultNotRemoved vertexNotRemoved
      · intro same
        subst result
        rfl
  | par first second result =>
      simp [vertices] at avoids
      have resultNotRemoved : result ≠ removed := Ne.symm avoids.2.2
      apply Bool.eq_iff_iff.mpr
      simp only [compactVertices, produces, beq_iff_eq]
      constructor
      · exact Certificate.compactVertex_injective_of_ne
          resultNotRemoved vertexNotRemoved
      · intro same
        subst result
        rfl

theorem usesAsPremise_deleteVertex?_eq_some
    {link compacted : Link} {removed vertex : Vertex}
    (vertexNotRemoved : vertex ≠ removed)
    (deleted : link.deleteVertex? removed = some compacted) :
    compacted.usesAsPremise (Certificate.compactVertex removed vertex) =
      link.usesAsPremise vertex := by
  rcases (deleteVertex?_eq_some_iff link compacted removed).mp deleted with
    ⟨avoids, rfl⟩
  cases link with
  | «axiom» first second => rfl
  | tensor first second result =>
      simp [vertices] at avoids
      have firstNotRemoved : first ≠ removed := Ne.symm avoids.1
      have secondNotRemoved : second ≠ removed := Ne.symm avoids.2.1
      apply Bool.eq_iff_iff.mpr
      simp only [compactVertices, usesAsPremise, premises,
        List.contains_cons, List.contains_nil, Bool.or_false, Bool.or_eq_true,
        beq_iff_eq]
      constructor
      · intro membership
        rcases membership with same | same
        · exact Or.inl (Certificate.compactVertex_injective_of_ne
            vertexNotRemoved firstNotRemoved same)
        · exact Or.inr (Certificate.compactVertex_injective_of_ne
            vertexNotRemoved secondNotRemoved same)
      · intro membership
        rcases membership with rfl | rfl <;> simp
  | par first second result =>
      simp [vertices] at avoids
      have firstNotRemoved : first ≠ removed := Ne.symm avoids.1
      have secondNotRemoved : second ≠ removed := Ne.symm avoids.2.1
      apply Bool.eq_iff_iff.mpr
      simp only [compactVertices, usesAsPremise, premises,
        List.contains_cons, List.contains_nil, Bool.or_false, Bool.or_eq_true,
        beq_iff_eq]
      constructor
      · intro membership
        rcases membership with same | same
        · exact Or.inl (Certificate.compactVertex_injective_of_ne
            vertexNotRemoved firstNotRemoved same)
        · exact Or.inr (Certificate.compactVertex_injective_of_ne
            vertexNotRemoved secondNotRemoved same)
      · intro membership
        rcases membership with rfl | rfl <;> simp

/-- Reindex a link into a listed vertex subset. Links crossing the subset
boundary are rejected. -/
def restrictTo? (vertices : List Vertex) : Link → Option Link
  | .axiom left right => do
      let left' ← vertices.idxOf? left
      let right' ← vertices.idxOf? right
      pure (.axiom left' right')
  | .tensor left right conclusion => do
      let left' ← vertices.idxOf? left
      let right' ← vertices.idxOf? right
      let conclusion' ← vertices.idxOf? conclusion
      pure (.tensor left' right' conclusion')
  | .par left right conclusion => do
      let left' ← vertices.idxOf? left
      let right' ← vertices.idxOf? right
      let conclusion' ← vertices.idxOf? conclusion
      pure (.par left' right' conclusion')

theorem restrictTo?_eq_some_of_vertices
    (link : Link) (vertices : List Vertex)
    (contained : ∀ vertex ∈ link.vertices, vertex ∈ vertices) :
    link.restrictTo? vertices = some (match link with
      | .axiom left right =>
          .axiom (vertices.idxOf left) (vertices.idxOf right)
      | .tensor left right conclusion =>
          .tensor (vertices.idxOf left) (vertices.idxOf right)
            (vertices.idxOf conclusion)
      | .par left right conclusion =>
          .par (vertices.idxOf left) (vertices.idxOf right)
            (vertices.idxOf conclusion)) := by
  cases link with
  | «axiom» left right =>
      have leftContained := contained left (by simp [Link.vertices])
      have rightContained := contained right (by simp [Link.vertices])
      simp [restrictTo?, idxOf?_eq_some_idxOf_of_mem leftContained,
        idxOf?_eq_some_idxOf_of_mem rightContained]
  | tensor left right conclusion =>
      have leftContained := contained left (by simp [Link.vertices])
      have rightContained := contained right (by simp [Link.vertices])
      have conclusionContained := contained conclusion (by simp [Link.vertices])
      simp [restrictTo?, idxOf?_eq_some_idxOf_of_mem leftContained,
        idxOf?_eq_some_idxOf_of_mem rightContained,
        idxOf?_eq_some_idxOf_of_mem conclusionContained]
  | par left right conclusion =>
      have leftContained := contained left (by simp [Link.vertices])
      have rightContained := contained right (by simp [Link.vertices])
      have conclusionContained := contained conclusion (by simp [Link.vertices])
      simp [restrictTo?, idxOf?_eq_some_idxOf_of_mem leftContained,
        idxOf?_eq_some_idxOf_of_mem rightContained,
        idxOf?_eq_some_idxOf_of_mem conclusionContained]

theorem vertices_mem_of_restrictTo?_eq_some
    {link restricted : Link} {vertices : List Vertex}
    (equation : link.restrictTo? vertices = some restricted) :
    ∀ vertex ∈ link.vertices, vertex ∈ vertices := by
  cases link with
  | «axiom» left right =>
      cases leftEquation : vertices.idxOf? left with
      | none => simp [restrictTo?, leftEquation] at equation
      | some leftIndex =>
          cases rightEquation : vertices.idxOf? right with
          | none => simp [restrictTo?, leftEquation, rightEquation] at equation
          | some rightIndex =>
              intro vertex membership
              simp [Link.vertices] at membership
              rcases membership with rfl | rfl
              · exact mem_of_idxOf?_eq_some leftEquation
              · exact mem_of_idxOf?_eq_some rightEquation
  | tensor left right conclusion =>
      cases leftEquation : vertices.idxOf? left with
      | none => simp [restrictTo?, leftEquation] at equation
      | some leftIndex =>
          cases rightEquation : vertices.idxOf? right with
          | none => simp [restrictTo?, leftEquation, rightEquation] at equation
          | some rightIndex =>
              cases conclusionEquation : vertices.idxOf? conclusion with
              | none =>
                  simp [restrictTo?, leftEquation, rightEquation,
                    conclusionEquation] at equation
              | some conclusionIndex =>
                  intro vertex membership
                  simp [Link.vertices] at membership
                  rcases membership with rfl | rfl | rfl
                  · exact mem_of_idxOf?_eq_some leftEquation
                  · exact mem_of_idxOf?_eq_some rightEquation
                  · exact mem_of_idxOf?_eq_some conclusionEquation
  | par left right conclusion =>
      cases leftEquation : vertices.idxOf? left with
      | none => simp [restrictTo?, leftEquation] at equation
      | some leftIndex =>
          cases rightEquation : vertices.idxOf? right with
          | none => simp [restrictTo?, leftEquation, rightEquation] at equation
          | some rightIndex =>
              cases conclusionEquation : vertices.idxOf? conclusion with
              | none =>
                  simp [restrictTo?, leftEquation, rightEquation,
                    conclusionEquation] at equation
              | some conclusionIndex =>
                  intro vertex membership
                  simp [Link.vertices] at membership
                  rcases membership with rfl | rfl | rfl
                  · exact mem_of_idxOf?_eq_some leftEquation
                  · exact mem_of_idxOf?_eq_some rightEquation
                  · exact mem_of_idxOf?_eq_some conclusionEquation

theorem restrictTo?_produces
    {link restricted : Link} {vertices : List Vertex} {vertex : Vertex}
    (equation : link.restrictTo? vertices = some restricted)
    (vertexContained : vertex ∈ vertices) :
    restricted.produces (vertices.idxOf vertex) = link.produces vertex := by
  have contained := Link.vertices_mem_of_restrictTo?_eq_some equation
  have exactEquation := Link.restrictTo?_eq_some_of_vertices link vertices contained
  rw [exactEquation] at equation
  cases equation
  cases link with
  | «axiom» left right => rfl
  | tensor left right conclusion =>
      have conclusionContained := contained conclusion (by simp [Link.vertices])
      apply Bool.eq_iff_iff.mpr
      simp only [produces, beq_iff_eq]
      constructor
      · exact idxOf_injective_of_mem conclusionContained vertexContained
      · intro same
        subst conclusion
        rfl
  | par left right conclusion =>
      have conclusionContained := contained conclusion (by simp [Link.vertices])
      apply Bool.eq_iff_iff.mpr
      simp only [produces, beq_iff_eq]
      constructor
      · exact idxOf_injective_of_mem conclusionContained vertexContained
      · intro same
        subst conclusion
        rfl

theorem restrictTo?_containsAxiomEndpoint
    {link restricted : Link} {vertices : List Vertex} {vertex : Vertex}
    (equation : link.restrictTo? vertices = some restricted)
    (vertexContained : vertex ∈ vertices) :
    restricted.containsAxiomEndpoint (vertices.idxOf vertex) =
      link.containsAxiomEndpoint vertex := by
  have contained := Link.vertices_mem_of_restrictTo?_eq_some equation
  have exactEquation := Link.restrictTo?_eq_some_of_vertices link vertices contained
  rw [exactEquation] at equation
  cases equation
  cases link with
  | «axiom» left right =>
      have leftContained := contained left (by simp [Link.vertices])
      have rightContained := contained right (by simp [Link.vertices])
      apply Bool.eq_iff_iff.mpr
      simp only [containsAxiomEndpoint, Bool.or_eq_true, beq_iff_eq]
      constructor
      · intro endpoint
        rcases endpoint with endpoint | endpoint
        · exact Or.inl
            (idxOf_injective_of_mem leftContained vertexContained endpoint)
        · exact Or.inr
            (idxOf_injective_of_mem rightContained vertexContained endpoint)
      · intro endpoint
        rcases endpoint with rfl | rfl <;> simp
  | tensor left right conclusion => rfl
  | par left right conclusion => rfl

theorem restrictTo?_usesAsPremise
    {link restricted : Link} {vertices : List Vertex} {vertex : Vertex}
    (equation : link.restrictTo? vertices = some restricted)
    (vertexContained : vertex ∈ vertices) :
    restricted.usesAsPremise (vertices.idxOf vertex) =
      link.usesAsPremise vertex := by
  have contained := Link.vertices_mem_of_restrictTo?_eq_some equation
  have exactEquation := Link.restrictTo?_eq_some_of_vertices link vertices contained
  rw [exactEquation] at equation
  cases equation
  cases link with
  | «axiom» left right => rfl
  | tensor left right conclusion =>
      have leftContained := contained left (by simp [Link.vertices])
      have rightContained := contained right (by simp [Link.vertices])
      apply Bool.eq_iff_iff.mpr
      simp only [usesAsPremise, premises, List.contains_cons,
        List.contains_nil, Bool.or_false, Bool.or_eq_true, beq_iff_eq]
      constructor
      · intro premise
        rcases premise with premise | premise
        · exact Or.inl
            (idxOf_injective_of_mem vertexContained leftContained premise)
        · exact Or.inr
            (idxOf_injective_of_mem vertexContained rightContained premise)
      · intro premise
        rcases premise with rfl | rfl <;> simp
  | par left right conclusion =>
      have leftContained := contained left (by simp [Link.vertices])
      have rightContained := contained right (by simp [Link.vertices])
      apply Bool.eq_iff_iff.mpr
      simp only [usesAsPremise, premises, List.contains_cons,
        List.contains_nil, Bool.or_false, Bool.or_eq_true, beq_iff_eq]
      constructor
      · intro premise
        rcases premise with premise | premise
        · exact Or.inl
            (idxOf_injective_of_mem vertexContained leftContained premise)
        · exact Or.inr
            (idxOf_injective_of_mem vertexContained rightContained premise)
      · intro premise
        rcases premise with rfl | rfl <;> simp

theorem produces_eq_false_of_not_mem_vertices
    (link : Link) {vertex : Vertex} (notIncident : vertex ∉ link.vertices) :
    link.produces vertex = false := by
  cases link with
  | «axiom» left right => rfl
  | tensor left right conclusion =>
      simp [Link.vertices] at notIncident
      simp [produces, Ne.symm notIncident.2.2]
  | par left right conclusion =>
      simp [Link.vertices] at notIncident
      simp [produces, Ne.symm notIncident.2.2]

theorem containsAxiomEndpoint_eq_false_of_not_mem_vertices
    (link : Link) {vertex : Vertex} (notIncident : vertex ∉ link.vertices) :
    link.containsAxiomEndpoint vertex = false := by
  cases link with
  | «axiom» left right =>
      simp [Link.vertices] at notIncident
      simp [containsAxiomEndpoint, Ne.symm notIncident.1,
        Ne.symm notIncident.2]
  | tensor left right conclusion => rfl
  | par left right conclusion => rfl

theorem usesAsPremise_eq_false_of_not_mem_vertices
    (link : Link) {vertex : Vertex} (notIncident : vertex ∉ link.vertices) :
    link.usesAsPremise vertex = false := by
  cases link with
  | «axiom» left right => rfl
  | tensor left right conclusion =>
      simp [Link.vertices] at notIncident
      simp [usesAsPremise, premises, notIncident.1, notIncident.2.1]
  | par left right conclusion =>
      simp [Link.vertices] at notIncident
      simp [usesAsPremise, premises, notIncident.1, notIncident.2.1]

end Link

namespace Edge

def incident (edge : Edge) (vertex : Vertex) : Bool :=
  edge.first == vertex || edge.second == vertex

@[simp] theorem incident_mk (first second vertex : Vertex) :
    (Edge.mk first second).incident vertex =
      (first == vertex || second == vertex) := rfl

def deleteVertex? (removed : Vertex) (edge : Edge) : Option Edge := do
  let first ← Certificate.deleteVertex? removed edge.first
  let second ← Certificate.deleteVertex? removed edge.second
  pure { first, second }

/-- Reindex an edge into a listed occurrence component. -/
def restrictTo? (vertices : List Vertex) (edge : Edge) : Option Edge := do
  let first ← vertices.idxOf? edge.first
  let second ← vertices.idxOf? edge.second
  pure { first, second }

theorem restrictTo?_eq_some_of_mem (edge : Edge) (vertices : List Vertex)
    (firstContained : edge.first ∈ vertices)
    (secondContained : edge.second ∈ vertices) :
    edge.restrictTo? vertices = some {
      first := vertices.idxOf edge.first
      second := vertices.idxOf edge.second } := by
  simp [restrictTo?, idxOf?_eq_some_idxOf_of_mem firstContained,
    idxOf?_eq_some_idxOf_of_mem secondContained]

theorem restrictTo?_eq_some {vertices : List Vertex} {edge restricted : Edge}
    (equation : edge.restrictTo? vertices = some restricted) :
    edge.first ∈ vertices ∧ edge.second ∈ vertices ∧
      restricted = {
        first := vertices.idxOf edge.first
        second := vertices.idxOf edge.second } := by
  cases firstEquation : vertices.idxOf? edge.first with
  | none => simp [restrictTo?, firstEquation] at equation
  | some first =>
      cases secondEquation : vertices.idxOf? edge.second with
      | none => simp [restrictTo?, firstEquation, secondEquation] at equation
      | some second =>
          simp [restrictTo?, firstEquation, secondEquation] at equation
          subst restricted
          have firstMembership := mem_of_idxOf?_eq_some firstEquation
          have secondMembership := mem_of_idxOf?_eq_some secondEquation
          have firstIndex := idxOf?_eq_some_idxOf_of_mem firstMembership
          have secondIndex := idxOf?_eq_some_idxOf_of_mem secondMembership
          rw [firstEquation] at firstIndex
          rw [secondEquation] at secondIndex
          simp at firstIndex secondIndex
          subst first
          subst second
          exact ⟨firstMembership, secondMembership, rfl⟩

def expandVertex (removed : Vertex) (edge : Edge) : Edge :=
  { first := Certificate.expandVertex removed edge.first
    second := Certificate.expandVertex removed edge.second }

theorem deleteVertex?_eq_some {removed : Vertex} {edge compacted : Edge}
    (accepted : edge.deleteVertex? removed = some compacted) :
    edge.first ≠ removed ∧ edge.second ≠ removed ∧
      compacted = {
        first := Certificate.compactVertex removed edge.first
        second := Certificate.compactVertex removed edge.second } := by
  rcases edge with ⟨first, second⟩
  by_cases firstDeleted : first = removed
  · simp [deleteVertex?, Certificate.deleteVertex?, firstDeleted] at accepted
  · by_cases secondDeleted : second = removed
    · simp [deleteVertex?, Certificate.deleteVertex?, firstDeleted,
        secondDeleted] at accepted
    · simp [deleteVertex?, Certificate.deleteVertex?, firstDeleted,
        secondDeleted] at accepted
      subst compacted
      exact ⟨firstDeleted, secondDeleted, rfl⟩

theorem deleteVertex?_eq_some_of_ne (edge : Edge) (removed : Vertex)
    (firstNotRemoved : edge.first ≠ removed)
    (secondNotRemoved : edge.second ≠ removed) :
    edge.deleteVertex? removed = some {
      first := Certificate.compactVertex removed edge.first
      second := Certificate.compactVertex removed edge.second } := by
  rcases edge with ⟨first, second⟩
  simp [deleteVertex?, Certificate.deleteVertex?, firstNotRemoved,
    secondNotRemoved]

theorem deleteVertex?_isSome (edge : Edge) (removed : Vertex) :
    (edge.deleteVertex? removed).isSome = !edge.incident removed := by
  rcases edge with ⟨first, second⟩
  by_cases firstRemoved : first = removed <;>
  by_cases secondRemoved : second = removed <;>
    simp [deleteVertex?, Certificate.deleteVertex?, incident,
      firstRemoved, secondRemoved]

end Edge

namespace ParChoice

/-- Delete one occurrence from both alternatives of a par switching choice.
The choice survives only when both alternative edges survive. -/
def deleteVertex? (removed : Vertex) (choice : Edge × Edge) :
    Option (Edge × Edge) := do
  let first ← choice.1.deleteVertex? removed
  let second ← choice.2.deleteVertex? removed
  pure (first, second)

/-- Restrict both alternatives of a par switching choice to one component. -/
def restrictTo? (vertices : List Vertex) (choice : Edge × Edge) :
    Option (Edge × Edge) := do
  let first ← choice.1.restrictTo? vertices
  let second ← choice.2.restrictTo? vertices
  pure (first, second)

end ParChoice

namespace Graph

private noncomputable def shortestWalkSteps (graph : Graph)
    (vertex : Vertex) : Nat := by
  classical
  exact if reachable : ∃ steps, graph.WalkN 0 steps vertex then
    Classical.choose (exists_least_nat
      (fun steps => graph.WalkN 0 steps vertex) reachable)
  else 0

private theorem walkN_shortestWalkSteps (graph : Graph) (vertex : Vertex)
    (reachable : ∃ steps, graph.WalkN 0 steps vertex) :
    graph.WalkN 0 (graph.shortestWalkSteps vertex) vertex := by
  unfold shortestWalkSteps
  rw [dif_pos reachable]
  exact (Classical.choose_spec (exists_least_nat
    (fun steps => graph.WalkN 0 steps vertex) reachable)).1

private theorem shortestWalkSteps_le (graph : Graph) {vertex : Vertex}
    {steps : Nat} (walk : graph.WalkN 0 steps vertex) :
    graph.shortestWalkSteps vertex ≤ steps := by
  have reachable : ∃ candidate, graph.WalkN 0 candidate vertex :=
    ⟨steps, walk⟩
  unfold shortestWalkSteps
  rw [dif_pos reachable]
  exact (Classical.choose_spec (exists_least_nat
    (fun candidate => graph.WalkN 0 candidate vertex) reachable)).2 steps walk

private def IsRootedParentEdge (graph : Graph) (vertex : Vertex)
    (edge : Edge) : Prop :=
  ∃ predecessor,
    edge ∈ graph.edges ∧
    ((edge.first = predecessor ∧ edge.second = vertex) ∨
      (edge.first = vertex ∧ edge.second = predecessor)) ∧
    graph.shortestWalkSteps predecessor < graph.shortestWalkSteps vertex

theorem WalkN.lastEdge {graph : Graph} {root vertex : Vertex} {steps : Nat}
    (walk : graph.WalkN root steps vertex) (nonRoot : vertex ≠ root) :
    ∃ priorSteps predecessor edge,
      graph.WalkN root priorSteps predecessor ∧
      edge ∈ graph.edges ∧
      ((edge.first = predecessor ∧ edge.second = vertex) ∨
        (edge.first = vertex ∧ edge.second = predecessor)) ∧
      steps = priorSteps + 1 := by
  cases walk with
  | refl => exact False.elim (nonRoot rfl)
  | @step priorSteps predecessor finish prior adjacency =>
      rcases adjacency with ⟨edge, edgeMembership, direction⟩
      exact ⟨priorSteps, predecessor, edge, prior, edgeMembership,
        direction, rfl⟩

private theorem exists_rootedParentEdge (graph : Graph) {vertex : Vertex}
    (reachable : ∃ steps, graph.WalkN 0 steps vertex)
    (nonRoot : vertex ≠ 0) :
    ∃ edge, graph.IsRootedParentEdge vertex edge := by
  have shortest := graph.walkN_shortestWalkSteps vertex reachable
  rcases shortest.lastEdge nonRoot with
    ⟨steps, predecessor, edge, prior, edgeMembership, direction,
      distanceEquation⟩
  refine ⟨edge, predecessor, edgeMembership, direction, ?_⟩
  have predecessorLe := graph.shortestWalkSteps_le prior
  omega

private noncomputable def parentEdge (graph : Graph) (vertex : Vertex) :
    Edge := by
  classical
  exact if existsParent : ∃ edge, graph.IsRootedParentEdge vertex edge then
    Classical.choose existsParent
  else { first := 0, second := 0 }

private theorem parentEdge_spec (graph : Graph) {vertex : Vertex}
    (connected : graph.Connected) (inBounds : vertex < graph.vertexCount)
    (nonRoot : vertex ≠ 0) :
    graph.IsRootedParentEdge vertex (graph.parentEdge vertex) := by
  have reachable : ∃ steps, graph.WalkN 0 steps vertex := by
    rcases (connected.2 vertex inBounds).toSimple with
      ⟨steps, visited, simple⟩
    exact ⟨steps, simple.toWalkN⟩
  have existsParent := graph.exists_rootedParentEdge reachable nonRoot
  unfold parentEdge
  rw [dif_pos existsParent]
  exact Classical.choose_spec existsParent

private theorem parentEdge_injective (graph : Graph)
    (connected : graph.Connected) {first second : Vertex}
    (firstInBounds : first < graph.vertexCount) (firstNonRoot : first ≠ 0)
    (secondInBounds : second < graph.vertexCount)
    (secondNonRoot : second ≠ 0)
    (same : graph.parentEdge first = graph.parentEdge second) :
    first = second := by
  rcases graph.parentEdge_spec connected firstInBounds firstNonRoot with
    ⟨firstPredecessor, firstMembership, firstDirection, firstDecrease⟩
  rcases graph.parentEdge_spec connected secondInBounds secondNonRoot with
    ⟨secondPredecessor, secondMembership, secondDirection, secondDecrease⟩
  rw [← same] at secondDirection
  rcases firstDirection with ⟨firstFirst, firstSecond⟩ |
      ⟨firstFirst, firstSecond⟩ <;>
    rcases secondDirection with ⟨secondFirst, secondSecond⟩ |
      ⟨secondFirst, secondSecond⟩
  · exact firstSecond.symm.trans secondSecond
  · have predecessorIsSecond : firstPredecessor = second :=
      firstFirst.symm.trans secondFirst
    have firstIsPredecessor : first = secondPredecessor :=
      firstSecond.symm.trans secondSecond
    rw [predecessorIsSecond] at firstDecrease
    rw [← firstIsPredecessor] at secondDecrease
    omega
  · have firstIsPredecessor : first = secondPredecessor :=
      firstFirst.symm.trans secondFirst
    have predecessorIsSecond : firstPredecessor = second :=
      firstSecond.symm.trans secondSecond
    rw [predecessorIsSecond] at firstDecrease
    rw [← firstIsPredecessor] at secondDecrease
    omega
  · exact firstFirst.symm.trans secondFirst

private noncomputable def parentEdgeIndex (graph : Graph)
    (vertex : Vertex) : Nat :=
  graph.edges.idxOf (graph.parentEdge vertex)

private theorem parentEdgeIndex_lookup (graph : Graph)
    (connected : graph.Connected) {vertex : Vertex}
    (inBounds : vertex < graph.vertexCount) (nonRoot : vertex ≠ 0) :
    graph.edges[graph.parentEdgeIndex vertex]? =
      some (graph.parentEdge vertex) := by
  rcases graph.parentEdge_spec connected inBounds nonRoot with
    ⟨predecessor, membership, direction, decrease⟩
  simpa [parentEdgeIndex] using
    (list_map_getElem?_idxOf_eq_some graph.edges id membership)

/-- A finite connected graph contains at least one distinct stored edge for
every non-root vertex. The proof selects a shortest-walk parent edge and uses
strict distance decrease to show that two vertices cannot select the same
undirected edge. -/
theorem Connected.vertexCount_le_edges_add_one {graph : Graph}
    (connected : graph.Connected) :
    graph.vertexCount ≤ graph.edges.length + 1 := by
  let nonRootVertices :=
    (List.range (graph.vertexCount - 1)).map (fun offset => offset + 1)
  have vertexData : ∀ vertex ∈ nonRootVertices,
      vertex < graph.vertexCount ∧ vertex ≠ 0 := by
    intro vertex membership
    change vertex ∈ (List.range (graph.vertexCount - 1)).map
      (fun offset => offset + 1) at membership
    rcases List.mem_map.mp membership with ⟨offset, offsetMembership, rfl⟩
    have offsetBound := List.mem_range.mp offsetMembership
    constructor <;> omega
  have verticesNodup : nonRootVertices.Nodup := by
    apply nodup_map_of_injective_on List.nodup_range
    intro first firstMembership second secondMembership same
    omega
  let edgeKey : Edge → Nat × Nat := fun edge => (edge.first, edge.second)
  have parentEdgeKeysNodup :
      (nonRootVertices.map
        (fun vertex => edgeKey (graph.parentEdge vertex))).Nodup := by
    apply nodup_map_of_injective_on verticesNodup
    intro first firstMembership second secondMembership same
    rcases vertexData first firstMembership with
      ⟨firstInBounds, firstNonRoot⟩
    rcases vertexData second secondMembership with
      ⟨secondInBounds, secondNonRoot⟩
    have sameEdge : graph.parentEdge first = graph.parentEdge second := by
      cases firstEquation : graph.parentEdge first with
      | mk firstSource firstTarget =>
          cases secondEquation : graph.parentEdge second with
          | mk secondSource secondTarget =>
              simp [edgeKey, firstEquation, secondEquation] at same
              simp [same]
    exact graph.parentEdge_injective connected firstInBounds firstNonRoot
      secondInBounds secondNonRoot sameEdge
  have parentEdgeKeysSubset :
      ∀ key ∈ nonRootVertices.map
        (fun vertex => edgeKey (graph.parentEdge vertex)),
        key ∈ graph.edges.map edgeKey := by
    intro key membership
    rcases List.mem_map.mp membership with
      ⟨vertex, vertexMembership, rfl⟩
    rcases vertexData vertex vertexMembership with
      ⟨inBounds, nonRoot⟩
    rcases graph.parentEdge_spec connected inBounds nonRoot with
      ⟨predecessor, edgeMembership, direction, decrease⟩
    exact List.mem_map.mpr ⟨graph.parentEdge vertex, edgeMembership, rfl⟩
  have edgeBound := length_le_of_nodup_subset' parentEdgeKeysNodup
    parentEdgeKeysSubset
  change (((List.range (graph.vertexCount - 1)).map
    (fun offset => offset + 1)).map
      (fun vertex => edgeKey (graph.parentEdge vertex))).length ≤
      (graph.edges.map edgeKey).length at edgeBound
  simp only [List.length_map, List.length_range] at edgeBound
  omega

/-- In a finite tree, the shortest-path parent edges of the non-root vertices
occupy every stored multigraph edge index exactly once. This occurrence-level
statement remains valid in the presence of parallel equal-valued edges. -/
theorem IsTree.every_edge_index_is_parent {graph : Graph}
    (tree : graph.IsTree) {index : Nat}
    (indexInBounds : index < graph.edges.length) :
    ∃ vertex,
      vertex < graph.vertexCount ∧ vertex ≠ 0 ∧
        graph.parentEdgeIndex vertex = index := by
  classical
  let nonRootVertices :=
    (List.range (graph.vertexCount - 1)).map (fun offset => offset + 1)
  have vertexData : ∀ vertex ∈ nonRootVertices,
      vertex < graph.vertexCount ∧ vertex ≠ 0 := by
    intro vertex membership
    change vertex ∈ (List.range (graph.vertexCount - 1)).map
      (fun offset => offset + 1) at membership
    rcases List.mem_map.mp membership with ⟨offset, offsetMembership, rfl⟩
    have offsetBound := List.mem_range.mp offsetMembership
    constructor <;> omega
  have verticesNodup : nonRootVertices.Nodup := by
    apply nodup_map_of_injective_on List.nodup_range
    intro first firstMembership second secondMembership same
    omega
  let parentIndices :=
    nonRootVertices.map (fun vertex => graph.parentEdgeIndex vertex)
  have parentIndicesNodup : parentIndices.Nodup := by
    apply nodup_map_of_injective_on verticesNodup
    intro first firstMembership second secondMembership sameIndex
    rcases vertexData first firstMembership with
      ⟨firstInBounds, firstNonRoot⟩
    rcases vertexData second secondMembership with
      ⟨secondInBounds, secondNonRoot⟩
    have firstLookup := graph.parentEdgeIndex_lookup tree.2.1
      firstInBounds firstNonRoot
    have secondLookup := graph.parentEdgeIndex_lookup tree.2.1
      secondInBounds secondNonRoot
    have sameSome : some (graph.parentEdge first) =
        some (graph.parentEdge second) := by
      rw [← firstLookup, ← secondLookup, sameIndex]
    have sameEdge : graph.parentEdge first = graph.parentEdge second :=
      Option.some.inj sameSome
    exact graph.parentEdge_injective tree.2.1 firstInBounds firstNonRoot
      secondInBounds secondNonRoot sameEdge
  have parentIndicesSubset : ∀ candidate ∈ parentIndices,
      candidate ∈ List.range graph.edges.length := by
    intro candidate membership
    rcases List.mem_map.mp membership with
      ⟨vertex, vertexMembership, rfl⟩
    rcases vertexData vertex vertexMembership with ⟨inBounds, nonRoot⟩
    exact List.mem_range.mpr
      (List.getElem?_eq_some_iff.mp
        (graph.parentEdgeIndex_lookup tree.2.1 inBounds nonRoot)).1
  have parentIndicesLength : parentIndices.length = graph.edges.length := by
    dsimp [parentIndices, nonRootVertices]
    simp only [List.length_map]
    simp only [List.length_range]
    have positive := tree.2.1.1
    have edgeCount := tree.2.2
    omega
  have indexMembership : index ∈ parentIndices := by
    by_cases present : index ∈ parentIndices
    · exact present
    · have enlargedNodup : (index :: parentIndices).Nodup :=
        List.nodup_cons.mpr ⟨present, parentIndicesNodup⟩
      have enlargedSubset : ∀ candidate ∈ index :: parentIndices,
          candidate ∈ List.range graph.edges.length := by
        intro candidate membership
        simp only [List.mem_cons] at membership
        rcases membership with rfl | tailMembership
        · exact List.mem_range.mpr indexInBounds
        · exact parentIndicesSubset candidate tailMembership
      have impossible := length_le_of_nodup_subset' enlargedNodup enlargedSubset
      simp only [List.length_cons, List.length_range,
        parentIndicesLength] at impossible
      omega
  rcases List.mem_map.mp indexMembership with
    ⟨vertex, vertexMembership, same⟩
  rcases vertexData vertex vertexMembership with ⟨inBounds, nonRoot⟩
  exact ⟨vertex, inBounds, nonRoot, same⟩

/-- A graph satisfying the declarative tree contract has no edge-aware simple
multigraph cycle. The proof counts exact stored edge occurrences, maps each
cycle edge to its unique shortest-path child vertex, and contradicts a
minimum-distance cycle vertex. -/
theorem IsTree.no_edgeSimpleCycle {graph : Graph} (tree : graph.IsTree)
    (cycle : graph.EdgeSimpleCycle) : False := by
  classical
  let parentVertex : graph.DirectedEdge → Vertex := fun directed =>
    Classical.choose (tree.every_edge_index_is_parent
      (List.getElem?_eq_some_iff.mp directed.lookup).1)
  have parentVertex_spec : ∀ directed : graph.DirectedEdge,
      parentVertex directed < graph.vertexCount ∧
        parentVertex directed ≠ 0 ∧
          graph.parentEdgeIndex (parentVertex directed) = directed.index := by
    intro directed
    dsimp [parentVertex]
    exact Classical.choose_spec (tree.every_edge_index_is_parent
      (List.getElem?_eq_some_iff.mp directed.lookup).1)
  let parentVertices := cycle.traversed.map parentVertex
  have parentVerticesNodup : parentVertices.Nodup := by
    have general : ∀ steps : List graph.DirectedEdge,
        (steps.map Graph.DirectedEdge.index).Nodup →
          (steps.map parentVertex).Nodup := by
      intro steps indexNodup
      induction steps with
      | nil => simp
      | cons head tail ih =>
          simp only [List.map_cons, List.nodup_cons] at indexNodup ⊢
          refine ⟨?_, ih indexNodup.2⟩
          intro parentMembership
          rcases List.mem_map.mp parentMembership with
            ⟨other, otherMembership, sameParent⟩
          have headSpec := parentVertex_spec head
          have otherSpec := parentVertex_spec other
          have sameIndex : head.index = other.index := by
            rw [← headSpec.2.2, ← otherSpec.2.2, sameParent]
          exact indexNodup.1
            (List.mem_map.mpr ⟨other, otherMembership, sameIndex.symm⟩)
    exact general cycle.traversed cycle.edgeIndicesNodup
  have parentVerticesSubset : ∀ vertex ∈ parentVertices,
      vertex ∈ cycle.vertices := by
    intro vertex membership
    rcases List.mem_map.mp membership with
      ⟨directed, directedMembership, rfl⟩
    have vertexSpec := parentVertex_spec directed
    have parentLookup := graph.parentEdgeIndex_lookup tree.2.1
      vertexSpec.1 vertexSpec.2.1
    rw [vertexSpec.2.2] at parentLookup
    have sameEdge : directed.edge =
        graph.parentEdge (parentVertex directed) :=
      Option.some.inj (directed.lookup.symm.trans parentLookup)
    rcases graph.parentEdge_spec tree.2.1 vertexSpec.1 vertexSpec.2.1 with
      ⟨predecessor, edgeMembership, direction, decrease⟩
    rw [← sameEdge] at direction
    have endpoints := cycle.edge_endpoints_mem_vertices directedMembership
    rcases direction with forward | backward
    · rw [← forward.2]
      exact endpoints.2
    · rw [← backward.1]
      exact endpoints.1
  have parentVerticesLength :
      parentVertices.length = cycle.vertices.length := by
    simp [parentVertices]
  have verticesSubsetParent : ∀ vertex ∈ cycle.vertices,
      vertex ∈ parentVertices := by
    intro vertex membership
    by_cases present : vertex ∈ parentVertices
    · exact present
    · have enlargedNodup : (vertex :: parentVertices).Nodup :=
        List.nodup_cons.mpr ⟨present, parentVerticesNodup⟩
      have enlargedSubset : ∀ candidate ∈ vertex :: parentVertices,
          candidate ∈ cycle.vertices := by
        intro candidate candidateMembership
        simp only [List.mem_cons] at candidateMembership
        rcases candidateMembership with rfl | tailMembership
        · exact membership
        · exact parentVerticesSubset candidate tailMembership
      have impossible := length_le_of_nodup_subset' enlargedNodup enlargedSubset
      rw [List.length_cons, parentVerticesLength] at impossible
      omega
  rcases exists_minimal_measure cycle.start
      (cycle.traversed.dropLast.map Graph.DirectedEdge.target)
      graph.shortestWalkSteps with
    ⟨minimal, minimalMembership, minimalBound⟩
  have minimalInCycle : minimal ∈ cycle.vertices := by
    simpa [Graph.EdgeSimpleCycle.vertices] using minimalMembership
  have minimalIsParent := verticesSubsetParent minimal minimalInCycle
  rcases List.mem_map.mp minimalIsParent with
    ⟨directed, directedMembership, parentEquation⟩
  have minimalSpec := parentVertex_spec directed
  rw [parentEquation] at minimalSpec
  have parentLookup := graph.parentEdgeIndex_lookup tree.2.1
    minimalSpec.1 minimalSpec.2.1
  rw [minimalSpec.2.2] at parentLookup
  have sameEdge : directed.edge = graph.parentEdge minimal :=
    Option.some.inj (directed.lookup.symm.trans parentLookup)
  rcases graph.parentEdge_spec tree.2.1 minimalSpec.1 minimalSpec.2.1 with
    ⟨predecessor, edgeMembership, direction, decrease⟩
  rw [← sameEdge] at direction
  have endpoints := cycle.edge_endpoints_mem_vertices directedMembership
  have predecessorInCycle : predecessor ∈ cycle.vertices := by
    rcases direction with forward | backward
    · rw [← forward.1]
      exact endpoints.1
    · rw [← backward.2]
      exact endpoints.2
  have minimalLePredecessor := minimalBound predecessor (by
    simpa [Graph.EdgeSimpleCycle.vertices] using predecessorInCycle)
  omega

/-- A simple cycle survives any occurrence mask that keeps all of its exact
stored edge indices. Compacted edge indices remain duplicate-free because the
retained-index map is strictly monotone at kept positions. -/
theorem EdgeSimpleCycle.retainEdges {graph : Graph} {mask : List Bool}
    (cycle : graph.EdgeSimpleCycle)
    (aligned : graph.edges.length = mask.length)
    (allKept : ∀ directed ∈ cycle.traversed,
      mask[directed.index]? = some true) :
    Nonempty (graph.retainEdges mask).EdgeSimpleCycle := by
  classical
  rcases cycle.walk.retainEdges aligned allKept with
    ⟨retainedTraversal, retainedWalk, indexEquation, targetEquation⟩
  have compactIndicesNodup :
      (cycle.traversed.map
        (fun directed => Graph.retainedIndex mask directed.index)).Nodup := by
    have mappedNodup :
        ((cycle.traversed.map Graph.DirectedEdge.index).map
          (Graph.retainedIndex mask)).Nodup := by
      apply nodup_map_of_injective_on cycle.edgeIndicesNodup
      intro first firstMembership second secondMembership same
      rcases List.mem_map.mp firstMembership with
        ⟨firstDirected, firstDirectedMembership, rfl⟩
      rcases List.mem_map.mp secondMembership with
        ⟨secondDirected, secondDirectedMembership, rfl⟩
      exact Graph.retainedIndex_injective_of_kept
        (allKept firstDirected firstDirectedMembership)
        (allKept secondDirected secondDirectedMembership) same
    simpa [List.map_map, Function.comp_def] using mappedNodup
  have retainedLength : retainedTraversal.length = cycle.traversed.length := by
    simpa using congrArg List.length indexEquation
  have retainedNonempty : retainedTraversal ≠ [] := by
    intro empty
    rw [empty] at retainedLength
    simp at retainedLength
    exact cycle.nonempty (List.eq_nil_of_length_eq_zero retainedLength.symm)
  have interiorTargets :
      retainedTraversal.dropLast.map Graph.DirectedEdge.target =
        cycle.traversed.dropLast.map Graph.DirectedEdge.target := by
    simpa only [List.map_dropLast] using congrArg List.dropLast targetEquation
  refine ⟨
    { start := cycle.start
      traversed := retainedTraversal
      nonempty := retainedNonempty
      walk := retainedWalk
      edgeIndicesNodup := ?_
      interiorNodup := ?_ }⟩
  · rw [indexEquation]
    exact compactIndicesNodup
  · rw [interiorTargets]
    exact cycle.interiorNodup

theorem Adjacent.symm {graph : Graph} {left right : Vertex}
    (adjacency : graph.Adjacent left right) : graph.Adjacent right left := by
  rcases adjacency with ⟨edge, membership, direction⟩
  refine ⟨edge, membership, ?_⟩
  rcases direction with forward | backward
  · exact .inr forward
  · exact .inl backward

/-- Induced local numbering of all edges whose two endpoints belong to the
listed occurrence component. -/
def restrictTo (graph : Graph) (vertices : List Vertex) : Graph where
  vertexCount := vertices.length
  edges := graph.edges.filterMap (Edge.restrictTo? vertices)

theorem restrictTo_edges_length (graph : Graph) (vertices : List Vertex) :
    (graph.restrictTo vertices).edges.length =
      (graph.edges.filter fun edge =>
        vertices.contains edge.first && vertices.contains edge.second).length := by
  change (graph.edges.filterMap (Edge.restrictTo? vertices)).length = _
  induction graph.edges with
  | nil => rfl
  | cons head tail ih =>
      by_cases firstContained : head.first ∈ vertices
      · by_cases secondContained : head.second ∈ vertices
        · have accepted := head.restrictTo?_eq_some_of_mem vertices
            firstContained secondContained
          simp [accepted, firstContained, secondContained, ih]
        · have rejected : head.restrictTo? vertices = none := by
            simp [Edge.restrictTo?,
              List.idxOf?_eq_none_iff.mpr secondContained]
          simp [rejected, firstContained, secondContained, ih]
      · have rejected : head.restrictTo? vertices = none := by
          simp [Edge.restrictTo?, List.idxOf?_eq_none_iff.mpr firstContained]
        simp [rejected, firstContained, ih]

theorem Bounded.restrictTo {graph : Graph} (bounded : graph.Bounded)
    (vertices : List Vertex) :
    (graph.restrictTo vertices).Bounded := by
  intro restrictedEdge restrictedMembership
  change restrictedEdge ∈ graph.edges.filterMap
    (Edge.restrictTo? vertices) at restrictedMembership
  rcases List.mem_filterMap.mp restrictedMembership with
    ⟨edge, edgeMembership, edgeEquation⟩
  rcases Edge.restrictTo?_eq_some edgeEquation with
    ⟨firstMembership, secondMembership, rfl⟩
  have originalDistinct := (bounded edge edgeMembership).2.2
  refine ⟨List.idxOf_lt_length_of_mem firstMembership,
    List.idxOf_lt_length_of_mem secondMembership, ?_⟩
  intro same
  exact originalDistinct
    (idxOf_injective_of_mem firstMembership secondMembership same)

theorem adjacent_restrictTo_iff (graph : Graph) (vertices : List Vertex)
    {left right : Vertex}
    (leftMembership : left ∈ vertices)
    (rightMembership : right ∈ vertices) :
    (graph.restrictTo vertices).Adjacent
        (vertices.idxOf left) (vertices.idxOf right) ↔
      graph.Adjacent left right := by
  constructor
  · rintro ⟨restrictedEdge, restrictedMembership, direction⟩
    change restrictedEdge ∈ graph.edges.filterMap
      (Edge.restrictTo? vertices) at restrictedMembership
    rcases List.mem_filterMap.mp restrictedMembership with
      ⟨edge, edgeMembership, edgeEquation⟩
    rcases Edge.restrictTo?_eq_some edgeEquation with
      ⟨firstMembership, secondMembership, rfl⟩
    refine ⟨edge, edgeMembership, ?_⟩
    rcases direction with forward | backward
    · exact .inl ⟨
        idxOf_injective_of_mem firstMembership leftMembership forward.1,
        idxOf_injective_of_mem secondMembership rightMembership forward.2⟩
    · exact .inr ⟨
        idxOf_injective_of_mem firstMembership rightMembership backward.1,
        idxOf_injective_of_mem secondMembership leftMembership backward.2⟩
  · rintro ⟨edge, edgeMembership, direction⟩
    rcases direction with forward | backward
    · have firstMembership : edge.first ∈ vertices := forward.1 ▸ leftMembership
      have secondMembership : edge.second ∈ vertices := forward.2 ▸ rightMembership
      let restrictedEdge : Edge := {
        first := vertices.idxOf edge.first
        second := vertices.idxOf edge.second }
      refine ⟨restrictedEdge, ?_, .inl ⟨?_, ?_⟩⟩
      · change restrictedEdge ∈ graph.edges.filterMap
          (Edge.restrictTo? vertices)
        exact List.mem_filterMap.mpr ⟨edge, edgeMembership,
          edge.restrictTo?_eq_some_of_mem vertices firstMembership
            secondMembership⟩
      · exact congrArg vertices.idxOf forward.1
      · exact congrArg vertices.idxOf forward.2
    · have firstMembership : edge.first ∈ vertices := backward.1 ▸ rightMembership
      have secondMembership : edge.second ∈ vertices := backward.2 ▸ leftMembership
      let restrictedEdge : Edge := {
        first := vertices.idxOf edge.first
        second := vertices.idxOf edge.second }
      refine ⟨restrictedEdge, ?_, .inr ⟨?_, ?_⟩⟩
      · change restrictedEdge ∈ graph.edges.filterMap
          (Edge.restrictTo? vertices)
        exact List.mem_filterMap.mpr ⟨edge, edgeMembership,
          edge.restrictTo?_eq_some_of_mem vertices firstMembership
            secondMembership⟩
      · exact congrArg vertices.idxOf backward.1
      · exact congrArg vertices.idxOf backward.2

/-- Delete a graph vertex, drop all incident edges, and compact larger vertex
names. -/
def deleteVertex (graph : Graph) (removed : Vertex) : Graph where
  vertexCount := graph.vertexCount - 1
  edges := graph.edges.filterMap (Edge.deleteVertex? removed)

@[simp] theorem deleteVertex_vertexCount (graph : Graph) (removed : Vertex) :
    (graph.deleteVertex removed).vertexCount = graph.vertexCount - 1 := rfl

def incidentCount (graph : Graph) (vertex : Vertex) : Nat :=
  (graph.edges.filter (·.incident vertex)).length

def Leaf (graph : Graph) (vertex : Vertex) : Prop :=
  vertex < graph.vertexCount ∧ graph.incidentCount vertex = 1

theorem Leaf.incidentEdge_eq {graph : Graph} {vertex : Vertex}
    (leaf : graph.Leaf vertex) {first second : Edge}
    (firstMembership : first ∈ graph.edges)
    (secondMembership : second ∈ graph.edges)
    (firstIncident : first.incident vertex = true)
    (secondIncident : second.incident vertex = true) :
    first = second := by
  have firstFiltered : first ∈ graph.edges.filter (·.incident vertex) := by
    simp [firstMembership, firstIncident]
  have secondFiltered : second ∈ graph.edges.filter (·.incident vertex) := by
    simp [secondMembership, secondIncident]
  rcases List.length_eq_one_iff.mp leaf.2 with ⟨only, filterEquation⟩
  rw [filterEquation] at firstFiltered secondFiltered
  simp at firstFiltered secondFiltered
  exact firstFiltered.trans secondFiltered.symm

theorem Leaf.adjacent_through_eq {graph : Graph} {vertex first second : Vertex}
    (leaf : graph.Leaf vertex)
    (enter : graph.Adjacent first vertex)
    (leave : graph.Adjacent vertex second) :
    first = second := by
  rcases enter with ⟨enterEdge, enterMembership, enterDirection⟩
  rcases leave with ⟨leaveEdge, leaveMembership, leaveDirection⟩
  have enterIncident : enterEdge.incident vertex = true := by
    rcases enterDirection with forward | backward
    · simp [Edge.incident, forward]
    · simp [Edge.incident, backward]
  have leaveIncident : leaveEdge.incident vertex = true := by
    rcases leaveDirection with forward | backward
    · simp [Edge.incident, forward]
    · simp [Edge.incident, backward]
  have sameEdge := leaf.incidentEdge_eq enterMembership leaveMembership
    enterIncident leaveIncident
  subst leaveEdge
  rcases enterDirection with enterForward | enterBackward <;>
  rcases leaveDirection with leaveForward | leaveBackward <;>
    simp_all

theorem Leaf.two_le_vertexCount {graph : Graph} {vertex : Vertex}
    (leaf : graph.Leaf vertex) (bounded : graph.Bounded) :
    2 ≤ graph.vertexCount := by
  rcases List.length_eq_one_iff.mp leaf.2 with ⟨edge, filterEquation⟩
  have filteredMembership : edge ∈ graph.edges.filter (·.incident vertex) := by
    rw [filterEquation]
    simp
  simp only [List.mem_filter] at filteredMembership
  rcases bounded edge filteredMembership.1 with
    ⟨firstInBounds, secondInBounds, distinct⟩
  cases countEquation : graph.vertexCount with
  | zero => simp [countEquation] at firstInBounds
  | succ remaining =>
      cases remaining with
      | zero =>
          have firstZero : edge.first = 0 := by
            simpa [countEquation] using firstInBounds
          have secondZero : edge.second = 0 := by
            simpa [countEquation] using secondInBounds
          exact False.elim (distinct (firstZero.trans secondZero.symm))
      | succ extra => simp

theorem SimpleWalk.finish_mem {graph : Graph} {start finish : Vertex}
    {steps : Nat} {visited : List Vertex}
    (walk : graph.SimpleWalk start steps visited finish) :
    finish ∈ visited := by
  induction walk with
  | refl => simp
  | step prior adjacency fresh ih => simp

theorem SimpleWalk.restrictTo {graph : Graph} {vertices : List Vertex}
    {start finish : Vertex} {steps : Nat} {visited : List Vertex}
    (walk : graph.SimpleWalk start steps visited finish)
    (contained : ∀ vertex ∈ visited, vertex ∈ vertices) :
    (graph.restrictTo vertices).Walk
      (vertices.idxOf start) (vertices.idxOf finish) := by
  induction walk with
  | refl => exact .refl _
  | @step priorSteps priorVisited middle current prior adjacency fresh ih =>
      have priorContained : ∀ vertex ∈ priorVisited, vertex ∈ vertices := by
        intro vertex membership
        exact contained vertex (by simp [membership])
      have middleMembership : middle ∈ vertices :=
        priorContained middle prior.finish_mem
      have currentMembership : current ∈ vertices :=
        contained current (by simp)
      exact .step (ih priorContained)
        ((graph.adjacent_restrictTo_iff vertices middleMembership
          currentMembership).mpr adjacency)

theorem SimpleWalk.avoidsLeaf {graph : Graph} {start finish removed : Vertex}
    {steps : Nat} {visited : List Vertex}
    (walk : graph.SimpleWalk start steps visited finish)
    (leaf : graph.Leaf removed)
    (startNotRemoved : start ≠ removed)
    (finishNotRemoved : finish ≠ removed) :
    removed ∉ visited := by
  induction walk with
  | refl => simpa [eq_comm] using startNotRemoved
  | @step priorSteps priorVisited middle current prior adjacency fresh ih =>
      have middleNotRemoved : middle ≠ removed := by
        intro middleIsRemoved
        subst middle
        cases prior with
        | refl => exact startNotRemoved rfl
        | @step earlierSteps earlierVisited previous _ earlier enter
            removedFresh =>
            have sameEndpoint := leaf.adjacent_through_eq enter adjacency
            subst current
            exact fresh (by
              simp only [List.mem_append, List.mem_singleton]
              exact .inl earlier.finish_mem)
      have priorAvoids := ih middleNotRemoved
      intro membership
      simp only [List.mem_append, List.mem_singleton] at membership
      rcases membership with priorMembership | finalEqual
      · exact priorAvoids priorMembership
      · exact finishNotRemoved finalEqual.symm

theorem deleteVertex_edges_length_add_incidentCount
    (graph : Graph) (removed : Vertex) :
    (graph.deleteVertex removed).edges.length + graph.incidentCount removed =
      graph.edges.length := by
  cases graph with
  | mk vertexCount edges =>
      simp only [deleteVertex, incidentCount]
      induction edges with
      | nil => rfl
      | cons edge rest ih =>
          rcases edge with ⟨first, second⟩
          by_cases firstDeleted : first = removed <;>
          by_cases secondDeleted : second = removed <;>
            simp [Edge.deleteVertex?,
              Certificate.deleteVertex?, firstDeleted, secondDeleted,
              ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem IsTree.deleteVertex_edgeCount {graph : Graph} (tree : graph.IsTree)
    {removed : Vertex} (leaf : graph.Leaf removed) :
    (graph.deleteVertex removed).edges.length + 1 =
      (graph.deleteVertex removed).vertexCount := by
  have accounting := graph.deleteVertex_edges_length_add_incidentCount removed
  rw [leaf.2] at accounting
  have originalCount := tree.2.2
  simp only [deleteVertex_vertexCount]
  omega

/-- Adjacency in the compacted graph is exactly adjacency between the embedded
old vertex names. -/
theorem adjacent_deleteVertex_iff (graph : Graph) (removed : Vertex)
    (left right : Vertex) :
    (graph.deleteVertex removed).Adjacent left right ↔
      graph.Adjacent (Certificate.expandVertex removed left)
        (Certificate.expandVertex removed right) := by
  constructor
  · rintro ⟨compacted, compactedMembership, direction⟩
    change compacted ∈ graph.edges.filterMap (Edge.deleteVertex? removed) at compactedMembership
    simp only [List.mem_filterMap] at compactedMembership
    rcases compactedMembership with
      ⟨edge, edgeMembership, compactedEquation⟩
    rcases Edge.deleteVertex?_eq_some compactedEquation with
      ⟨firstNotRemoved, secondNotRemoved, rfl⟩
    refine ⟨edge, edgeMembership, ?_⟩
    rcases direction with forward | backward
    · left
      constructor
      · have expanded := congrArg (Certificate.expandVertex removed) forward.1
        simpa [Certificate.expandVertex_compactVertex_of_ne firstNotRemoved]
          using expanded
      · have expanded := congrArg (Certificate.expandVertex removed) forward.2
        simpa [Certificate.expandVertex_compactVertex_of_ne secondNotRemoved]
          using expanded
    · right
      constructor
      · have expanded := congrArg (Certificate.expandVertex removed) backward.1
        simpa [Certificate.expandVertex_compactVertex_of_ne firstNotRemoved]
          using expanded
      · have expanded := congrArg (Certificate.expandVertex removed) backward.2
        simpa [Certificate.expandVertex_compactVertex_of_ne secondNotRemoved]
          using expanded
  · rintro ⟨edge, edgeMembership, direction⟩
    have firstNotRemoved : edge.first ≠ removed := by
      intro same
      rcases direction with forward | backward
      · exact Certificate.expandVertex_ne removed left (forward.1 ▸ same)
      · exact Certificate.expandVertex_ne removed right (backward.1 ▸ same)
    have secondNotRemoved : edge.second ≠ removed := by
      intro same
      rcases direction with forward | backward
      · exact Certificate.expandVertex_ne removed right (forward.2 ▸ same)
      · exact Certificate.expandVertex_ne removed left (backward.2 ▸ same)
    let compacted : Edge := {
      first := Certificate.compactVertex removed edge.first
      second := Certificate.compactVertex removed edge.second }
    refine ⟨compacted, ?_, ?_⟩
    · change compacted ∈ graph.edges.filterMap (Edge.deleteVertex? removed)
      simp only [List.mem_filterMap]
      exact ⟨edge, edgeMembership,
        edge.deleteVertex?_eq_some_of_ne removed firstNotRemoved
          secondNotRemoved⟩
    · rcases direction with forward | backward
      · left
        constructor
        · change Certificate.compactVertex removed edge.first = left
          simp [forward.1]
        · change Certificate.compactVertex removed edge.second = right
          simp [forward.2]
      · right
        constructor
        · change Certificate.compactVertex removed edge.first = right
          simp [backward.1]
        · change Certificate.compactVertex removed edge.second = left
          simp [backward.2]

theorem SimpleWalk.deleteVertex {graph : Graph}
    {start finish removed : Vertex} {steps : Nat} {visited : List Vertex}
    (walk : graph.SimpleWalk start steps visited finish)
    (avoids : removed ∉ visited) :
    (graph.deleteVertex removed).Walk
      (Certificate.compactVertex removed start)
      (Certificate.compactVertex removed finish) := by
  induction walk with
  | refl => exact .refl _
  | @step priorSteps priorVisited middle current prior adjacency fresh ih =>
      have priorAvoids : removed ∉ priorVisited := by
        intro membership
        exact avoids (by simp [membership])
      have currentNotRemoved : current ≠ removed := by
        intro same
        subst current
        exact avoids (by simp)
      have middleNotRemoved : middle ≠ removed := by
        intro same
        subst middle
        exact priorAvoids prior.finish_mem
      have compactedAdjacency :
          (graph.deleteVertex removed).Adjacent
            (Certificate.compactVertex removed middle)
            (Certificate.compactVertex removed current) := by
        apply (graph.adjacent_deleteVertex_iff removed _ _).mpr
        simpa [Certificate.expandVertex_compactVertex_of_ne middleNotRemoved,
          Certificate.expandVertex_compactVertex_of_ne currentNotRemoved]
          using adjacency
      exact .step (ih priorAvoids) compactedAdjacency

theorem Walk.expandDelete {graph : Graph} {removed start finish : Vertex}
    (walk : (graph.deleteVertex removed).Walk start finish) :
    graph.Walk (Certificate.expandVertex removed start)
      (Certificate.expandVertex removed finish) := by
  induction walk with
  | refl => exact .refl _
  | step prior adjacency ih =>
      exact .step ih
        ((graph.adjacent_deleteVertex_iff removed _ _).mp adjacency)

theorem Connected.deleteLeaf {graph : Graph} (connected : graph.Connected)
    (bounded : graph.Bounded) {removed : Vertex} (leaf : graph.Leaf removed) :
    (graph.deleteVertex removed).Connected := by
  have remainingPositive : 0 < graph.vertexCount - 1 := by
    have atLeastTwo := leaf.two_le_vertexCount bounded
    omega
  refine ⟨by simpa using remainingPositive, ?_⟩
  intro vertex vertexInBounds
  have oldStartInBounds :
      Certificate.expandVertex removed 0 < graph.vertexCount :=
    Certificate.expandVertex_lt leaf.1 remainingPositive
  have oldFinishInBounds :
      Certificate.expandVertex removed vertex < graph.vertexCount :=
    Certificate.expandVertex_lt leaf.1 (by simpa using vertexInBounds)
  have between : graph.Walk
      (Certificate.expandVertex removed 0)
      (Certificate.expandVertex removed vertex) :=
    (connected.2 _ oldStartInBounds).reverse.trans
      (connected.2 _ oldFinishInBounds)
  rcases between.toSimple with ⟨steps, visited, simple⟩
  have avoids := simple.avoidsLeaf leaf
    (Certificate.expandVertex_ne removed 0)
    (Certificate.expandVertex_ne removed vertex)
  simpa using simple.deleteVertex avoids

theorem Bounded.deleteVertex {graph : Graph} (bounded : graph.Bounded)
    {removed : Vertex} (removedInBounds : removed < graph.vertexCount) :
    (graph.deleteVertex removed).Bounded := by
  intro compacted compactedMembership
  change compacted ∈ graph.edges.filterMap (Edge.deleteVertex? removed) at compactedMembership
  simp only [List.mem_filterMap] at compactedMembership
  rcases compactedMembership with
    ⟨edge, edgeMembership, compactedEquation⟩
  rcases Edge.deleteVertex?_eq_some compactedEquation with
    ⟨firstNotRemoved, secondNotRemoved, rfl⟩
  rcases bounded edge edgeMembership with
    ⟨firstInBounds, secondInBounds, endpointsDistinct⟩
  refine ⟨Certificate.compactVertex_lt removedInBounds firstInBounds
      firstNotRemoved,
    Certificate.compactVertex_lt removedInBounds secondInBounds
      secondNotRemoved, ?_⟩
  intro compactedEqual
  have expandedEqual := congrArg (Certificate.expandVertex removed)
    compactedEqual
  rw [Certificate.expandVertex_compactVertex_of_ne firstNotRemoved,
    Certificate.expandVertex_compactVertex_of_ne secondNotRemoved] at expandedEqual
  exact endpointsDistinct expandedEqual

theorem IsTree.deleteLeaf {graph : Graph} (tree : graph.IsTree)
    {removed : Vertex} (leaf : graph.Leaf removed) :
    (graph.deleteVertex removed).IsTree :=
  ⟨tree.1.deleteVertex leaf.1,
    tree.2.1.deleteLeaf tree.1 leaf,
    tree.deleteVertex_edgeCount leaf⟩

/-- On a bounded finite graph, `vertexCount` closure rounds decide the
unbounded walk relation between any two in-bounds vertices. -/
theorem mem_closureN_vertexCount_iff_walk (graph : Graph)
    (bounded : graph.Bounded) {start finish : Vertex}
    (startInBounds : start < graph.vertexCount)
    (finishInBounds : finish < graph.vertexCount) :
    finish ∈ graph.closureN graph.vertexCount [start] ↔
      graph.Walk start finish := by
  rw [graph.mem_closureN_iff_walkWithin bounded start finish
    graph.vertexCount finishInBounds]
  constructor
  · rintro ⟨steps, _, walk⟩
    exact walk.toWalk
  · intro walk
    rcases walk.toSimple with ⟨steps, visited, simple⟩
    exact simple.toWalkWithin bounded startInBounds

end Graph

/-- A local color for one directed incidence of the unswitched occurrence
graph. Ordinary incidences retain the exact stored multiedge and endpoint;
the two premise incidences aimed at one par conclusion deliberately share the
same color. -/
inductive LocalSwitchingColor where
  | unique (edgeIndex : Nat) (forward : Bool)
  | par (conclusion : Vertex)
  deriving Repr, DecidableEq, BEq

namespace Certificate

/-- The unswitched occurrence graph contains both premise edges of every
logical link. It is used only to discover candidate tensor components; the
authoritative correctness definition continues to quantify over switchings. -/
def fullEdges (certificate : Certificate) : List Edge :=
  certificate.links.flatMap fun
    | .axiom left right => [{ first := left, second := right }]
    | .tensor left right conclusion =>
        [{ first := left, second := conclusion },
         { first := right, second := conclusion }]
    | .par left right conclusion =>
        [{ first := left, second := conclusion },
         { first := right, second := conclusion }]

/-- Par choices computed directly from a link list. This is definitionally the
same projection used by `Certificate.parChoices`, but makes structural
induction over links explicit. -/
def linkParChoices (links : List Link) : List (Edge × Edge) :=
  links.filterMap fun
    | .par left right conclusion =>
        some ({ first := left, second := conclusion },
          { first := right, second := conclusion })
    | _ => none

/-- Fixed switching edges computed directly from a link list. -/
def linkFixedEdges (links : List Link) : List Edge :=
  links.flatMap fun
    | .axiom left right => [{ first := left, second := right }]
    | .tensor left right conclusion =>
        [{ first := left, second := conclusion },
         { first := right, second := conclusion }]
    | .par _ _ _ => []

/-- All occurrence edges computed directly from a link list. -/
def linkFullEdges (links : List Link) : List Edge :=
  links.flatMap fun
    | .axiom left right => [{ first := left, second := right }]
    | .tensor left right conclusion =>
        [{ first := left, second := conclusion },
         { first := right, second := conclusion }]
    | .par left right conclusion =>
        [{ first := left, second := conclusion },
         { first := right, second := conclusion }]

@[simp] theorem linkFullEdges_nil : linkFullEdges [] = [] := rfl

/-- Par-target annotations computed from an arbitrary link suffix. Keeping the
suffix-level projection explicit lets occurrence offsets be tracked during
structural switching constructions. -/
def linkFullEdgeParTargets (links : List Link) : List (Option Vertex) :=
  links.flatMap fun
    | .axiom _ _ => [none]
    | .tensor _ _ _ => [none, none]
    | .par _ _ conclusion => [some conclusion, some conclusion]

@[simp] theorem linkFullEdgeParTargets_nil :
    linkFullEdgeParTargets [] = [] := rfl

@[simp] theorem linkFullEdgeParTargets_axiom_cons
    (links : List Link) (left right : Vertex) :
    linkFullEdgeParTargets (.axiom left right :: links) =
      none :: linkFullEdgeParTargets links := rfl

@[simp] theorem linkFullEdgeParTargets_tensor_cons
    (links : List Link) (left right conclusion : Vertex) :
    linkFullEdgeParTargets (.tensor left right conclusion :: links) =
      none :: none :: linkFullEdgeParTargets links := rfl

@[simp] theorem linkFullEdgeParTargets_par_cons
    (links : List Link) (left right conclusion : Vertex) :
    linkFullEdgeParTargets (.par left right conclusion :: links) =
      some conclusion :: some conclusion :: linkFullEdgeParTargets links := rfl

@[simp] theorem linkFullEdges_axiom_cons
    (links : List Link) (left right : Vertex) :
    linkFullEdges (.axiom left right :: links) =
      { first := left, second := right } :: linkFullEdges links := rfl

@[simp] theorem linkFullEdges_tensor_cons
    (links : List Link) (left right conclusion : Vertex) :
    linkFullEdges (.tensor left right conclusion :: links) =
      { first := left, second := conclusion } ::
        { first := right, second := conclusion } :: linkFullEdges links := rfl

@[simp] theorem linkFullEdges_par_cons
    (links : List Link) (left right conclusion : Vertex) :
    linkFullEdges (.par left right conclusion :: links) =
      { first := left, second := conclusion } ::
      { first := right, second := conclusion } :: linkFullEdges links := rfl

@[simp] theorem linkFullEdges_append (first second : List Link) :
    linkFullEdges (first ++ second) =
      linkFullEdges first ++ linkFullEdges second := by
  unfold linkFullEdges
  exact List.flatMap_append

@[simp] theorem linkFullEdgeParTargets_append (first second : List Link) :
    linkFullEdgeParTargets (first ++ second) =
      linkFullEdgeParTargets first ++ linkFullEdgeParTargets second := by
  unfold linkFullEdgeParTargets
  exact List.flatMap_append

@[simp] theorem linkFullEdgeParTargets_length (links : List Link) :
    (linkFullEdgeParTargets links).length = (linkFullEdges links).length := by
  induction links with
  | nil => rfl
  | cons link rest ih =>
      cases link <;> simp [ih]

@[simp] theorem linkParChoices_certificate (certificate : Certificate) :
    linkParChoices certificate.links = certificate.parChoices := rfl

@[simp] theorem linkFixedEdges_certificate (certificate : Certificate) :
    linkFixedEdges certificate.links = certificate.fixedEdges := rfl

@[simp] theorem linkFullEdges_certificate (certificate : Certificate) :
    linkFullEdges certificate.links = certificate.fullEdges := rfl

/-- Keep exactly those edge occurrences whose parallel Boolean mask entry is
true. Mismatched tails are rejected by truncation; `FullSwitchingSelection`
proves exact length alignment for all masks it constructs. -/
def retainByMask : List Edge → List Bool → List Edge
  := Graph.retainEdgesByMask

/-- An occurrence-order realization of a switching. It walks the stored link
list once, retains every axiom/tensor edge, and retains exactly one indexed
position from each par pair while separately recording the ordinary selected
par-edge list. -/
inductive FullSwitchingSelection :
    List Link → List Edge → List Edge → List Bool → Prop where
  | nil : FullSwitchingSelection [] [] [] []
  | axiom {links selected retained mask left right}
      (prior : FullSwitchingSelection links selected retained mask) :
      FullSwitchingSelection (.axiom left right :: links) selected
        ({ first := left, second := right } :: retained) (true :: mask)
  | tensor {links selected retained mask left right conclusion}
      (prior : FullSwitchingSelection links selected retained mask) :
      FullSwitchingSelection (.tensor left right conclusion :: links) selected
        ({ first := left, second := conclusion } ::
          { first := right, second := conclusion } :: retained)
        (true :: true :: mask)
  | parLeft {links selected retained mask left right conclusion}
      (prior : FullSwitchingSelection links selected retained mask) :
      FullSwitchingSelection (.par left right conclusion :: links)
        ({ first := left, second := conclusion } :: selected)
        ({ first := left, second := conclusion } :: retained)
        (true :: false :: mask)
  | parRight {links selected retained mask left right conclusion}
      (prior : FullSwitchingSelection links selected retained mask) :
      FullSwitchingSelection (.par left right conclusion :: links)
        ({ first := right, second := conclusion } :: selected)
        ({ first := right, second := conclusion } :: retained)
        (false :: true :: mask)

/-- Relative occurrence indices used by a switching request are sparse at
every par pair: the two positions emitted by one par link are never both
requested. The running offset refers to the original full-edge list. -/
def ParPairSparse : List Link → Nat → (Nat → Prop) → Prop
  | [], _, _ => True
  | .axiom _ _ :: links, offset, uses =>
      ParPairSparse links (offset + 1) uses
  | .tensor _ _ _ :: links, offset, uses =>
      ParPairSparse links (offset + 2) uses
  | .par _ _ _ :: links, offset, uses =>
      ¬(uses offset ∧ uses (offset + 1)) ∧
        ParPairSparse links (offset + 2) uses

namespace FullSwitchingSelection

theorem choiceSelection {links : List Link} {selected retained : List Edge}
    {mask : List Bool}
    (selection : FullSwitchingSelection links selected retained mask) :
    ChoiceSelection (linkParChoices links) selected := by
  induction selection with
  | nil => exact .nil
  | «axiom» prior ih => simpa [linkParChoices] using ih
  | tensor prior ih => simpa [linkParChoices] using ih
  | parLeft prior ih => simpa [linkParChoices] using ChoiceSelection.left ih
  | parRight prior ih => simpa [linkParChoices] using ChoiceSelection.right ih

theorem edgePermutation {links : List Link} {selected retained : List Edge}
    {mask : List Bool}
    (selection : FullSwitchingSelection links selected retained mask) :
    retained.Perm (linkFixedEdges links ++ selected) := by
  induction selection with
  | nil => exact .nil
  | @«axiom» links selected retained mask left right prior ih =>
      simpa [linkFixedEdges] using
        ih.cons ({ first := left, second := right } : Edge)
  | @tensor links selected retained mask left right conclusion prior ih =>
      simpa [linkFixedEdges] using
        (ih.cons ({ first := right, second := conclusion } : Edge)).cons
          ({ first := left, second := conclusion } : Edge)
  | @parLeft links selected retained mask left right conclusion prior ih =>
      exact (ih.cons ({ first := left, second := conclusion } : Edge)).trans
        (List.perm_middle.symm)
  | @parRight links selected retained mask left right conclusion prior ih =>
      exact (ih.cons ({ first := right, second := conclusion } : Edge)).trans
        (List.perm_middle.symm)

theorem mask_length {links : List Link} {selected retained : List Edge}
    {mask : List Bool}
    (selection : FullSwitchingSelection links selected retained mask) :
    mask.length = (linkFullEdges links).length := by
  induction selection with
  | nil => rfl
  | «axiom» prior ih => simp [linkFullEdges, ih]
  | tensor prior ih => simp [linkFullEdges, ih]
  | parLeft prior ih => simp [linkFullEdges, ih]
  | parRight prior ih => simp [linkFullEdges, ih]

theorem retained_eq_retainByMask {links : List Link}
    {selected retained : List Edge} {mask : List Bool}
    (selection : FullSwitchingSelection links selected retained mask) :
    retained = retainByMask (linkFullEdges links) mask := by
  induction selection with
  | nil => rfl
  | «axiom» prior ih =>
      simp [linkFullEdges, retainByMask, Graph.retainEdgesByMask, ih]
  | tensor prior ih =>
      simp [linkFullEdges, retainByMask, Graph.retainEdgesByMask, ih]
  | parLeft prior ih =>
      simp [linkFullEdges, retainByMask, Graph.retainEdgesByMask, ih]
  | parRight prior ih =>
      simp [linkFullEdges, retainByMask, Graph.retainEdgesByMask, ih]

end FullSwitchingSelection

/-- Any par-sparse set of exact full-edge indices is contained in an
occurrence-order switching. The returned mask is aligned with `linkFullEdges`
and keeps every requested in-range occurrence. -/
theorem fullSwitchingSelection_covering_exists {links : List Link}
    {offset : Nat} {uses : Nat → Prop}
    (sparse : ParPairSparse links offset uses) :
    ∃ selected retained mask,
      FullSwitchingSelection links selected retained mask ∧
        ∀ relativeIndex,
          relativeIndex < (linkFullEdges links).length →
          uses (offset + relativeIndex) →
          mask[relativeIndex]? = some true := by
  classical
  induction links generalizing offset with
  | nil =>
      refine ⟨[], [], [], .nil, ?_⟩
      intro relativeIndex inBounds
      change relativeIndex < 0 at inBounds
      omega
  | cons link rest ih =>
      cases link with
      | «axiom» left right =>
          change ParPairSparse rest (offset + 1) uses at sparse
          rcases ih sparse with ⟨selected, retained, mask, selection, keeps⟩
          refine ⟨selected, _, true :: mask, .axiom selection, ?_⟩
          intro relativeIndex inBounds used
          cases relativeIndex with
          | zero => rfl
          | succ tailIndex =>
              have tailBound : tailIndex < (linkFullEdges rest).length := by
                simpa using inBounds
              have tailUsed : uses ((offset + 1) + tailIndex) := by
                have indexEquation :
                    offset + (tailIndex + 1) = (offset + 1) + tailIndex := by
                  omega
                rw [← indexEquation]
                exact used
              change mask[tailIndex]? = some true
              exact keeps tailIndex tailBound tailUsed
      | tensor left right conclusion =>
          change ParPairSparse rest (offset + 2) uses at sparse
          rcases ih sparse with ⟨selected, retained, mask, selection, keeps⟩
          refine ⟨selected, _, true :: true :: mask, .tensor selection, ?_⟩
          intro relativeIndex inBounds used
          cases relativeIndex with
          | zero => rfl
          | succ afterFirst =>
              cases afterFirst with
              | zero => rfl
              | succ tailIndex =>
                  have tailBound : tailIndex < (linkFullEdges rest).length := by
                    simpa using inBounds
                  have tailUsed : uses ((offset + 2) + tailIndex) := by
                    have indexEquation :
                        offset + ((tailIndex + 1) + 1) =
                          (offset + 2) + tailIndex := by
                      omega
                    rw [← indexEquation]
                    exact used
                  change mask[tailIndex]? = some true
                  exact keeps tailIndex tailBound tailUsed
      | par left right conclusion =>
          change (¬(uses offset ∧ uses (offset + 1))) ∧
            ParPairSparse rest (offset + 2) uses at sparse
          rcases ih sparse.2 with
            ⟨selected, retained, mask, selection, keeps⟩
          by_cases leftUsed : uses offset
          · refine ⟨_, _, true :: false :: mask, .parLeft selection, ?_⟩
            intro relativeIndex inBounds used
            cases relativeIndex with
            | zero => rfl
            | succ afterFirst =>
                cases afterFirst with
                | zero =>
                    exact False.elim (sparse.1 ⟨leftUsed, by simpa using used⟩)
                | succ tailIndex =>
                    have tailBound : tailIndex < (linkFullEdges rest).length := by
                      simpa using inBounds
                    have tailUsed : uses ((offset + 2) + tailIndex) := by
                      have indexEquation :
                          offset + ((tailIndex + 1) + 1) =
                            (offset + 2) + tailIndex := by
                        omega
                      rw [← indexEquation]
                      exact used
                    change mask[tailIndex]? = some true
                    exact keeps tailIndex tailBound tailUsed
          · refine ⟨_, _, false :: true :: mask, .parRight selection, ?_⟩
            intro relativeIndex inBounds used
            cases relativeIndex with
            | zero => exact False.elim (leftUsed (by simpa using used))
            | succ afterFirst =>
                cases afterFirst with
                | zero => rfl
                | succ tailIndex =>
                    have tailBound : tailIndex < (linkFullEdges rest).length := by
                      simpa using inBounds
                    have tailUsed : uses ((offset + 2) + tailIndex) := by
                      have indexEquation :
                          offset + ((tailIndex + 1) + 1) =
                            (offset + 2) + tailIndex := by
                        omega
                      rw [← indexEquation]
                      exact used
                    change mask[tailIndex]? = some true
                    exact keeps tailIndex tailBound tailUsed

theorem fullSwitchingSelection_exists {links : List Link}
    {selected : List Edge}
    (selection : ChoiceSelection (linkParChoices links) selected) :
    ∃ retained mask, FullSwitchingSelection links selected retained mask := by
  induction links generalizing selected with
  | nil =>
      cases selection
      exact ⟨[], [], .nil⟩
  | cons link rest ih =>
      cases link with
      | «axiom» left right =>
          change ChoiceSelection (linkParChoices rest) selected at selection
          rcases ih selection with ⟨retained, mask, realized⟩
          exact ⟨_, _, .axiom realized⟩
      | tensor left right conclusion =>
          change ChoiceSelection (linkParChoices rest) selected at selection
          rcases ih selection with ⟨retained, mask, realized⟩
          exact ⟨_, _, .tensor realized⟩
      | par left right conclusion =>
          change ChoiceSelection
            (({ first := left, second := conclusion },
              { first := right, second := conclusion }) ::
                linkParChoices rest) selected at selection
          cases selection with
          | left prior =>
              rcases ih prior with ⟨retained, mask, realized⟩
              exact ⟨_, _, .parLeft realized⟩
          | right prior =>
              rcases ih prior with ⟨retained, mask, realized⟩
              exact ⟨_, _, .parRight realized⟩

/-- Every independent checker switching has an occurrence-order realization;
its retained edge list differs from the actual checker graph only by storage
order, not by multiplicity or edge identity. -/
theorem occurrenceSwitching_exists (certificate : Certificate)
    {selected : List Edge}
    (selection : ChoiceSelection certificate.parChoices selected) :
    ∃ retained mask,
      FullSwitchingSelection certificate.links selected retained mask ∧
        retained.Perm (certificate.graphForSelection selected).edges := by
  have linkSelection : ChoiceSelection
      (linkParChoices certificate.links) selected := by
    simpa using selection
  rcases fullSwitchingSelection_exists linkSelection with
    ⟨retained, mask, realized⟩
  refine ⟨retained, mask, realized, ?_⟩
  simpa [graphForSelection] using realized.edgePermutation

/-- The unswitched occurrence multigraph. Its stored edge order is part of the
internal incidence identity used by the colored-path layer. -/
def fullGraph (certificate : Certificate) : Graph where
  vertexCount := certificate.formulas.size
  edges := certificate.fullEdges

/-- Local link well-formedness makes every stored full-graph occurrence
loopless. -/
theorem fullEdge_loopless (certificate : Certificate)
    (structural : certificate.StructurallyWellFormed)
    {edge : Edge} (membership : edge ∈ certificate.fullEdges) :
    edge.first ≠ edge.second := by
  simp only [fullEdges, List.mem_flatMap] at membership
  rcases membership with ⟨link, linkMembership, edgeMembership⟩
  have localWellFormed := structural.2.2.2.2.1 link linkMembership
  cases link with
  | «axiom» left right =>
      simp at edgeMembership
      subst edge
      exact localWellFormed.1
  | tensor left right conclusion =>
      simp at edgeMembership
      rcases edgeMembership with same | same <;> subst edge
      · exact localWellFormed.2.1
      · exact localWellFormed.2.2.1
  | par left right conclusion =>
      simp at edgeMembership
      rcases edgeMembership with same | same <;> subst edge
      · exact localWellFormed.2.1
      · exact localWellFormed.2.2.1

/-- Both orientations of every structurally valid full-graph occurrence have
distinct endpoints. -/
theorem fullDirectedEdge_loopless (certificate : Certificate)
    (structural : certificate.StructurallyWellFormed)
    (directed : certificate.fullGraph.DirectedEdge) :
    directed.source ≠ directed.target := by
  have edgeMembership : directed.edge ∈ certificate.fullEdges := by
    simpa [fullGraph] using directed.edge_mem
  have edgeDistinct := certificate.fullEdge_loopless structural edgeMembership
  cases direction : directed.forward with
  | false =>
      simpa [Graph.DirectedEdge.source, Graph.DirectedEdge.target,
        direction] using edgeDistinct.symm
  | true =>
      simpa [Graph.DirectedEdge.source, Graph.DirectedEdge.target,
        direction] using edgeDistinct

/-- Full occurrence edges paired with their exact local par annotation. This
single source-level list is useful for proving that the independently exposed
edge and color projections remain aligned. -/
def fullEdgeAnnotations (certificate : Certificate) :
    List (Edge × Option Vertex) :=
  certificate.links.flatMap fun
    | .axiom left right =>
        [({ first := left, second := right }, none)]
    | .tensor left right conclusion =>
        [({ first := left, second := conclusion }, none),
         ({ first := right, second := conclusion }, none)]
    | .par left right conclusion =>
        [({ first := left, second := conclusion }, some conclusion),
         ({ first := right, second := conclusion }, some conclusion)]

/-- Annotation parallel to `fullEdges`: a `some conclusion` entry records an
edge emitted as a premise of that exact par link. Keeping this list parallel to
the multigraph edges prevents equal-valued parallel edges from being confused. -/
def fullEdgeParTargets (certificate : Certificate) : List (Option Vertex) :=
  linkFullEdgeParTargets certificate.links

theorem linkFullEdgeParTargets_certificate (certificate : Certificate) :
    linkFullEdgeParTargets certificate.links =
      certificate.fullEdgeParTargets := rfl

@[simp] theorem fullEdgeAnnotations_edges (certificate : Certificate) :
    certificate.fullEdgeAnnotations.map Prod.fst =
      certificate.fullEdges := by
  rcases certificate with ⟨formulas, links, conclusions⟩
  simp only [fullEdgeAnnotations, fullEdges]
  induction links with
  | nil => simp
  | cons link rest ih =>
      cases link <;> simp [ih]

@[simp] theorem fullEdgeAnnotations_parTargets (certificate : Certificate) :
    certificate.fullEdgeAnnotations.map Prod.snd =
      certificate.fullEdgeParTargets := by
  rcases certificate with ⟨formulas, links, conclusions⟩
  simp only [fullEdgeAnnotations]
  unfold fullEdgeParTargets
  induction links with
  | nil => simp
  | cons link rest ih =>
      cases link <;> simp [ih]

theorem par_fullEdgeAnnotations (certificate : Certificate)
    {left right conclusion : Vertex}
    (membership : Link.par left right conclusion ∈ certificate.links) :
    (({ first := left, second := conclusion }, some conclusion) ∈
        certificate.fullEdgeAnnotations) ∧
      (({ first := right, second := conclusion }, some conclusion) ∈
        certificate.fullEdgeAnnotations) := by
  simp only [fullEdgeAnnotations, List.mem_flatMap]
  constructor
  · exact ⟨.par left right conclusion, membership, by simp⟩
  · exact ⟨.par left right conclusion, membership, by simp⟩

theorem tensor_fullEdgeAnnotations (certificate : Certificate)
    {left right conclusion : Vertex}
    (membership : Link.tensor left right conclusion ∈ certificate.links) :
    (({ first := left, second := conclusion }, none) ∈
        certificate.fullEdgeAnnotations) ∧
      (({ first := right, second := conclusion }, none) ∈
        certificate.fullEdgeAnnotations) := by
  simp only [fullEdgeAnnotations, List.mem_flatMap]
  constructor
  · exact ⟨.tensor left right conclusion, membership, by simp⟩
  · exact ⟨.tensor left right conclusion, membership, by simp⟩

theorem fullEdgeAnnotation_lookup (certificate : Certificate)
    {index : Nat} {edge : Edge} {parTarget : Option Vertex}
    (lookup : certificate.fullEdgeAnnotations[index]? =
      some (edge, parTarget)) :
    certificate.fullEdges[index]? = some edge ∧
      certificate.fullEdgeParTargets[index]? = some parTarget := by
  constructor
  · have mapped :
        (certificate.fullEdgeAnnotations.map Prod.fst)[index]? =
          some edge := by
      rw [List.getElem?_map, lookup]
      rfl
    rw [certificate.fullEdgeAnnotations_edges] at mapped
    exact mapped
  · have mapped :
        (certificate.fullEdgeAnnotations.map Prod.snd)[index]? =
          some parTarget := by
      rw [List.getElem?_map, lookup]
      rfl
    rw [certificate.fullEdgeAnnotations_parTargets] at mapped
    exact mapped

/-- The aligned edge/color projections recover the unique annotation at an
exact occurrence index. This converse is what prevents equal-valued parallel
edges from exchanging their local switching colors. -/
theorem fullEdgeAnnotation_lookup_iff (certificate : Certificate)
    {index : Nat} {edge : Edge} {parTarget : Option Vertex} :
    certificate.fullEdgeAnnotations[index]? = some (edge, parTarget) ↔
      certificate.fullEdges[index]? = some edge ∧
        certificate.fullEdgeParTargets[index]? = some parTarget := by
  constructor
  · exact certificate.fullEdgeAnnotation_lookup
  · rintro ⟨edgeLookup, targetLookup⟩
    have firstLookup :
        (certificate.fullEdgeAnnotations.map Prod.fst)[index]? = some edge := by
      rw [certificate.fullEdgeAnnotations_edges]
      exact edgeLookup
    have secondLookup :
        (certificate.fullEdgeAnnotations.map Prod.snd)[index]? =
          some parTarget := by
      rw [certificate.fullEdgeAnnotations_parTargets]
      exact targetLookup
    rw [List.getElem?_map] at firstLookup secondLookup
    cases annotationLookup : certificate.fullEdgeAnnotations[index]? with
    | none => simp [annotationLookup] at firstLookup
    | some annotation =>
        rcases annotation with ⟨annotatedEdge, annotatedTarget⟩
        simp [annotationLookup] at firstLookup secondLookup
        subst annotatedEdge
        subst annotatedTarget
        rfl

/-- A par annotation records the stored premise-to-conclusion orientation:
the second endpoint of the annotated occurrence is exactly its par target. -/
theorem fullEdgeAnnotation_some_second (certificate : Certificate)
    {index : Nat} {edge : Edge} {conclusion : Vertex}
    (lookup : certificate.fullEdgeAnnotations[index]? =
      some (edge, some conclusion)) :
    edge.second = conclusion := by
  have membership := List.mem_of_getElem? lookup
  simp only [fullEdgeAnnotations, List.mem_flatMap] at membership
  rcases membership with ⟨link, _, emitted⟩
  cases link with
  | «axiom» left right => simp at emitted
  | tensor left right conclusion => simp at emitted
  | par left right target =>
      simp at emitted
      rcases emitted with first | second
      · rcases first with ⟨rfl, colorEquation⟩
        exact colorEquation.symm
      · rcases second with ⟨rfl, colorEquation⟩
        exact colorEquation.symm

/-- A nonempty par annotation at an exact full-edge index comes from a stored
par link, not merely from an equal-valued parallel edge. -/
theorem fullEdgeAnnotation_some_par_origin (certificate : Certificate)
    {index : Nat} {edge : Edge} {conclusion : Vertex}
    (lookup : certificate.fullEdgeAnnotations[index]? =
      some (edge, some conclusion)) :
    ∃ left right,
      Link.par left right conclusion ∈ certificate.links ∧
        (edge = { first := left, second := conclusion } ∨
          edge = { first := right, second := conclusion }) := by
  have membership := List.mem_of_getElem? lookup
  simp only [fullEdgeAnnotations, List.mem_flatMap] at membership
  rcases membership with ⟨link, linkMembership, emitted⟩
  cases link with
  | «axiom» left right => simp at emitted
  | tensor left right result => simp at emitted
  | par left right result =>
      simp at emitted
      rcases emitted with first | second
      · rcases first with ⟨rfl, resultEquation⟩
        subst result
        exact ⟨left, right, linkMembership, .inl rfl⟩
      · rcases second with ⟨rfl, resultEquation⟩
        subst result
        exact ⟨left, right, linkMembership, .inr rfl⟩

@[simp] theorem fullEdgeParTargets_length (certificate : Certificate) :
    certificate.fullEdgeParTargets.length = certificate.fullEdges.length := by
  change (linkFullEdgeParTargets certificate.links).length =
    (linkFullEdges certificate.links).length
  exact linkFullEdgeParTargets_length certificate.links

/-- Color the incidence at the target of a directed occurrence edge. Only the
stored premise-to-conclusion orientation of a par edge receives the shared par
color. Reversing that edge exposes its other, uniquely colored incidence. -/
def incidenceColor (certificate : Certificate)
    (directed : certificate.fullGraph.DirectedEdge) : LocalSwitchingColor :=
  if directed.forward then
    match certificate.fullEdgeParTargets[directed.index]? with
    | some (some conclusion) => .par conclusion
    | _ => .unique directed.index directed.forward
  else
    .unique directed.index directed.forward

theorem incidenceColor_eq_par_iff (certificate : Certificate)
    (directed : certificate.fullGraph.DirectedEdge)
    (conclusion : Vertex) :
    certificate.incidenceColor directed = .par conclusion ↔
      directed.forward = true ∧
        certificate.fullEdgeParTargets[directed.index]? =
          some (some conclusion) := by
  cases forward : directed.forward with
  | false => simp [incidenceColor, forward]
  | true =>
      cases targetLookup :
          certificate.fullEdgeParTargets[directed.index]? with
      | none => simp [incidenceColor, forward, targetLookup]
      | some parTarget =>
          cases parTarget <;>
            simp [incidenceColor, forward, targetLookup]

/-- If a directed incidence has no shared par color, its color is exactly its
own occurrence index and orientation. -/
theorem incidenceColor_eq_unique_of_not_par (certificate : Certificate)
    (directed : certificate.fullGraph.DirectedEdge)
    (notPar : ∀ conclusion,
      certificate.incidenceColor directed ≠ .par conclusion) :
    certificate.incidenceColor directed =
      .unique directed.index directed.forward := by
  cases forward : directed.forward with
  | false => simp [incidenceColor, forward]
  | true =>
      cases targetLookup :
          certificate.fullEdgeParTargets[directed.index]? with
      | none => simp [incidenceColor, forward, targetLookup]
      | some parTarget =>
          cases parTarget with
          | none => simp [incidenceColor, forward, targetLookup]
          | some conclusion =>
              exact False.elim (notPar conclusion (by
                simp [incidenceColor, forward, targetLookup]))

theorem par_incidenceColors_exist (certificate : Certificate)
    {left right conclusion : Vertex}
    (membership : Link.par left right conclusion ∈ certificate.links) :
    ∃ leftIncidence rightIncidence : certificate.fullGraph.DirectedEdge,
      leftIncidence.source = left ∧
      leftIncidence.target = conclusion ∧
      rightIncidence.source = right ∧
      rightIncidence.target = conclusion ∧
      certificate.incidenceColor leftIncidence = .par conclusion ∧
      certificate.incidenceColor rightIncidence = .par conclusion := by
  have annotations := certificate.par_fullEdgeAnnotations membership
  rcases List.getElem?_of_mem annotations.1 with ⟨leftIndex, leftLookup⟩
  rcases List.getElem?_of_mem annotations.2 with ⟨rightIndex, rightLookup⟩
  have leftProjection := certificate.fullEdgeAnnotation_lookup leftLookup
  have rightProjection := certificate.fullEdgeAnnotation_lookup rightLookup
  let leftIncidence : certificate.fullGraph.DirectedEdge :=
    { index := leftIndex
      edge := { first := left, second := conclusion }
      lookup := leftProjection.1
      forward := true }
  let rightIncidence : certificate.fullGraph.DirectedEdge :=
    { index := rightIndex
      edge := { first := right, second := conclusion }
      lookup := rightProjection.1
      forward := true }
  refine ⟨leftIncidence, rightIncidence, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · simp [incidenceColor, leftIncidence, leftProjection.2]
  · simp [incidenceColor, rightIncidence, rightProjection.2]

/-- The two premise occurrences of a concrete tensor link are represented by
distinct exact indices and carry distinct unique incidence colors at the
tensor conclusion. -/
theorem tensor_incidenceColors_exist (certificate : Certificate)
    {left right conclusion : Vertex}
    (membership : Link.tensor left right conclusion ∈ certificate.links)
    (leftNeRight : left ≠ right) :
    ∃ leftIncidence rightIncidence : certificate.fullGraph.DirectedEdge,
      leftIncidence.source = left ∧
      leftIncidence.target = conclusion ∧
      rightIncidence.source = right ∧
      rightIncidence.target = conclusion ∧
      certificate.incidenceColor leftIncidence =
        .unique leftIncidence.index true ∧
      certificate.incidenceColor rightIncidence =
        .unique rightIncidence.index true ∧
      leftIncidence.index ≠ rightIncidence.index := by
  have annotations := certificate.tensor_fullEdgeAnnotations membership
  rcases List.getElem?_of_mem annotations.1 with ⟨leftIndex, leftLookup⟩
  rcases List.getElem?_of_mem annotations.2 with ⟨rightIndex, rightLookup⟩
  have leftProjection := certificate.fullEdgeAnnotation_lookup leftLookup
  have rightProjection := certificate.fullEdgeAnnotation_lookup rightLookup
  let leftIncidence : certificate.fullGraph.DirectedEdge :=
    { index := leftIndex
      edge := { first := left, second := conclusion }
      lookup := leftProjection.1
      forward := true }
  let rightIncidence : certificate.fullGraph.DirectedEdge :=
    { index := rightIndex
      edge := { first := right, second := conclusion }
      lookup := rightProjection.1
      forward := true }
  have indicesDifferent : leftIncidence.index ≠ rightIncidence.index := by
    intro sameIndex
    have sameOccurrence := Graph.DirectedEdge.eq_of_index_eq_of_forward_eq
      leftIncidence rightIncidence sameIndex rfl
    apply leftNeRight
    have sameSource := congrArg Graph.DirectedEdge.source sameOccurrence
    simpa [leftIncidence, rightIncidence, Graph.DirectedEdge.source] using
      sameSource
  refine ⟨leftIncidence, rightIncidence, rfl, rfl, rfl, rfl, ?_, ?_,
    indicesDifferent⟩
  · simp [incidenceColor, leftIncidence, leftProjection.2]
  · simp [incidenceColor, rightIncidence, rightProjection.2]

/-- A cusp occurs when two consecutive traversals use equally colored
incidences at their common vertex. The outgoing traversal is reversed before
coloring so that both colors are evaluated at that common vertex. -/
def Cusp (certificate : Certificate)
    (incoming outgoing : certificate.fullGraph.DirectedEdge) : Prop :=
  certificate.incidenceColor incoming =
    certificate.incidenceColor outgoing.reverse

instance cuspDecidable (certificate : Certificate)
    (incoming outgoing : certificate.fullGraph.DirectedEdge) :
    Decidable (certificate.Cusp incoming outgoing) := by
  unfold Cusp
  infer_instance

/-- Local cusps are invariant under reversing the direction through their
common vertex. -/
theorem cusp_reverse_iff (certificate : Certificate)
    (incoming outgoing : certificate.fullGraph.DirectedEdge) :
    certificate.Cusp incoming outgoing ↔
      certificate.Cusp outgoing.reverse incoming.reverse := by
  simp only [Cusp, Graph.DirectedEdge.reverse_reverse]
  exact eq_comm

/-- No consecutive pair of traversed edges forms a cusp at its shared
intermediate vertex. Closing-pair cusp-freedom is stated separately for
cycles. -/
def CuspFreeTraversal (certificate : Certificate) :
    List certificate.fullGraph.DirectedEdge → Prop
  | [] => True
  | [_] => True
  | incoming :: outgoing :: rest =>
      ¬certificate.Cusp incoming outgoing ∧
        certificate.CuspFreeTraversal (outgoing :: rest)

theorem CuspFreeTraversal.tail (certificate : Certificate)
    {first : certificate.fullGraph.DirectedEdge}
    {rest : List certificate.fullGraph.DirectedEdge}
    (free : certificate.CuspFreeTraversal (first :: rest)) :
    certificate.CuspFreeTraversal rest := by
  cases rest with
  | nil => trivial
  | cons second tail =>
      cases tail with
      | nil => trivial
      | cons third remaining => exact free.2

theorem CuspFreeTraversal.suffix (certificate : Certificate)
    {initial suffix : List certificate.fullGraph.DirectedEdge}
    (free : certificate.CuspFreeTraversal (initial ++ suffix)) :
    certificate.CuspFreeTraversal suffix := by
  induction initial with
  | nil => simpa using free
  | cons first rest ih =>
      exact ih (CuspFreeTraversal.tail certificate free)

/-- Every list prefix of a cusp-free traversal is cusp-free. -/
theorem CuspFreeTraversal.prefix (certificate : Certificate)
    {initial suffix : List certificate.fullGraph.DirectedEdge}
    (free : certificate.CuspFreeTraversal (initial ++ suffix)) :
    certificate.CuspFreeTraversal initial := by
  induction initial with
  | nil => trivial
  | cons first rest ih =>
      cases rest with
      | nil => trivial
      | cons second tail =>
          exact ⟨free.1, ih free.2⟩

/-- Two nonempty cusp-free traversals concatenate when their boundary
transition is not a cusp. -/
theorem CuspFreeTraversal.append (certificate : Certificate)
    {first second : List certificate.fullGraph.DirectedEdge}
    (firstFree : certificate.CuspFreeTraversal first)
    (secondFree : certificate.CuspFreeTraversal second)
    (firstNonempty : first ≠ []) (secondNonempty : second ≠ [])
    (boundary : ¬certificate.Cusp (first.getLast firstNonempty)
      (second.head secondNonempty)) :
    certificate.CuspFreeTraversal (first ++ second) := by
  induction first with
  | nil => exact False.elim (firstNonempty rfl)
  | cons head tail ih =>
      cases tail with
      | nil =>
          cases second with
          | nil => exact False.elim (secondNonempty rfl)
          | cons next rest =>
              exact ⟨by simpa using boundary, secondFree⟩
      | cons next rest =>
          have tailNonempty : next :: rest ≠ [] := by simp
          have tailBoundary :
              ¬certificate.Cusp ((next :: rest).getLast tailNonempty)
                (second.head secondNonempty) := by
            simpa using boundary
          exact ⟨firstFree.1,
            ih firstFree.2 tailNonempty tailBoundary⟩

/-- Failure of traversal cusp-freedom exposes an internal adjacent cusp. -/
theorem CuspFreeTraversal.exists_cusp_of_not_free
    (certificate : Certificate)
    {traversed : List certificate.fullGraph.DirectedEdge}
    (notFree : ¬certificate.CuspFreeTraversal traversed) :
    ∃ before incoming outgoing after,
      traversed = before ++ incoming :: outgoing :: after ∧
        certificate.Cusp incoming outgoing := by
  induction traversed with
  | nil => exact False.elim (notFree trivial)
  | cons first rest ih =>
      cases rest with
      | nil => exact False.elim (notFree trivial)
      | cons second tail =>
          by_cases cusp : certificate.Cusp first second
          · exact ⟨[], first, second, tail, by simp, cusp⟩
          · have tailNotFree :
                ¬certificate.CuspFreeTraversal (second :: tail) := by
              intro tailFree
              exact notFree ⟨cusp, tailFree⟩
            rcases ih tailNotFree with
              ⟨before, incoming, outgoing, after, equation, found⟩
            exact ⟨first :: before, incoming, outgoing, after,
              by simp [equation], found⟩

/-- The first internal cusp can be chosen with a cusp-free prefix ending at
its incoming edge. -/
theorem CuspFreeTraversal.exists_first_cusp_of_not_free
    (certificate : Certificate)
    {traversed : List certificate.fullGraph.DirectedEdge}
    (notFree : ¬certificate.CuspFreeTraversal traversed) :
    ∃ before incoming outgoing after,
      traversed = before ++ incoming :: outgoing :: after ∧
      certificate.Cusp incoming outgoing ∧
      certificate.CuspFreeTraversal (before ++ [incoming]) := by
  induction traversed with
  | nil => exact False.elim (notFree trivial)
  | cons first rest ih =>
      cases rest with
      | nil => exact False.elim (notFree trivial)
      | cons second tail =>
          by_cases cusp : certificate.Cusp first second
          · exact ⟨[], first, second, tail, by simp, cusp, by trivial⟩
          · have tailNotFree :
                ¬certificate.CuspFreeTraversal (second :: tail) := by
              intro tailFree
              exact notFree ⟨cusp, tailFree⟩
            rcases ih tailNotFree with
              ⟨before, incoming, outgoing, after, equation, found, prefixFree⟩
            have enlargedPrefixFree : certificate.CuspFreeTraversal
                ((first :: before) ++ [incoming]) := by
              cases before with
              | nil =>
                  have sameIncoming : second = incoming :=
                    (List.cons.inj equation).1
                  subst incoming
                  exact ⟨cusp, trivial⟩
              | cons prefixHead prefixTail =>
                  have sameHead : second = prefixHead :=
                    (List.cons.inj equation).1
                  subst prefixHead
                  exact ⟨cusp, prefixFree⟩
            exact ⟨first :: before, incoming, outgoing, after,
              by simp [equation], found, enlargedPrefixFree⟩

/-- Number of internal adjacent cusps in a directed traversal. The closing
transition of a cycle is deliberately counted separately by `ClosingCusp`. -/
def cuspCount (certificate : Certificate) :
    List certificate.fullGraph.DirectedEdge → Nat
  | incoming :: outgoing :: rest =>
      (if certificate.Cusp incoming outgoing then 1 else 0) +
        certificate.cuspCount (outgoing :: rest)
  | _ => 0

/-- Numeric contribution of one adjacent directed-edge pair. -/
def cuspIndicator (certificate : Certificate)
    (incoming outgoing : certificate.fullGraph.DirectedEdge) : Nat :=
  if certificate.Cusp incoming outgoing then 1 else 0

/-- The single possible cusp contribution across a list concatenation. -/
def cuspBoundaryCount (certificate : Certificate)
    (first second : List certificate.fullGraph.DirectedEdge) : Nat :=
  match first.getLast?, second.head? with
  | some incoming, some outgoing =>
      certificate.cuspIndicator incoming outgoing
  | _, _ => 0

/-- Number of cusps in a traversal viewed cyclically. Unlike `cuspCount`,
this also includes the transition from the final edge back to the first. -/
def cyclicCuspCount (certificate : Certificate)
    (traversed : List certificate.fullGraph.DirectedEdge) : Nat :=
  certificate.cuspCount traversed +
    certificate.cuspBoundaryCount traversed traversed

theorem cuspBoundaryCount_le_one (certificate : Certificate)
    (first second : List certificate.fullGraph.DirectedEdge) :
    certificate.cuspBoundaryCount first second ≤ 1 := by
  cases firstLookup : first.getLast? with
  | none => simp [cuspBoundaryCount, firstLookup]
  | some incoming =>
      cases secondLookup : second.head? with
      | none => simp [cuspBoundaryCount, firstLookup, secondLookup]
      | some outgoing =>
          by_cases cusp : certificate.Cusp incoming outgoing <;>
            simp [cuspBoundaryCount, firstLookup, secondLookup,
              cuspIndicator, cusp]

/-- Internal cusp counting is additive up to the unique concatenation
boundary. This arithmetic form is the bookkeeping interface used by the
bungee argument. -/
theorem cuspCount_append (certificate : Certificate)
    (first second : List certificate.fullGraph.DirectedEdge) :
    certificate.cuspCount (first ++ second) =
      certificate.cuspCount first + certificate.cuspCount second +
        certificate.cuspBoundaryCount first second := by
  induction first with
  | nil => simp [cuspCount, cuspBoundaryCount]
  | cons incoming rest ih =>
      cases rest with
      | nil =>
          cases second with
          | nil => simp [cuspCount, cuspBoundaryCount]
          | cons outgoing tail =>
              simp [cuspCount, cuspBoundaryCount, cuspIndicator]
              omega
      | cons next tail =>
          simp only [List.cons_append, cuspCount]
          change (if certificate.Cusp incoming next then 1 else 0) +
              certificate.cuspCount ((next :: tail) ++ second) = _
          rw [ih]
          simp [cuspBoundaryCount, cuspIndicator, Nat.add_assoc]

/-- For two nonempty blocks, the closing boundary of their concatenation is
the boundary from the second block back to the first. -/
theorem cuspBoundaryCount_append_self (certificate : Certificate)
    {first second : List certificate.fullGraph.DirectedEdge}
    (firstNonempty : first ≠ []) (secondNonempty : second ≠ []) :
    certificate.cuspBoundaryCount (first ++ second) (first ++ second) =
      certificate.cuspBoundaryCount second first := by
  cases first with
  | nil => exact False.elim (firstNonempty rfl)
  | cons firstHead firstTail =>
      cases second with
      | nil => exact False.elim (secondNonempty rfl)
      | cons secondHead secondTail =>
          simp only [cuspBoundaryCount, List.head?_cons]
          rw [List.getLast?_append]
          rw [List.getLast?_eq_some_getLast (by simp :
            secondHead :: secondTail ≠ [])]
          simp

/-- Cyclic cusp counting is invariant under rotation of two list blocks. -/
theorem cyclicCuspCount_append_comm (certificate : Certificate)
    (first second : List certificate.fullGraph.DirectedEdge) :
    certificate.cyclicCuspCount (first ++ second) =
      certificate.cyclicCuspCount (second ++ first) := by
  by_cases firstEmpty : first = []
  · subst first
    simp [cyclicCuspCount]
  · by_cases secondEmpty : second = []
    · subst second
      simp [cyclicCuspCount]
    · rw [cyclicCuspCount, cyclicCuspCount,
        certificate.cuspCount_append first second,
        certificate.cuspCount_append second first,
        certificate.cuspBoundaryCount_append_self firstEmpty secondEmpty,
        certificate.cuspBoundaryCount_append_self secondEmpty firstEmpty]
      omega

/-- Reversing a traversal and every directed incidence preserves its number
of internal cusps. -/
theorem cuspCount_reverseTraversal (certificate : Certificate)
    (traversed : List certificate.fullGraph.DirectedEdge) :
    certificate.cuspCount
        (Graph.EdgeWalk.reverseTraversal traversed) =
      certificate.cuspCount traversed := by
  induction traversed with
  | nil => simp [Graph.EdgeWalk.reverseTraversal, cuspCount]
  | cons incoming rest ih =>
      cases rest with
      | nil => simp [Graph.EdgeWalk.reverseTraversal, cuspCount]
      | cons outgoing tail =>
          have reversedEquation :
              Graph.EdgeWalk.reverseTraversal
                  (incoming :: outgoing :: tail) =
                Graph.EdgeWalk.reverseTraversal (outgoing :: tail) ++
                  [incoming.reverse] := by
            simp [Graph.EdgeWalk.reverseTraversal, List.map_append]
          rw [reversedEquation, certificate.cuspCount_append, ih]
          simp [cuspCount, cuspBoundaryCount, cuspIndicator,
            Graph.EdgeWalk.reverseTraversal,
            certificate.cusp_reverse_iff incoming outgoing,
            Nat.add_comm]

theorem cuspCount_eq_zero_iff (certificate : Certificate)
    (traversed : List certificate.fullGraph.DirectedEdge) :
    certificate.cuspCount traversed = 0 ↔
      certificate.CuspFreeTraversal traversed := by
  induction traversed with
  | nil => simp [cuspCount, CuspFreeTraversal]
  | cons first rest ih =>
      cases rest with
      | nil => simp [cuspCount, CuspFreeTraversal]
      | cons second tail =>
          by_cases cusp : certificate.Cusp first second
          · simp [cuspCount, CuspFreeTraversal, cusp]
          · simp [cuspCount, CuspFreeTraversal, cusp, ih]

theorem cuspBoundaryCount_eq_one (certificate : Certificate)
    {first second : List certificate.fullGraph.DirectedEdge}
    (firstNonempty : first ≠ []) (secondNonempty : second ≠ [])
    (boundary : certificate.Cusp (first.getLast firstNonempty)
      (second.head secondNonempty)) :
    certificate.cuspBoundaryCount first second = 1 := by
  simp [cuspBoundaryCount, List.getLast?_eq_some_getLast firstNonempty,
    List.head?_eq_some_head secondNonempty, cuspIndicator, boundary]

theorem cuspBoundaryCount_eq_zero (certificate : Certificate)
    {first second : List certificate.fullGraph.DirectedEdge}
    (firstNonempty : first ≠ []) (secondNonempty : second ≠ [])
    (boundary : ¬certificate.Cusp (first.getLast firstNonempty)
      (second.head secondNonempty)) :
    certificate.cuspBoundaryCount first second = 0 := by
  simp [cuspBoundaryCount, List.getLast?_eq_some_getLast firstNonempty,
    List.head?_eq_some_head secondNonempty, cuspIndicator, boundary]

theorem cuspBoundaryCount_eq_zero_iff (certificate : Certificate)
    {first second : List certificate.fullGraph.DirectedEdge}
    (firstNonempty : first ≠ []) (secondNonempty : second ≠ []) :
    certificate.cuspBoundaryCount first second = 0 ↔
      ¬certificate.Cusp (first.getLast firstNonempty)
        (second.head secondNonempty) := by
  simp [cuspBoundaryCount, List.getLast?_eq_some_getLast firstNonempty,
    List.head?_eq_some_head secondNonempty, cuspIndicator]

theorem cuspBoundaryCount_eq_one_iff (certificate : Certificate)
    {first second : List certificate.fullGraph.DirectedEdge}
    (firstNonempty : first ≠ []) (secondNonempty : second ≠ []) :
    certificate.cuspBoundaryCount first second = 1 ↔
      certificate.Cusp (first.getLast firstNonempty)
        (second.head secondNonempty) := by
  simp [cuspBoundaryCount, List.getLast?_eq_some_getLast firstNonempty,
    List.head?_eq_some_head secondNonempty, cuspIndicator]

theorem cuspCount_eq_zero_of_free (certificate : Certificate)
    {traversed : List certificate.fullGraph.DirectedEdge}
    (free : certificate.CuspFreeTraversal traversed) :
    certificate.cuspCount traversed = 0 :=
  (certificate.cuspCount_eq_zero_iff traversed).2 free

/-- If a concatenation has exactly one cusp and its boundary is a cusp, both
pieces are internally cusp-free. -/
theorem cuspCount_one_boundary_splits_free (certificate : Certificate)
    {first second : List certificate.fullGraph.DirectedEdge}
    (firstNonempty : first ≠ []) (secondNonempty : second ≠ [])
    (boundary : certificate.Cusp (first.getLast firstNonempty)
      (second.head secondNonempty))
    (one : certificate.cuspCount (first ++ second) = 1) :
    certificate.CuspFreeTraversal first ∧
      certificate.CuspFreeTraversal second := by
  have countEquation := certificate.cuspCount_append first second
  have boundaryCount := certificate.cuspBoundaryCount_eq_one
    firstNonempty secondNonempty boundary
  rw [one, boundaryCount] at countEquation
  have firstZero : certificate.cuspCount first = 0 := by omega
  have secondZero : certificate.cuspCount second = 0 := by omega
  exact ⟨(certificate.cuspCount_eq_zero_iff first).1 firstZero,
    (certificate.cuspCount_eq_zero_iff second).1 secondZero⟩

/-- Cusp-freedom is invariant under reversing the order and orientation of
the whole traversal. -/
theorem cuspFreeTraversal_reverse_iff (certificate : Certificate)
    (traversed : List certificate.fullGraph.DirectedEdge) :
    certificate.CuspFreeTraversal
        (Graph.EdgeWalk.reverseTraversal traversed) ↔
      certificate.CuspFreeTraversal traversed := by
  calc
    certificate.CuspFreeTraversal
          (Graph.EdgeWalk.reverseTraversal traversed) ↔
        certificate.cuspCount
            (Graph.EdgeWalk.reverseTraversal traversed) = 0 :=
      (certificate.cuspCount_eq_zero_iff
        (Graph.EdgeWalk.reverseTraversal traversed)).symm
    _ ↔ certificate.cuspCount traversed = 0 := by
      rw [certificate.cuspCount_reverseTraversal traversed]
    _ ↔ certificate.CuspFreeTraversal traversed :=
      certificate.cuspCount_eq_zero_iff traversed

/-- A simple, open, cusp-free continuation from the target of `incoming` to
the target of `outgoing`, ending with that exact directed edge. -/
structure CuspFreeContinuation (certificate : Certificate)
    (incoming outgoing : certificate.fullGraph.DirectedEdge) where
  path : certificate.fullGraph.EdgeSimplePath
  nonempty : path.traversed ≠ []
  startsAt : path.start = incoming.target
  endsAt : path.finish = outgoing.target
  cuspFree : certificate.CuspFreeTraversal path.traversed
  initialFree :
    ¬certificate.Cusp incoming (path.traversed.head nonempty)
  lastEdge : path.traversed.getLast nonempty = outgoing

namespace CuspFreeContinuation

/-- A continuation leaving the target of the incoming side of a cusp can be
viewed as leaving the target of the reversed outgoing side.  This is the
orientation change used when the ambient cycle is reversed. -/
def rebaseAtReversedPartner {certificate : Certificate}
    {incoming partner outgoing : certificate.fullGraph.DirectedEdge}
    (continuation : CuspFreeContinuation certificate incoming outgoing)
    (meeting : incoming.target = partner.source)
    (cusp : certificate.Cusp incoming partner) :
    CuspFreeContinuation certificate partner.reverse outgoing where
  path := continuation.path
  nonempty := continuation.nonempty
  startsAt := by
    rw [Graph.DirectedEdge.reverse_target]
    exact continuation.startsAt.trans meeting
  endsAt := continuation.endsAt
  cuspFree := continuation.cuspFree
  initialFree := by
    intro partnerCusp
    apply continuation.initialFree
    unfold Certificate.Cusp at cusp partnerCusp ⊢
    exact cusp.trans partnerCusp
  lastEdge := continuation.lastEdge

/-- The first step of a continuation cannot reuse the incoming stored edge in
either orientation. The forward orientation would revisit the path start; the
reverse orientation would form the forbidden immediate cusp. -/
theorem head_index_ne_incoming {certificate : Certificate}
    {incoming outgoing : certificate.fullGraph.DirectedEdge}
    (continuation : CuspFreeContinuation certificate incoming outgoing) :
    (continuation.path.traversed.head continuation.nonempty).index ≠
      incoming.index := by
  intro sameIndex
  let first := continuation.path.traversed.head continuation.nonempty
  have alternatives := Graph.DirectedEdge.eq_or_eq_reverse_of_index_eq
    first incoming sameIndex
  rcases alternatives with same | reversed
  · have startFresh : continuation.path.start ∉
        continuation.path.traversed.map Graph.DirectedEdge.target := by
      have nodup : (continuation.path.start ::
          continuation.path.traversed.map
            Graph.DirectedEdge.target).Nodup := by
        simpa [Graph.EdgeSimplePath.vertices,
          Graph.EdgeWalk.visitedVertices] using
            continuation.path.verticesNodup
      exact (List.nodup_cons.mp nodup).1
    apply startFresh
    have firstMembership : first ∈ continuation.path.traversed := by
      exact List.head_mem continuation.nonempty
    apply List.mem_map.mpr
    refine ⟨first, firstMembership, ?_⟩
    rw [same]
    exact continuation.startsAt.symm
  · apply continuation.initialFree
    change certificate.Cusp incoming first
    rw [reversed]
    unfold Cusp
    simp

/-- If `partner` is the next edge at the incoming cusp, the first step of a
continuation cannot reuse that occurrence either. The equal orientation is
excluded by initial cusp-freedom; the reverse orientation would force a loop.
-/
theorem head_index_ne_cusp_partner {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    {incoming outgoing partner : certificate.fullGraph.DirectedEdge}
    (continuation : CuspFreeContinuation certificate incoming outgoing)
    (meeting : incoming.target = partner.source)
    (cusp : certificate.Cusp incoming partner) :
    (continuation.path.traversed.head continuation.nonempty).index ≠
      partner.index := by
  intro sameIndex
  let first := continuation.path.traversed.head continuation.nonempty
  rcases Graph.DirectedEdge.eq_or_eq_reverse_of_index_eq first partner
      sameIndex with same | reversed
  · apply continuation.initialFree
    change certificate.Cusp incoming first
    rw [same]
    exact cusp
  · have headSource : first.source = continuation.path.start := by
      cases traversalEquation : continuation.path.traversed with
      | nil => exact False.elim (continuation.nonempty traversalEquation)
      | cons head tail =>
          have chain := continuation.path.walk.toChain
          rw [traversalEquation] at chain
          simpa [first, traversalEquation] using chain.head_source
    apply certificate.fullDirectedEdge_loopless structural partner
    calc
      partner.source = incoming.target := meeting.symm
      _ = continuation.path.start := continuation.startsAt.symm
      _ = first.source := headSource.symm
      _ = partner.reverse.source := by rw [reversed]
      _ = partner.target := Graph.DirectedEdge.reverse_source partner

/-- Concatenate compatible continuations. The explicit vertex-disjointness
hypothesis is exactly what preserves simplicity after the shared endpoint is
removed from the second path's vertex list. -/
def append {certificate : Certificate}
    {incoming middle outgoing : certificate.fullGraph.DirectedEdge}
    (first : CuspFreeContinuation certificate incoming middle)
    (second : CuspFreeContinuation certificate middle outgoing)
    (disjoint : ∀ vertex, vertex ∈ first.path.vertices →
      vertex ∈ second.path.vertices.tail → False) :
    CuspFreeContinuation certificate incoming outgoing := by
  have meeting : first.path.finish = second.path.start :=
    first.endsAt.trans second.startsAt.symm
  let combinedPath := first.path.append second.path meeting disjoint
  have combinedNonempty : combinedPath.traversed ≠ [] := by
    simp [combinedPath, first.nonempty]
  have boundary : ¬certificate.Cusp
      (first.path.traversed.getLast first.nonempty)
      (second.path.traversed.head second.nonempty) := by
    rw [first.lastEdge]
    exact second.initialFree
  refine
    { path := combinedPath
      nonempty := combinedNonempty
      startsAt := ?_
      endsAt := ?_
      cuspFree := ?_
      initialFree := ?_
      lastEdge := ?_ }
  · exact first.startsAt
  · exact second.endsAt
  · change certificate.CuspFreeTraversal
      (first.path.traversed ++ second.path.traversed)
    exact CuspFreeTraversal.append certificate first.cuspFree second.cuspFree
      first.nonempty second.nonempty boundary
  · have headEquation :
        (first.path.traversed ++ second.path.traversed).head
            combinedNonempty =
          first.path.traversed.head first.nonempty :=
      List.head_append_of_ne_nil first.nonempty
    change ¬certificate.Cusp incoming
      ((first.path.traversed ++ second.path.traversed).head combinedNonempty)
    rw [headEquation]
    exact first.initialFree
  · have lastEquation :
        (first.path.traversed ++ second.path.traversed).getLast
            combinedNonempty =
          second.path.traversed.getLast second.nonempty :=
      List.getLast_append_of_ne_nil combinedNonempty second.nonempty
    change (first.path.traversed ++ second.path.traversed).getLast
      combinedNonempty = outgoing
    rw [lastEquation]
    exact second.lastEdge

@[simp] theorem append_path_vertices {certificate : Certificate}
    {incoming middle outgoing : certificate.fullGraph.DirectedEdge}
    (first : CuspFreeContinuation certificate incoming middle)
    (second : CuspFreeContinuation certificate middle outgoing)
    (disjoint : ∀ vertex, vertex ∈ first.path.vertices →
      vertex ∈ second.path.vertices.tail → False) :
    (first.append second disjoint).path.vertices =
      first.path.vertices ++ second.path.vertices.tail := by
  simp [append]

/-- Truncate a continuation at a specified exact edge occurrence in its
traversal. The returned continuation exposes its precise prefix list. -/
theorem prefixAtEdge {certificate : Certificate}
    {incoming outgoing : certificate.fullGraph.DirectedEdge}
    (continuation : CuspFreeContinuation certificate incoming outgoing)
    {before after : List certificate.fullGraph.DirectedEdge}
    {last : certificate.fullGraph.DirectedEdge}
    (traversalEquation :
      continuation.path.traversed = before ++ last :: after) :
    ∃ truncated : CuspFreeContinuation certificate incoming last,
      truncated.path.traversed = before ++ [last] := by
  rcases continuation.path.prefixPath traversalEquation with
    ⟨initialPath, prefixStarts, prefixFinishes, prefixSteps⟩
  have prefixNonempty : initialPath.traversed ≠ [] := by
    rw [prefixSteps]
    simp
  have decomposedFree : certificate.CuspFreeTraversal
      ((before ++ [last]) ++ after) := by
    simpa [traversalEquation, List.append_assoc] using
      continuation.cuspFree
  have prefixFree : certificate.CuspFreeTraversal (before ++ [last]) :=
    CuspFreeTraversal.prefix certificate decomposedFree
  have headEquation :
      initialPath.traversed.head prefixNonempty =
        continuation.path.traversed.head continuation.nonempty := by
    cases before <;> simp [prefixSteps, traversalEquation]
  let truncated : CuspFreeContinuation certificate incoming last :=
    { path := initialPath
      nonempty := prefixNonempty
      startsAt := prefixStarts.trans continuation.startsAt
      endsAt := prefixFinishes
      cuspFree := by simpa [prefixSteps] using prefixFree
      initialFree := by simpa [headEquation] using continuation.initialFree
      lastEdge := by simp [prefixSteps] }
  exact ⟨truncated, by simpa [truncated] using prefixSteps⟩

/-- Truncate a continuation at any visited vertex after its start. The exact
last directed edge becomes the new outgoing occurrence. -/
theorem prefixToTailVertex {certificate : Certificate}
    {incoming outgoing : certificate.fullGraph.DirectedEdge}
    (continuation : CuspFreeContinuation certificate incoming outgoing)
    {vertex : Vertex}
    (membership : vertex ∈ continuation.path.vertices.tail) :
    ∃ last : certificate.fullGraph.DirectedEdge,
      Nonempty (CuspFreeContinuation certificate incoming last) ∧
        last.target = vertex := by
  rcases continuation.path.prefixToTailVertex membership with
    ⟨initialPath, before, after, last, traversalEquation,
      prefixStarts, prefixFinishes, prefixSteps, lastTarget⟩
  have prefixNonempty : initialPath.traversed ≠ [] := by
    rw [prefixSteps]
    simp
  have decomposedFree : certificate.CuspFreeTraversal
      ((before ++ [last]) ++ after) := by
    simpa [traversalEquation, List.append_assoc] using
      continuation.cuspFree
  have prefixFree : certificate.CuspFreeTraversal (before ++ [last]) :=
    CuspFreeTraversal.prefix certificate decomposedFree
  have headEquation :
      initialPath.traversed.head prefixNonempty =
        continuation.path.traversed.head continuation.nonempty := by
    cases before <;> simp [prefixSteps, traversalEquation]
  refine ⟨last, ⟨?_⟩, lastTarget⟩
  exact
    { path := initialPath
      nonempty := prefixNonempty
      startsAt := prefixStarts.trans continuation.startsAt
      endsAt := prefixFinishes.trans lastTarget.symm
      cuspFree := by simpa [prefixSteps] using prefixFree
      initialFree := by simpa [headEquation] using continuation.initialFree
      lastEdge := by simp [prefixSteps] }

/-- Truncate at the first endpoint that enters a specified finite vertex list.
Within the returned prefix, that endpoint is the only visited tail vertex in
the list. -/
theorem prefixToFirstIntersection {certificate : Certificate}
    {incoming outgoing : certificate.fullGraph.DirectedEdge}
    (continuation : CuspFreeContinuation certificate incoming outgoing)
    (vertices : List Vertex)
    (intersects : ∃ vertex,
      vertex ∈ continuation.path.vertices.tail ∧ vertex ∈ vertices) :
    ∃ (last : certificate.fullGraph.DirectedEdge)
      (truncated : CuspFreeContinuation certificate incoming last),
      last.target ∈ vertices ∧
      ∀ vertex, vertex ∈ truncated.path.vertices.tail →
        vertex ∈ vertices → vertex = last.target := by
  have edgeExists : ∃ directed ∈ continuation.path.traversed,
      directed.target ∈ vertices := by
    rcases intersects with ⟨vertex, inTail, inVertices⟩
    have targetMembership : vertex ∈
        continuation.path.traversed.map Graph.DirectedEdge.target := by
      simpa [Graph.EdgeSimplePath.vertices,
        Graph.EdgeWalk.visitedVertices] using inTail
    rcases List.mem_map.mp targetMembership with
      ⟨directed, directedMembership, targetEquation⟩
    exact ⟨directed, directedMembership, targetEquation.symm ▸ inVertices⟩
  rcases Graph.exists_first_decomposition continuation.path.traversed
      (fun directed => directed.target ∈ vertices) edgeExists with
    ⟨before, last, after, traversalEquation, lastIn, beforeAvoids⟩
  rcases continuation.prefixAtEdge traversalEquation with
    ⟨truncated, truncatedSteps⟩
  refine ⟨last, truncated, lastIn, ?_⟩
  intro vertex inTruncated inVertices
  have targetMembership : vertex ∈
      truncated.path.traversed.map Graph.DirectedEdge.target := by
    simpa [Graph.EdgeSimplePath.vertices,
      Graph.EdgeWalk.visitedVertices] using inTruncated
  rw [truncatedSteps, List.map_append] at targetMembership
  rcases List.mem_append.mp targetMembership with inBefore | atLast
  · rcases List.mem_map.mp inBefore with
      ⟨earlier, earlierMembership, earlierTarget⟩
    exact False.elim
      (beforeAvoids earlier earlierMembership (earlierTarget.symm ▸ inVertices))
  · simpa using atLast

/-- An intersection between a continuation prefix and a later continuation
determines a simple return suffix inside the first path. -/
theorem returnSuffixFromIntersection {certificate : Certificate}
    {incoming middle outgoing : certificate.fullGraph.DirectedEdge}
    (first : CuspFreeContinuation certificate incoming middle)
    (later : CuspFreeContinuation certificate middle outgoing)
    {vertex : Vertex}
    (inFirst : vertex ∈ first.path.vertices)
    (inLater : vertex ∈ later.path.vertices.tail) :
    ∃ returnPath : certificate.fullGraph.EdgeSimplePath,
      returnPath.start = vertex ∧
      returnPath.finish = middle.target ∧
      (∀ candidate, candidate ∈ returnPath.vertices →
        candidate ∈ first.path.vertices) ∧
      certificate.CuspFreeTraversal returnPath.traversed ∧
      returnPath.traversed.getLast? = some middle := by
  have notFinish : vertex ≠ first.path.finish := by
    intro atFinish
    have atLaterStart : vertex = later.path.start :=
      atFinish.trans (first.endsAt.trans later.startsAt.symm)
    apply later.path.start_not_mem_vertices_tail
    rw [← atLaterStart]
    exact inLater
  rcases first.path.outgoingAtVertex inFirst notFinish with
    ⟨before, next, after, traversalEquation, nextSource⟩
  rcases first.path.suffixPath traversalEquation with
    ⟨returnPath, returnStarts, returnFinishes, returnSteps,
      returnSubset⟩
  have fullLast : first.path.traversed.getLast? = some middle := by
    rw [List.getLast?_eq_some_getLast first.nonempty, first.lastEdge]
  rw [traversalEquation] at fullLast
  have returnLast : returnPath.traversed.getLast? = some middle := by
    rw [returnSteps]
    simpa using fullLast
  have suffixFree : certificate.CuspFreeTraversal (next :: after) := by
    have fullFree : certificate.CuspFreeTraversal
        (before ++ next :: after) := by
      rw [← traversalEquation]
      exact first.cuspFree
    exact CuspFreeTraversal.suffix certificate fullFree
  have returnFree : certificate.CuspFreeTraversal returnPath.traversed := by
    rw [returnSteps]
    exact suffixFree
  exact ⟨returnPath, returnStarts.trans nextSource,
    returnFinishes.trans first.endsAt, returnSubset, returnFree, returnLast⟩

/-- First-intersection normalization gives exactly the vertex separation
needed to close the later prefix with the return suffix. -/
theorem firstIntersection_vertexDisjoint {certificate : Certificate}
    {incoming middle last : certificate.fullGraph.DirectedEdge}
    (first : CuspFreeContinuation certificate incoming middle)
    (later : CuspFreeContinuation certificate middle last)
    (returnPath : certificate.fullGraph.EdgeSimplePath)
    (returnStarts : returnPath.start = last.target)
    (returnFinishes : returnPath.finish = middle.target)
    (returnSubset : ∀ candidate, candidate ∈ returnPath.vertices →
      candidate ∈ first.path.vertices)
    (uniqueIntersection : ∀ vertex,
      vertex ∈ later.path.vertices.tail →
      vertex ∈ first.path.vertices → vertex = last.target)
    (returnNonempty : returnPath.traversed ≠ []) :
    ∀ vertex, vertex ∈ later.path.vertices →
      vertex ∈ returnPath.vertices.tail.dropLast → False := by
  intro vertex inLater inReturnInterior
  have inReturnTail : vertex ∈ returnPath.vertices.tail :=
    Graph.mem_of_mem_dropLast inReturnInterior
  have inReturn : vertex ∈ returnPath.vertices :=
    List.mem_of_mem_tail inReturnTail
  have inFirst := returnSubset vertex inReturn
  by_cases atLaterStart : vertex = later.path.start
  · apply returnPath.finish_not_mem_vertices_tail_dropLast returnNonempty
    have atReturnFinish : vertex = returnPath.finish := by
      calc
        vertex = later.path.start := atLaterStart
        _ = middle.target := later.startsAt
        _ = returnPath.finish := returnFinishes.symm
    rw [← atReturnFinish]
    exact inReturnInterior
  · have inLaterTail : vertex ∈ later.path.vertices.tail := by
      change vertex ∈
        later.path.traversed.map Graph.DirectedEdge.target
      simp only [Graph.EdgeSimplePath.vertices,
        Graph.EdgeWalk.visitedVertices, List.mem_cons] at inLater
      exact inLater.resolve_left atLaterStart
    have atLastTarget := uniqueIntersection vertex inLaterTail inFirst
    apply returnPath.start_not_mem_vertices_tail
    rw [returnStarts, ← atLastTarget]
    exact inReturnTail

/-- The later prefix and its return suffix share no exact edge occurrence.
Any hypothetical shared occurrence is forced to be both the later head and the
return last edge, contradicting continuation initial-freedom. -/
theorem firstIntersection_edgeDisjoint {certificate : Certificate}
    {incoming middle last : certificate.fullGraph.DirectedEdge}
    (first : CuspFreeContinuation certificate incoming middle)
    (later : CuspFreeContinuation certificate middle last)
    (returnPath : certificate.fullGraph.EdgeSimplePath)
    (returnStarts : returnPath.start = last.target)
    (returnFinishes : returnPath.finish = middle.target)
    (returnSubset : ∀ candidate, candidate ∈ returnPath.vertices →
      candidate ∈ first.path.vertices)
    (uniqueIntersection : ∀ vertex,
      vertex ∈ later.path.vertices.tail →
      vertex ∈ first.path.vertices → vertex = last.target)
    (returnLast : returnPath.traversed.getLast? = some middle) :
    ∀ index,
      index ∈ later.path.traversed.map Graph.DirectedEdge.index →
      index ∈ returnPath.traversed.map Graph.DirectedEdge.index →
      False := by
  intro index inLaterIndices inReturnIndices
  rcases List.mem_map.mp inLaterIndices with
    ⟨laterEdge, laterEdgeMembership, laterIndex⟩
  rcases List.mem_map.mp inReturnIndices with
    ⟨returnEdge, returnEdgeMembership, returnIndex⟩
  have sameIndex : laterEdge.index = returnEdge.index :=
    laterIndex.trans returnIndex.symm
  rcases Graph.DirectedEdge.eq_or_eq_reverse_of_index_eq
      laterEdge returnEdge sameIndex with same | reversed
  · have laterTargetInTail : laterEdge.target ∈
        later.path.vertices.tail := by
      change laterEdge.target ∈
        later.path.traversed.map Graph.DirectedEdge.target
      exact List.mem_map.mpr ⟨laterEdge, laterEdgeMembership, rfl⟩
    have returnTargetInReturn : returnEdge.target ∈ returnPath.vertices :=
      (returnPath.walk.endpoints_mem_visitedVertices
        returnEdgeMembership).2
    have laterTargetInFirst : laterEdge.target ∈ first.path.vertices := by
      rw [same]
      exact returnSubset returnEdge.target returnTargetInReturn
    have targetAtIntersection := uniqueIntersection laterEdge.target
      laterTargetInTail laterTargetInFirst
    apply returnPath.start_not_mem_vertices_tail
    have returnTargetInTail : returnEdge.target ∈ returnPath.vertices.tail := by
      change returnEdge.target ∈
        returnPath.traversed.map Graph.DirectedEdge.target
      exact List.mem_map.mpr ⟨returnEdge, returnEdgeMembership, rfl⟩
    rw [returnStarts, ← targetAtIntersection, same]
    exact returnTargetInTail
  · have laterTargetInTail : laterEdge.target ∈
        later.path.vertices.tail := by
      change laterEdge.target ∈
        later.path.traversed.map Graph.DirectedEdge.target
      exact List.mem_map.mpr ⟨laterEdge, laterEdgeMembership, rfl⟩
    have returnSourceInReturn : returnEdge.source ∈ returnPath.vertices :=
      (returnPath.walk.endpoints_mem_visitedVertices
        returnEdgeMembership).1
    have targetSource : laterEdge.target = returnEdge.source := by
      calc
        laterEdge.target = returnEdge.reverse.target :=
          congrArg Graph.DirectedEdge.target reversed
        _ = returnEdge.source := Graph.DirectedEdge.reverse_target returnEdge
    have laterTargetInFirst : laterEdge.target ∈ first.path.vertices := by
      rw [targetSource]
      exact returnSubset returnEdge.source returnSourceInReturn
    have targetAtIntersection := uniqueIntersection laterEdge.target
      laterTargetInTail laterTargetInFirst
    have returnTargetInReturn : returnEdge.target ∈ returnPath.vertices :=
      (returnPath.walk.endpoints_mem_visitedVertices
        returnEdgeMembership).2
    have laterSourceInFirst : laterEdge.source ∈ first.path.vertices := by
      have sourceTarget : laterEdge.source = returnEdge.target := by
        calc
          laterEdge.source = returnEdge.reverse.source :=
            congrArg Graph.DirectedEdge.source reversed
          _ = returnEdge.target := Graph.DirectedEdge.reverse_source returnEdge
      rw [sourceTarget]
      exact returnSubset returnEdge.target returnTargetInReturn
    have laterSourceAtStart : laterEdge.source = later.path.start := by
      apply Classical.byContradiction
      intro notAtStart
      have laterSourceInTail : laterEdge.source ∈ later.path.vertices.tail := by
        have inVertices :=
          (later.path.walk.endpoints_mem_visitedVertices
            laterEdgeMembership).1
        simp only [Graph.EdgeWalk.visitedVertices, List.mem_cons] at inVertices
        exact inVertices.resolve_left notAtStart
      have sourceAtIntersection := uniqueIntersection laterEdge.source
        laterSourceInTail laterSourceInFirst
      apply later.path.directed_source_ne_target laterEdgeMembership
      exact sourceAtIntersection.trans targetAtIntersection.symm
    have returnNonempty : returnPath.traversed ≠ [] := by
      intro empty
      simp [empty] at returnLast
    let returnEnd := returnPath.traversed.getLast returnNonempty
    have returnEndMembership : returnEnd ∈ returnPath.traversed :=
      List.getLast_mem returnNonempty
    have returnEndTarget : returnEnd.target = returnPath.finish :=
      returnPath.walk.getLast_target returnNonempty
    have returnEdgeTarget : returnEdge.target = returnPath.finish := by
      calc
        returnEdge.target = laterEdge.source := by
          symm
          calc
            laterEdge.source = returnEdge.reverse.source :=
              congrArg Graph.DirectedEdge.source reversed
            _ = returnEdge.target := Graph.DirectedEdge.reverse_source returnEdge
        _ = later.path.start := laterSourceAtStart
        _ = middle.target := later.startsAt
        _ = returnPath.finish := returnFinishes.symm
    have returnEdgeIsEnd : returnEdge = returnEnd :=
      returnPath.eq_of_target_eq returnEdgeMembership returnEndMembership
        (returnEdgeTarget.trans returnEndTarget.symm)
    have returnEndIsMiddle : returnEnd = middle :=
      List.getLast_of_getLast?_eq_some returnLast
    let headEdge := later.path.traversed.head later.nonempty
    have headMembership : headEdge ∈ later.path.traversed := by
      simp [headEdge]
    have headSource : headEdge.source = later.path.start := by
      cases traversalEquation : later.path.traversed with
      | nil => exact False.elim (later.nonempty traversalEquation)
      | cons firstEdge remaining =>
          have chain := later.path.walk.toChain
          rw [traversalEquation] at chain
          simpa [headEdge, traversalEquation] using chain.head_source
    have laterEdgeIsHead : laterEdge = headEdge :=
      later.path.eq_of_source_eq laterEdgeMembership headMembership
        (laterSourceAtStart.trans headSource.symm)
    apply later.head_index_ne_incoming
    calc
      (later.path.traversed.head later.nonempty).index = headEdge.index := rfl
      _ = laterEdge.index := congrArg Graph.DirectedEdge.index laterEdgeIsHead.symm
      _ = returnEdge.index := sameIndex
      _ = returnEnd.index := congrArg Graph.DirectedEdge.index returnEdgeIsEnd
      _ = middle.index := congrArg Graph.DirectedEdge.index returnEndIsMiddle

/-- A continuation truncated at its first return to a simple cycle cannot
reuse any stored edge occurrence of that cycle. The only endpoint cases that
vertex separation does not rule out are the two cusp edges at the departure
vertex; continuation initial-freedom rules those out exactly. -/
theorem firstIntersection_cycle_edgeDisjoint {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    (cycle : certificate.fullGraph.EdgeSimpleCycle)
    {middle partner last : certificate.fullGraph.DirectedEdge}
    (later : CuspFreeContinuation certificate middle last)
    (middleMembership : middle ∈ cycle.traversed)
    (partnerMembership : partner ∈ cycle.traversed)
    (meeting : middle.target = partner.source)
    (cusp : certificate.Cusp middle partner)
    (uniqueIntersection : ∀ vertex,
      vertex ∈ later.path.vertices.tail →
      vertex ∈ cycle.vertices → vertex = last.target) :
    ∀ index,
      index ∈ later.path.traversed.map Graph.DirectedEdge.index →
      index ∈ cycle.traversed.map Graph.DirectedEdge.index → False := by
  intro index inLaterIndices inCycleIndices
  rcases List.mem_map.mp inLaterIndices with
    ⟨laterEdge, laterMembership, laterIndex⟩
  rcases List.mem_map.mp inCycleIndices with
    ⟨cycleEdge, cycleMembership, cycleIndex⟩
  have sameIndex : laterEdge.index = cycleEdge.index :=
    laterIndex.trans cycleIndex.symm
  have laterTargetInTail : laterEdge.target ∈ later.path.vertices.tail := by
    change laterEdge.target ∈
      later.path.traversed.map Graph.DirectedEdge.target
    exact List.mem_map.mpr ⟨laterEdge, laterMembership, rfl⟩
  let headEdge := later.path.traversed.head later.nonempty
  have headMembership : headEdge ∈ later.path.traversed := by
    exact List.head_mem later.nonempty
  have headSource : headEdge.source = later.path.start := by
    cases traversalEquation : later.path.traversed with
    | nil => exact False.elim (later.nonempty traversalEquation)
    | cons head tail =>
        have chain := later.path.walk.toChain
        rw [traversalEquation] at chain
        simpa [headEdge, traversalEquation] using chain.head_source
  have edgeIsHead (atStart : laterEdge.source = later.path.start) :
      laterEdge = headEdge := by
    apply later.path.eq_of_source_eq laterMembership
      headMembership
    exact atStart.trans headSource.symm
  have sourceInTail (notStart : laterEdge.source ≠ later.path.start) :
      laterEdge.source ∈ later.path.vertices.tail := by
    have inVertices :=
      (later.path.walk.endpoints_mem_visitedVertices laterMembership).1
    simp only [Graph.EdgeWalk.visitedVertices, List.mem_cons] at inVertices
    exact inVertices.resolve_left notStart
  rcases Graph.DirectedEdge.eq_or_eq_reverse_of_index_eq
      laterEdge cycleEdge sameIndex with same | reversed
  · have cycleTargetInVertices :=
      (cycle.directed_endpoints_mem_vertices cycleMembership).2
    have targetAtHit := uniqueIntersection laterEdge.target
      laterTargetInTail (same ▸ cycleTargetInVertices)
    by_cases atStart : laterEdge.source = later.path.start
    · have laterIsHead := edgeIsHead atStart
      have cycleEdgeIsPartner : cycleEdge = partner := by
        apply cycle.eq_of_source_eq cycleMembership partnerMembership
        calc
          cycleEdge.source = laterEdge.source := by rw [same]
          _ = later.path.start := atStart
          _ = middle.target := later.startsAt
          _ = partner.source := meeting
      apply later.head_index_ne_cusp_partner structural meeting cusp
      calc
        (later.path.traversed.head later.nonempty).index = laterEdge.index :=
          congrArg Graph.DirectedEdge.index laterIsHead.symm
        _ = cycleEdge.index := sameIndex
        _ = partner.index :=
          congrArg Graph.DirectedEdge.index cycleEdgeIsPartner
    · have sourceAtHit := uniqueIntersection laterEdge.source
        (sourceInTail atStart)
        (same ▸ (cycle.directed_endpoints_mem_vertices cycleMembership).1)
      exact certificate.fullDirectedEdge_loopless structural laterEdge
        (sourceAtHit.trans targetAtHit.symm)
  · have targetSource : laterEdge.target = cycleEdge.source := by
      calc
        laterEdge.target = cycleEdge.reverse.target :=
          congrArg Graph.DirectedEdge.target reversed
        _ = cycleEdge.source := Graph.DirectedEdge.reverse_target cycleEdge
    have sourceTarget : laterEdge.source = cycleEdge.target := by
      calc
        laterEdge.source = cycleEdge.reverse.source :=
          congrArg Graph.DirectedEdge.source reversed
        _ = cycleEdge.target := Graph.DirectedEdge.reverse_source cycleEdge
    have targetAtHit := uniqueIntersection laterEdge.target
      laterTargetInTail (targetSource ▸
        (cycle.directed_endpoints_mem_vertices cycleMembership).1)
    by_cases atStart : laterEdge.source = later.path.start
    · have laterIsHead := edgeIsHead atStart
      have cycleEdgeIsMiddle : cycleEdge = middle := by
        apply cycle.eq_of_target_eq cycleMembership middleMembership
        calc
          cycleEdge.target = laterEdge.source := sourceTarget.symm
          _ = later.path.start := atStart
          _ = middle.target := later.startsAt
      apply later.head_index_ne_incoming
      calc
        (later.path.traversed.head later.nonempty).index = laterEdge.index :=
          congrArg Graph.DirectedEdge.index laterIsHead.symm
        _ = cycleEdge.index := sameIndex
        _ = middle.index :=
          congrArg Graph.DirectedEdge.index cycleEdgeIsMiddle
    · have sourceAtHit := uniqueIntersection laterEdge.source
        (sourceInTail atStart)
        (sourceTarget ▸
          (cycle.directed_endpoints_mem_vertices cycleMembership).2)
      exact certificate.fullDirectedEdge_loopless structural laterEdge
        (sourceAtHit.trans targetAtHit.symm)

/-- First-return vertex separation against an entire simple cycle is inherited
by every return path contained in that cycle. -/
theorem firstIntersection_cycle_vertexDisjoint {certificate : Certificate}
    (cycle : certificate.fullGraph.EdgeSimpleCycle)
    {middle last : certificate.fullGraph.DirectedEdge}
    (later : CuspFreeContinuation certificate middle last)
    (returnPath : certificate.fullGraph.EdgeSimplePath)
    (returnStarts : returnPath.start = last.target)
    (returnFinishes : returnPath.finish = later.path.start)
    (returnSubset : ∀ candidate, candidate ∈ returnPath.vertices →
      candidate ∈ cycle.vertices)
    (uniqueIntersection : ∀ vertex,
      vertex ∈ later.path.vertices.tail →
      vertex ∈ cycle.vertices → vertex = last.target)
    (returnNonempty : returnPath.traversed ≠ []) :
    ∀ vertex, vertex ∈ later.path.vertices →
      vertex ∈ returnPath.vertices.tail.dropLast → False := by
  intro vertex inLater inReturnInterior
  have inReturnTail : vertex ∈ returnPath.vertices.tail :=
    Graph.mem_of_mem_dropLast inReturnInterior
  have inReturn : vertex ∈ returnPath.vertices :=
    List.mem_of_mem_tail inReturnTail
  have inCycle := returnSubset vertex inReturn
  by_cases atLaterStart : vertex = later.path.start
  · apply returnPath.finish_not_mem_vertices_tail_dropLast returnNonempty
    rw [returnFinishes, ← atLaterStart]
    exact inReturnInterior
  · have inLaterTail : vertex ∈ later.path.vertices.tail := by
      change vertex ∈
        later.path.traversed.map Graph.DirectedEdge.target
      simp only [Graph.EdgeSimplePath.vertices,
        Graph.EdgeWalk.visitedVertices, List.mem_cons] at inLater
      exact inLater.resolve_left atLaterStart
    have atHit := uniqueIntersection vertex inLaterTail inCycle
    apply returnPath.start_not_mem_vertices_tail
    rw [returnStarts, ← atHit]
    exact inReturnTail

/-- Close a first-return continuation with any oppositely directed return
path contained in the original cycle. Exact edge containment is stated
separately because parallel stored edges cannot be recovered from vertices. -/
theorem firstIntersection_withCycle_cycle {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    (cycle : certificate.fullGraph.EdgeSimpleCycle)
    {middle partner last : certificate.fullGraph.DirectedEdge}
    (later : CuspFreeContinuation certificate middle last)
    (middleMembership : middle ∈ cycle.traversed)
    (partnerMembership : partner ∈ cycle.traversed)
    (meeting : middle.target = partner.source)
    (cusp : certificate.Cusp middle partner)
    (returnPath : certificate.fullGraph.EdgeSimplePath)
    (returnNonempty : returnPath.traversed ≠ [])
    (returnStarts : returnPath.start = last.target)
    (returnFinishes : returnPath.finish = later.path.start)
    (returnSubset : ∀ candidate, candidate ∈ returnPath.vertices →
      candidate ∈ cycle.vertices)
    (returnEdgeSubset : ∀ index,
      index ∈ returnPath.traversed.map Graph.DirectedEdge.index →
      index ∈ cycle.traversed.map Graph.DirectedEdge.index)
    (uniqueIntersection : ∀ vertex,
      vertex ∈ later.path.vertices.tail →
      vertex ∈ cycle.vertices → vertex = last.target) :
    ∃ closed : certificate.fullGraph.EdgeSimpleCycle,
      closed.start = later.path.start ∧
      closed.traversed = later.path.traversed ++ returnPath.traversed := by
  have vertexDisjoint := firstIntersection_cycle_vertexDisjoint cycle later
    returnPath returnStarts returnFinishes returnSubset uniqueIntersection
    returnNonempty
  have laterCycleEdgeDisjoint := firstIntersection_cycle_edgeDisjoint
    structural cycle later middleMembership partnerMembership meeting cusp
    uniqueIntersection
  have edgeDisjoint : ∀ index,
      index ∈ later.path.traversed.map Graph.DirectedEdge.index →
      index ∈ returnPath.traversed.map Graph.DirectedEdge.index → False := by
    intro index inLater inReturn
    exact laterCycleEdgeDisjoint index inLater
      (returnEdgeSubset index inReturn)
  have pathsMeet : later.path.finish = returnPath.start :=
    later.endsAt.trans returnStarts.symm
  have pathsClose : returnPath.finish = later.path.start := returnFinishes
  let closed := Graph.EdgeSimpleCycle.ofTwoPaths later.path returnPath
    later.nonempty returnNonempty pathsMeet pathsClose vertexDisjoint edgeDisjoint
  exact ⟨closed, rfl, rfl⟩

/-- In the oriented bungee configuration, a first-return continuation and the
reverse of the old complementary arc form an exact simple cycle. The returned
arc wraps through the old cycle base, which is what later permits a same-base
minimality comparison. -/
theorem bungee_firstIntersection_cycle {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    (cycle : certificate.fullGraph.EdgeSimpleCycle)
    {before between after : List certificate.fullGraph.DirectedEdge}
    {outgoingAtHit middle partner last :
      certificate.fullGraph.DirectedEdge}
    (cycleSteps : cycle.traversed =
      before ++ outgoingAtHit :: between ++ middle :: partner :: after)
    (cusp : certificate.Cusp middle partner)
    (later : CuspFreeContinuation certificate middle last)
    (hit : last.target = outgoingAtHit.source)
    (uniqueIntersection : ∀ vertex,
      vertex ∈ later.path.vertices.tail →
      vertex ∈ cycle.vertices → vertex = last.target) :
    ∃ (returnPath : certificate.fullGraph.EdgeSimplePath)
      (closed : certificate.fullGraph.EdgeSimpleCycle),
      returnPath.start = last.target ∧
      returnPath.finish = later.path.start ∧
      returnPath.traversed = Graph.EdgeWalk.reverseTraversal
        ((partner :: after) ++ before) ∧
      cycle.start ∈ returnPath.vertices ∧
      cycle.start ≠ returnPath.finish ∧
      closed.start = later.path.start ∧
      closed.traversed = later.path.traversed ++ returnPath.traversed := by
  have middleMembership : middle ∈ cycle.traversed := by
    rw [cycleSteps]
    simp
  have partnerMembership : partner ∈ cycle.traversed := by
    rw [cycleSteps]
    simp
  have cuspMeeting : middle.target = partner.source := by
    have fullChain := cycle.walk.toChain
    rw [cycleSteps] at fullChain
    have regrouped : certificate.fullGraph.EdgeChain cycle.start
        ((before ++ outgoingAtHit :: between) ++
          middle :: partner :: after) cycle.start := by
      simpa [List.append_assoc] using fullChain
    rcases regrouped.split_append with
      ⟨splitVertex, _prefixChain, suffixChain⟩
    cases suffixChain with
    | cons _middle middleStarts middleTail =>
        cases middleTail with
        | cons _partner partnerStarts partnerTail =>
            exact partnerStarts.symm
  rcases cycle.complementPath cycleSteps with
    ⟨complement, complementStarts, complementFinishes, complementSteps,
      baseInComplementTail, complementVertexSubset, complementEdgeSubset⟩
  let returnPath := complement.reverse
  have returnNonempty : returnPath.traversed ≠ [] := by
    simp [returnPath, Graph.EdgeSimplePath.reverse,
      Graph.EdgeWalk.reverseTraversal, complementSteps]
  have returnStarts : returnPath.start = last.target := by
    change complement.finish = last.target
    exact complementFinishes.trans hit.symm
  have returnFinishes : returnPath.finish = later.path.start := by
    change complement.start = later.path.start
    exact complementStarts.trans
      (cuspMeeting.symm.trans later.startsAt.symm)
  have baseInReturn : cycle.start ∈ returnPath.vertices := by
    have baseInComplement : cycle.start ∈ complement.vertices :=
      List.mem_of_mem_tail baseInComplementTail
    simpa [returnPath] using baseInComplement
  have baseNeReturnFinish : cycle.start ≠ returnPath.finish := by
    change cycle.start ≠ complement.start
    intro same
    apply complement.start_not_mem_vertices_tail
    rw [← same]
    exact baseInComplementTail
  have returnVertexSubset : ∀ candidate,
      candidate ∈ returnPath.vertices → candidate ∈ cycle.vertices := by
    intro candidate membership
    apply complementVertexSubset candidate
    simpa [returnPath] using membership
  have returnEdgeSubset : ∀ index,
      index ∈ returnPath.traversed.map Graph.DirectedEdge.index →
      index ∈ cycle.traversed.map Graph.DirectedEdge.index := by
    intro index membership
    apply complementEdgeSubset index
    simpa [returnPath, Graph.EdgeSimplePath.reverse,
      Graph.EdgeWalk.reverseTraversal, List.map_map, Function.comp_def] using
      membership
  rcases firstIntersection_withCycle_cycle structural cycle later
      middleMembership partnerMembership cuspMeeting cusp returnPath
      returnNonempty returnStarts returnFinishes returnVertexSubset
      returnEdgeSubset uniqueIntersection with
    ⟨closed, closedStarts, closedSteps⟩
  refine ⟨returnPath, closed, returnStarts, returnFinishes, ?_, baseInReturn,
    baseNeReturnFinish, closedStarts, closedSteps⟩
  change Graph.EdgeWalk.reverseTraversal complement.traversed = _
  rw [complementSteps]

/-- If a closed splice contains the old base inside its return path, rotate
the splice back to that base while exposing the exact list decomposition.
The cyclic cusp count is preserved independently of the chosen base. -/
theorem rotate_spliced_cycle_to_return_vertex {certificate : Certificate}
    {middle last : certificate.fullGraph.DirectedEdge}
    (later : CuspFreeContinuation certificate middle last)
    (returnPath : certificate.fullGraph.EdgeSimplePath)
    (closed : certificate.fullGraph.EdgeSimpleCycle)
    (closedSteps : closed.traversed =
      later.path.traversed ++ returnPath.traversed)
    (vertex : Vertex) (inReturn : vertex ∈ returnPath.vertices)
    (notReturnFinish : vertex ≠ returnPath.finish) :
    ∃ (based : certificate.fullGraph.EdgeSimpleCycle)
      (returnBefore : List certificate.fullGraph.DirectedEdge)
      (baseEdge : certificate.fullGraph.DirectedEdge)
      (returnAfter : List certificate.fullGraph.DirectedEdge),
      returnPath.traversed = returnBefore ++ baseEdge :: returnAfter ∧
      baseEdge.source = vertex ∧
      closed.traversed =
        (later.path.traversed ++ returnBefore) ++ baseEdge :: returnAfter ∧
      based.start = vertex ∧
      based.traversed =
        (baseEdge :: returnAfter) ++
          (later.path.traversed ++ returnBefore) ∧
      certificate.cyclicCuspCount based.traversed =
        certificate.cyclicCuspCount closed.traversed := by
  rcases returnPath.outgoingAtVertex inReturn notReturnFinish with
    ⟨returnBefore, baseEdge, returnAfter, returnSteps, baseSource⟩
  have closedDecomposition : closed.traversed =
      (later.path.traversed ++ returnBefore) ++ baseEdge :: returnAfter := by
    rw [closedSteps, returnSteps]
    simp [List.append_assoc]
  rcases closed.rotateAt_exists closedDecomposition with
    ⟨based, basedStarts, basedSteps⟩
  refine ⟨based, returnBefore, baseEdge, returnAfter, returnSteps,
    baseSource, closedDecomposition, basedStarts.trans baseSource, basedSteps,
    ?_⟩
  rw [basedSteps, closedDecomposition]
  exact (certificate.cyclicCuspCount_append_comm
    (later.path.traversed ++ returnBefore)
    (baseEdge :: returnAfter)).symm

/-- The oriented first-return bungee splice can therefore be represented by a
simple cycle at the original cycle base, without changing its cyclic cusp
count. This is the exact same-base object required by minimality. -/
theorem bungee_firstIntersection_sameBaseCycle {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    (cycle : certificate.fullGraph.EdgeSimpleCycle)
    {before between after : List certificate.fullGraph.DirectedEdge}
    {outgoingAtHit middle partner last :
      certificate.fullGraph.DirectedEdge}
    (cycleSteps : cycle.traversed =
      before ++ outgoingAtHit :: between ++ middle :: partner :: after)
    (cusp : certificate.Cusp middle partner)
    (later : CuspFreeContinuation certificate middle last)
    (hit : last.target = outgoingAtHit.source)
    (uniqueIntersection : ∀ vertex,
      vertex ∈ later.path.vertices.tail →
      vertex ∈ cycle.vertices → vertex = last.target) :
    ∃ (returnPath : certificate.fullGraph.EdgeSimplePath)
      (closed based : certificate.fullGraph.EdgeSimpleCycle)
      (returnBefore : List certificate.fullGraph.DirectedEdge)
      (baseEdge : certificate.fullGraph.DirectedEdge)
      (returnAfter : List certificate.fullGraph.DirectedEdge),
      returnPath.traversed = Graph.EdgeWalk.reverseTraversal
        ((partner :: after) ++ before) ∧
      closed.start = later.path.start ∧
      closed.traversed = later.path.traversed ++ returnPath.traversed ∧
      returnPath.traversed = returnBefore ++ baseEdge :: returnAfter ∧
      baseEdge.source = cycle.start ∧
      based.start = cycle.start ∧
      based.traversed =
        (baseEdge :: returnAfter) ++
          (later.path.traversed ++ returnBefore) ∧
      certificate.cyclicCuspCount based.traversed =
        certificate.cyclicCuspCount closed.traversed := by
  rcases bungee_firstIntersection_cycle structural cycle cycleSteps cusp later
      hit uniqueIntersection with
    ⟨returnPath, closed, _returnStarts, _returnFinishes, returnSteps,
      baseInReturn, baseNeReturnFinish, closedStarts, closedSteps⟩
  rcases rotate_spliced_cycle_to_return_vertex later returnPath closed
      closedSteps cycle.start baseInReturn baseNeReturnFinish with
    ⟨based, returnBefore, baseEdge, returnAfter, returnDecomposition,
      baseSource, _closedDecomposition, basedStarts, basedSteps, cyclicCount⟩
  exact ⟨returnPath, closed, based, returnBefore, baseEdge, returnAfter,
    returnSteps, closedStarts, closedSteps, returnDecomposition, baseSource,
    basedStarts, basedSteps, cyclicCount⟩

/-- The same-base splice has a canonical traversal formula: reverse the old
arc after the selected cusp, follow the new continuation, then reverse the old
prefix before the hit. This removes the existential rotation cut from the
subsequent closing-cusp arithmetic. -/
theorem bungee_firstIntersection_exactSameBaseCycle
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    (cycle : certificate.fullGraph.EdgeSimpleCycle)
    {before between after : List certificate.fullGraph.DirectedEdge}
    {outgoingAtHit middle partner last :
      certificate.fullGraph.DirectedEdge}
    (cycleSteps : cycle.traversed =
      before ++ outgoingAtHit :: between ++ middle :: partner :: after)
    (cusp : certificate.Cusp middle partner)
    (later : CuspFreeContinuation certificate middle last)
    (hit : last.target = outgoingAtHit.source)
    (uniqueIntersection : ∀ vertex,
      vertex ∈ later.path.vertices.tail →
      vertex ∈ cycle.vertices → vertex = last.target) :
    ∃ based : certificate.fullGraph.EdgeSimpleCycle,
      based.start = cycle.start ∧
      based.traversed =
        Graph.EdgeWalk.reverseTraversal (partner :: after) ++
          later.path.traversed ++
          Graph.EdgeWalk.reverseTraversal before := by
  rcases bungee_firstIntersection_cycle structural cycle cycleSteps cusp later
      hit uniqueIntersection with
    ⟨returnPath, closed, returnStarts, _returnFinishes, returnSteps,
      _baseInReturn, _baseNeReturnFinish, _closedStarts, closedSteps⟩
  let baseArc := Graph.EdgeWalk.reverseTraversal (partner :: after)
  have baseArcNonempty : baseArc ≠ [] := by
    simp [baseArc, Graph.EdgeWalk.reverseTraversal]
  have returnDecomposition : returnPath.traversed =
      Graph.EdgeWalk.reverseTraversal before ++ baseArc := by
    rw [returnSteps]
    simp [baseArc, Graph.EdgeWalk.reverseTraversal, List.map_append,
      List.append_assoc]
  cases baseArcEquation : baseArc with
  | nil => exact False.elim (baseArcNonempty baseArcEquation)
  | cons baseEdge baseAfter =>
      have cyclePrefixEquation : cycle.traversed =
          before ++ outgoingAtHit ::
            (between ++ middle :: partner :: after) := by
        simpa [List.append_assoc] using cycleSteps
      rcases cycle.prefixBefore cyclePrefixEquation with
        ⟨prefixPath, prefixStarts, prefixFinishes, prefixSteps,
          _prefixSubset⟩
      have returnChain := returnPath.walk.toChain
      rw [returnDecomposition, baseArcEquation] at returnChain
      rcases returnChain.split_append with
        ⟨splitVertex, returnPrefixChain, returnSuffixChain⟩
      have reversedPrefixChain : certificate.fullGraph.EdgeChain
          returnPath.start (Graph.EdgeWalk.reverseTraversal before)
            cycle.start := by
        have chain := prefixPath.reverse.walk.toChain
        change certificate.fullGraph.EdgeChain prefixPath.finish
          (Graph.EdgeWalk.reverseTraversal prefixPath.traversed)
            prefixPath.start at chain
        rw [prefixSteps, prefixFinishes, prefixStarts, ← hit,
          ← returnStarts] at chain
        exact chain
      have splitIsBase : splitVertex = cycle.start :=
        returnPrefixChain.finish_unique reversedPrefixChain
      have baseEdgeSource : baseEdge.source = cycle.start := by
        cases returnSuffixChain with
        | cons _edge edgeStarts edgeTail =>
            exact edgeStarts.trans splitIsBase
      have closedDecomposition : closed.traversed =
          (later.path.traversed ++
            Graph.EdgeWalk.reverseTraversal before) ++
              baseEdge :: baseAfter := by
        rw [closedSteps, returnDecomposition, baseArcEquation]
        simp [List.append_assoc]
      rcases closed.rotateAt_exists closedDecomposition with
        ⟨based, basedStarts, basedSteps⟩
      refine ⟨based, basedStarts.trans baseEdgeSource, ?_⟩
      rw [basedSteps, ← baseArcEquation]
      simp [baseArc, List.append_assoc]

/-- Symmetric exact same-base splice when the first cycle hit lies after the
selected cusp. The old post-cusp segment is replaced by the later path while
the old base prefix and suffix remain in their original orientation. -/
theorem bungee_afterCusp_exactSameBaseCycle
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    (cycle : certificate.fullGraph.EdgeSimpleCycle)
    {initial between suffix : List certificate.fullGraph.DirectedEdge}
    {middle partner outgoingAtHit last :
      certificate.fullGraph.DirectedEdge}
    (cycleSteps : cycle.traversed =
      initial ++ middle :: partner :: between ++ outgoingAtHit :: suffix)
    (cusp : certificate.Cusp middle partner)
    (later : CuspFreeContinuation certificate middle last)
    (hit : last.target = outgoingAtHit.source)
    (uniqueIntersection : ∀ vertex,
      vertex ∈ later.path.vertices.tail →
      vertex ∈ cycle.vertices → vertex = last.target) :
    ∃ based : certificate.fullGraph.EdgeSimpleCycle,
      based.start = cycle.start ∧
      based.traversed =
        (initial ++ [middle]) ++ later.path.traversed ++
          (outgoingAtHit :: suffix) := by
  rcases cycle.wrapPathAfterCusp cycleSteps with
    ⟨returnPath, returnStartsAtHit, returnFinishesAtCusp, returnSteps,
      returnVertexSubset, returnEdgeSubset⟩
  have returnNonempty : returnPath.traversed ≠ [] := by
    simp [returnSteps]
  have returnStarts : returnPath.start = last.target :=
    returnStartsAtHit.trans hit.symm
  have returnFinishes : returnPath.finish = later.path.start :=
    returnFinishesAtCusp.trans later.startsAt.symm
  have middleMembership : middle ∈ cycle.traversed := by
    rw [cycleSteps]
    simp
  have partnerMembership : partner ∈ cycle.traversed := by
    rw [cycleSteps]
    simp
  have cuspMeeting : middle.target = partner.source := by
    have fullChain := cycle.walk.toChain
    rw [cycleSteps] at fullChain
    have regrouped : certificate.fullGraph.EdgeChain cycle.start
        (initial ++ (middle :: partner :: between ++
          outgoingAtHit :: suffix)) cycle.start := by
      simpa [List.append_assoc] using fullChain
    rcases regrouped.split_append with
      ⟨splitVertex, _initialChain, suffixChain⟩
    cases suffixChain with
    | cons _middle middleStarts middleTail =>
        cases middleTail with
        | cons _partner partnerStarts partnerTail =>
            exact partnerStarts.symm
  rcases firstIntersection_withCycle_cycle structural cycle later
      middleMembership partnerMembership cuspMeeting cusp returnPath
      returnNonempty returnStarts returnFinishes returnVertexSubset
      returnEdgeSubset uniqueIntersection with
    ⟨closed, _closedStarts, closedSteps⟩
  let baseArc := initial ++ [middle]
  have baseArcNonempty : baseArc ≠ [] := by simp [baseArc]
  have returnDecomposition : returnPath.traversed =
      (outgoingAtHit :: suffix) ++ baseArc := by
    rw [returnSteps]
    simp [baseArc, List.append_assoc]
  cases baseArcEquation : baseArc with
  | nil => exact False.elim (baseArcNonempty baseArcEquation)
  | cons baseEdge baseAfter =>
      have cyclePrefixEquation : cycle.traversed =
          initial ++ middle :: partner ::
            (between ++ outgoingAtHit :: suffix) := by
        simpa [List.append_assoc] using cycleSteps
      rcases cycle.prefixPath cyclePrefixEquation with
        ⟨prefixPath, prefixStarts, _prefixFinishes, prefixSteps⟩
      have prefixChain := prefixPath.walk.toChain
      rw [prefixSteps] at prefixChain
      change certificate.fullGraph.EdgeChain prefixPath.start baseArc
        prefixPath.finish at prefixChain
      rw [baseArcEquation] at prefixChain
      have baseEdgeSource : baseEdge.source = cycle.start :=
        prefixChain.head_source.trans prefixStarts
      have closedDecomposition : closed.traversed =
          (later.path.traversed ++ (outgoingAtHit :: suffix)) ++
            baseEdge :: baseAfter := by
        rw [closedSteps, returnDecomposition, baseArcEquation]
        simp [List.append_assoc]
      rcases closed.rotateAt_exists closedDecomposition with
        ⟨based, basedStarts, basedSteps⟩
      refine ⟨based, basedStarts.trans baseEdgeSource, ?_⟩
      rw [basedSteps, ← baseArcEquation]
      simp [baseArc, List.append_assoc]

/-- The normalized later prefix and return suffix form a genuine exact-edge
simple cycle. This is the closed graph object on which the remaining bungee
cusp-count contradiction is carried out. -/
theorem firstIntersection_cycle {certificate : Certificate}
    {incoming middle last : certificate.fullGraph.DirectedEdge}
    (first : CuspFreeContinuation certificate incoming middle)
    (later : CuspFreeContinuation certificate middle last)
    (returnPath : certificate.fullGraph.EdgeSimplePath)
    (returnStarts : returnPath.start = last.target)
    (returnFinishes : returnPath.finish = middle.target)
    (returnSubset : ∀ candidate, candidate ∈ returnPath.vertices →
      candidate ∈ first.path.vertices)
    (uniqueIntersection : ∀ vertex,
      vertex ∈ later.path.vertices.tail →
      vertex ∈ first.path.vertices → vertex = last.target)
    (returnLast : returnPath.traversed.getLast? = some middle) :
    ∃ cycle : certificate.fullGraph.EdgeSimpleCycle,
      cycle.traversed = later.path.traversed ++ returnPath.traversed := by
  have returnNonempty : returnPath.traversed ≠ [] := by
    intro empty
    simp [empty] at returnLast
  have meeting : later.path.finish = returnPath.start :=
    later.endsAt.trans returnStarts.symm
  have closing : returnPath.finish = later.path.start :=
    returnFinishes.trans later.startsAt.symm
  have vertexDisjoint := firstIntersection_vertexDisjoint first later
    returnPath returnStarts returnFinishes returnSubset uniqueIntersection
    returnNonempty
  have edgeDisjoint := firstIntersection_edgeDisjoint first later returnPath
    returnStarts returnFinishes returnSubset uniqueIntersection returnLast
  let cycle := Graph.EdgeSimpleCycle.ofTwoPaths later.path returnPath
    later.nonempty returnNonempty meeting closing vertexDisjoint edgeDisjoint
  exact ⟨cycle, rfl⟩

end CuspFreeContinuation

/-- The strengthened continuation used as the strict generalized-Yeo order:
every later continuation from `outgoing` is vertex-disjoint from this path,
apart from its removed initial vertex. -/
structure OrderingPath (certificate : Certificate)
    (incoming outgoing : certificate.fullGraph.DirectedEdge)
    extends CuspFreeContinuation certificate incoming outgoing where
  separated : ∀ {later : certificate.fullGraph.DirectedEdge},
    (continuation : CuspFreeContinuation certificate outgoing later) →
      ∀ vertex, vertex ∈ path.vertices →
        vertex ∈ continuation.path.vertices.tail → False

namespace OrderingPath

/-- The separation clause makes ordering paths composable: it supplies the
exact disjointness needed for the simple-path append, and remains stable
against every later continuation. -/
def append {certificate : Certificate}
    {incoming middle outgoing : certificate.fullGraph.DirectedEdge}
    (first : OrderingPath certificate incoming middle)
    (second : OrderingPath certificate middle outgoing) :
    OrderingPath certificate incoming outgoing := by
  have firstSecondDisjoint : ∀ vertex,
      vertex ∈ first.path.vertices →
        vertex ∈ second.path.vertices.tail → False :=
    first.separated second.toCuspFreeContinuation
  let combined := first.toCuspFreeContinuation.append
    second.toCuspFreeContinuation firstSecondDisjoint
  refine
    { combined with
      separated := ?_ }
  intro later continuation vertex combinedMembership laterMembership
  have secondLaterDisjoint : ∀ candidate,
      candidate ∈ second.path.vertices →
        candidate ∈ continuation.path.vertices.tail → False :=
    second.separated continuation
  let extended := second.toCuspFreeContinuation.append continuation
    secondLaterDisjoint
  have firstExtendedDisjoint : ∀ candidate,
      candidate ∈ first.path.vertices →
        candidate ∈ extended.path.vertices.tail → False :=
    first.separated extended
  have combinedVertices : combined.path.vertices =
      first.path.vertices ++ second.path.vertices.tail := by
    exact CuspFreeContinuation.append_path_vertices _ _ _
  rw [combinedVertices, List.mem_append] at combinedMembership
  rcases combinedMembership with inFirst | inSecond
  · apply firstExtendedDisjoint vertex inFirst
    have extendedVertices : extended.path.vertices =
        second.path.vertices ++ continuation.path.vertices.tail := by
      exact CuspFreeContinuation.append_path_vertices _ _ _
    rw [extendedVertices]
    have laterTargetMembership : vertex ∈
        continuation.path.traversed.map Graph.DirectedEdge.target := by
      simpa [Graph.EdgeSimplePath.vertices,
        Graph.EdgeWalk.visitedVertices] using laterMembership
    change vertex ∈
      second.path.traversed.map Graph.DirectedEdge.target ++
        continuation.path.traversed.map Graph.DirectedEdge.target
    exact List.mem_append.mpr (.inr laterTargetMembership)
  · exact secondLaterDisjoint vertex (List.mem_of_mem_tail inSecond)
      laterMembership

end OrderingPath

/-- Existential strict ordering on directed edge occurrences. -/
def EdgeOrdering (certificate : Certificate)
    (incoming outgoing : certificate.fullGraph.DirectedEdge) : Prop :=
  Nonempty (OrderingPath certificate incoming outgoing)

theorem EdgeOrdering.irrefl (certificate : Certificate)
    (directed : certificate.fullGraph.DirectedEdge) :
    ¬certificate.EdgeOrdering directed directed := by
  rintro ⟨ordering⟩
  have endpointEquation : ordering.path.start = ordering.path.finish :=
    ordering.startsAt.trans ordering.endsAt.symm
  exact ordering.path.start_ne_finish_of_nonempty ordering.nonempty
    endpointEquation

theorem EdgeOrdering.transitive (certificate : Certificate)
    {first middle last : certificate.fullGraph.DirectedEdge}
    (firstBeforeMiddle : certificate.EdgeOrdering first middle)
    (middleBeforeLast : certificate.EdgeOrdering middle last) :
    certificate.EdgeOrdering first last := by
  rcases firstBeforeMiddle with ⟨firstOrdering⟩
  rcases middleBeforeLast with ⟨secondOrdering⟩
  exact ⟨firstOrdering.append secondOrdering⟩

/-- Every nonempty duplicate-free finite list has a maximal member for an
irreflexive transitive relation. The proof minimizes the number of successors;
any strict successor would have a strictly smaller successor set. -/
theorem exists_relation_maximal {α : Type} (values : List α)
    (valuesNodup : values.Nodup) (nonempty : values ≠ [])
    (relation : α → α → Prop)
    (irrefl : ∀ value, ¬relation value value)
    (transitive : ∀ {first middle last},
      relation first middle → relation middle last → relation first last) :
    ∃ maximal ∈ values,
      ∀ candidate ∈ values, ¬relation maximal candidate := by
  classical
  let successors : α → List α := fun value =>
    values.filter fun candidate => decide (relation value candidate)
  cases values with
  | nil => exact False.elim (nonempty rfl)
  | cons head tail =>
      rcases exists_minimal_measure head tail
          (fun value => (successors value).length) with
        ⟨maximal, maximalMembership, minimal⟩
      refine ⟨maximal, maximalMembership, ?_⟩
      intro candidate candidateMembership maximalBeforeCandidate
      have candidateInMaximalSuccessors :
          candidate ∈ successors maximal := by
        simp [successors, candidateMembership, maximalBeforeCandidate]
      have candidateNotInOwnSuccessors :
          candidate ∉ successors candidate := by
        simp [successors, irrefl candidate]
      have successorSubset : ∀ value ∈ successors candidate,
          value ∈ successors maximal := by
        intro value membership
        have filtered := List.mem_filter.mp membership
        have candidateBeforeValue : relation candidate value :=
          of_decide_eq_true filtered.2
        have maximalBeforeValue :=
          transitive maximalBeforeCandidate candidateBeforeValue
        exact List.mem_filter.mpr
          ⟨filtered.1, by simpa using maximalBeforeValue⟩
      have enlargedNodup :
          (candidate :: successors candidate).Nodup := by
        exact List.nodup_cons.mpr
          ⟨candidateNotInOwnSuccessors, valuesNodup.filter _⟩
      have enlargedSubset : ∀ value ∈ candidate :: successors candidate,
          value ∈ successors maximal := by
        intro value membership
        rcases List.mem_cons.mp membership with rfl | tailMembership
        · exact candidateInMaximalSuccessors
        · exact successorSubset value tailMembership
      have strictBound := length_le_of_nodup_subset'
        enlargedNodup enlargedSubset
      have minimalBound := minimal candidate candidateMembership
      simp only [List.length_cons] at strictBound
      omega

/-- Core's executable duplicate removal is duplicate-free for every lawful
Boolean equality. -/
theorem eraseDups_nodup_generic {α : Type} [BEq α] [LawfulBEq α]
    (values : List α) : values.eraseDups.Nodup := by
  match values with
  | [] => simp
  | head :: tail =>
      rw [List.eraseDups_cons, List.nodup_cons]
      exact ⟨by simp, eraseDups_nodup_generic
        (tail.filter fun value => !value == head)⟩
termination_by values.length
decreasing_by
  exact Nat.lt_succ_of_le (List.length_filter_le _ _)

/-- A simple closed traversal is cusp-free when neither an internal adjacent
pair nor the last/first closing pair forms a cusp. -/
def CuspFreeCycle (certificate : Certificate)
    (cycle : certificate.fullGraph.EdgeSimpleCycle) : Prop :=
  certificate.CuspFreeTraversal cycle.traversed ∧
    match cycle.traversed with
    | [] => False
    | first :: rest =>
        ¬certificate.Cusp ((first :: rest).getLast (by simp)) first

/-- The transition from the last traversal edge back to the first. -/
def ClosingCusp (certificate : Certificate)
    (cycle : certificate.fullGraph.EdgeSimpleCycle) : Prop :=
  certificate.Cusp (cycle.traversed.getLast cycle.nonempty)
    (cycle.traversed.head cycle.nonempty)

/-- Rotating the chosen base occurrence of a simple cycle preserves its
cyclic cusp count. -/
theorem cyclicCuspCount_rotateAt (certificate : Certificate)
    (cycle rotated : certificate.fullGraph.EdgeSimpleCycle)
    {before after : List certificate.fullGraph.DirectedEdge}
    {first : certificate.fullGraph.DirectedEdge}
    (cycleSteps : cycle.traversed = before ++ first :: after)
    (rotatedSteps : rotated.traversed = (first :: after) ++ before) :
    certificate.cyclicCuspCount rotated.traversed =
      certificate.cyclicCuspCount cycle.traversed := by
  rw [rotatedSteps, cycleSteps]
  exact (certificate.cyclicCuspCount_append_comm
    before (first :: after)).symm

/-- If the closing transition is free at both selected bases, rotation also
preserves the internal cusp count used by the minimal-cycle argument. -/
theorem cuspCount_rotateAt_of_closing_free (certificate : Certificate)
    (cycle rotated : certificate.fullGraph.EdgeSimpleCycle)
    {before after : List certificate.fullGraph.DirectedEdge}
    {first : certificate.fullGraph.DirectedEdge}
    (cycleSteps : cycle.traversed = before ++ first :: after)
    (rotatedSteps : rotated.traversed = (first :: after) ++ before)
    (cycleClosingFree : ¬certificate.ClosingCusp cycle)
    (rotatedClosingFree : ¬certificate.ClosingCusp rotated) :
    certificate.cuspCount rotated.traversed =
      certificate.cuspCount cycle.traversed := by
  have cyclicInvariant := certificate.cyclicCuspCount_rotateAt cycle rotated
    cycleSteps rotatedSteps
  have cycleBoundaryZero := certificate.cuspBoundaryCount_eq_zero
    cycle.nonempty cycle.nonempty cycleClosingFree
  have rotatedBoundaryZero := certificate.cuspBoundaryCount_eq_zero
    rotated.nonempty rotated.nonempty rotatedClosingFree
  unfold cyclicCuspCount at cyclicInvariant
  rw [cycleBoundaryZero, rotatedBoundaryZero] at cyclicInvariant
  omega

/-- The exact same-base bungee splice closes freely. When the hit precedes the
old base along a nonempty prefix, its closing pair is exactly the reversal of
the old cycle's closing pair. If the hit is the base itself, the explicitly
oriented endpoint boundary supplies the only additional case. -/
theorem bungee_exactSameBase_closingFree (certificate : Certificate)
    (cycle based : certificate.fullGraph.EdgeSimpleCycle)
    {before between after : List certificate.fullGraph.DirectedEdge}
    {outgoingAtHit middle partner last :
      certificate.fullGraph.DirectedEdge}
    (later : certificate.CuspFreeContinuation middle last)
    (cycleSteps : cycle.traversed =
      before ++ outgoingAtHit :: between ++ middle :: partner :: after)
    (basedSteps : based.traversed =
      Graph.EdgeWalk.reverseTraversal (partner :: after) ++
        later.path.traversed ++
        Graph.EdgeWalk.reverseTraversal before)
    (cycleClosingFree : ¬certificate.ClosingCusp cycle)
    (baseHitClosingFree : before = [] →
      ¬certificate.Cusp last
        ((partner :: after).getLast (by simp)).reverse) :
    ¬certificate.ClosingCusp based := by
  have suffixNonempty : partner :: after ≠ [] := by simp
  have reversedSuffixNonempty :
      Graph.EdgeWalk.reverseTraversal (partner :: after) ≠ [] := by
    simp [Graph.EdgeWalk.reverseTraversal]
  have reversedSuffixHeadOption :
      (Graph.EdgeWalk.reverseTraversal (partner :: after)).head? =
        some ((partner :: after).getLast suffixNonempty).reverse := by
    rw [List.head?_eq_some_head reversedSuffixNonempty,
      Graph.EdgeWalk.head_reverseTraversal]
  have basedHeadOption : based.traversed.head? =
      some ((partner :: after).getLast suffixNonempty).reverse := by
    rw [basedSteps, List.head?_append, List.head?_append,
      reversedSuffixHeadOption]
    rfl
  have basedHead : based.traversed.head based.nonempty =
      ((partner :: after).getLast suffixNonempty).reverse :=
    List.head_of_head?_eq_some basedHeadOption
  by_cases beforeEmpty : before = []
  · have basedLastOption : based.traversed.getLast? = some last := by
      rw [basedSteps, beforeEmpty]
      simp only [Graph.EdgeWalk.reverseTraversal, List.reverse_nil,
        List.map_nil, List.append_nil, List.getLast?_append]
      rw [List.getLast?_eq_some_getLast later.nonempty, later.lastEdge]
      simp
    have basedLast : based.traversed.getLast based.nonempty = last :=
      List.getLast_of_getLast?_eq_some basedLastOption
    intro closing
    unfold ClosingCusp at closing
    rw [basedLast, basedHead] at closing
    exact baseHitClosingFree beforeEmpty closing
  · have reversedBeforeNonempty :
        Graph.EdgeWalk.reverseTraversal before ≠ [] := by
      simpa [Graph.EdgeWalk.reverseTraversal] using beforeEmpty
    have reversedBeforeLastOption :
        (Graph.EdgeWalk.reverseTraversal before).getLast? =
          some (before.head beforeEmpty).reverse := by
      rw [List.getLast?_eq_some_getLast reversedBeforeNonempty,
        Graph.EdgeWalk.getLast_reverseTraversal]
    have basedLastOption : based.traversed.getLast? =
        some (before.head beforeEmpty).reverse := by
      rw [basedSteps, List.getLast?_append, reversedBeforeLastOption]
      rfl
    have basedLast : based.traversed.getLast based.nonempty =
        (before.head beforeEmpty).reverse :=
      List.getLast_of_getLast?_eq_some basedLastOption
    have cycleHeadOption : cycle.traversed.head? =
        some (before.head beforeEmpty) := by
      rw [cycleSteps, List.head?_append, List.head?_append,
        List.head?_eq_some_head beforeEmpty]
      simp
    have cycleHead : cycle.traversed.head cycle.nonempty =
        before.head beforeEmpty :=
      List.head_of_head?_eq_some cycleHeadOption
    have cycleLastOption : cycle.traversed.getLast? =
        some ((partner :: after).getLast suffixNonempty) := by
      have grouped : cycle.traversed =
          (before ++ outgoingAtHit :: between ++ [middle]) ++
            (partner :: after) := by
        simpa [List.append_assoc] using cycleSteps
      rw [grouped, List.getLast?_append,
        List.getLast?_eq_some_getLast suffixNonempty]
      simp
    have cycleLast : cycle.traversed.getLast cycle.nonempty =
        (partner :: after).getLast suffixNonempty :=
      List.getLast_of_getLast?_eq_some cycleLastOption
    intro closing
    apply cycleClosingFree
    unfold ClosingCusp at closing ⊢
    rw [basedLast, basedHead] at closing
    rw [cycleLast, cycleHead]
    exact (certificate.cusp_reverse_iff
      ((partner :: after).getLast suffixNonempty)
      (before.head beforeEmpty)).mpr closing

/-- The after-cusp replacement keeps the original base prefix and final
suffix, so its closing pair is literally the old cycle's closing pair. -/
theorem bungee_afterCusp_exactSameBase_closingFree
    (certificate : Certificate)
    (cycle based : certificate.fullGraph.EdgeSimpleCycle)
    {initial between suffix : List certificate.fullGraph.DirectedEdge}
    {middle partner outgoingAtHit last :
      certificate.fullGraph.DirectedEdge}
    (later : certificate.CuspFreeContinuation middle last)
    (cycleSteps : cycle.traversed =
      initial ++ middle :: partner :: between ++ outgoingAtHit :: suffix)
    (basedSteps : based.traversed =
      (initial ++ [middle]) ++ later.path.traversed ++
        (outgoingAtHit :: suffix))
    (cycleClosingFree : ¬certificate.ClosingCusp cycle) :
    ¬certificate.ClosingCusp based := by
  let baseArc := initial ++ [middle]
  let suffixArc := outgoingAtHit :: suffix
  have baseArcNonempty : baseArc ≠ [] := by simp [baseArc]
  have suffixArcNonempty : suffixArc ≠ [] := by simp [suffixArc]
  have cycleGrouped : cycle.traversed =
      (baseArc ++ (partner :: between)) ++ suffixArc := by
    simpa [baseArc, suffixArc, List.append_assoc] using cycleSteps
  have basedGrouped : based.traversed =
      (baseArc ++ later.path.traversed) ++ suffixArc := by
    simpa [baseArc, suffixArc, List.append_assoc] using basedSteps
  have cycleHeadOption : cycle.traversed.head? =
      some (baseArc.head baseArcNonempty) := by
    rw [cycleGrouped, List.head?_append, List.head?_append,
      List.head?_eq_some_head baseArcNonempty]
    rfl
  have basedHeadOption : based.traversed.head? =
      some (baseArc.head baseArcNonempty) := by
    rw [basedGrouped, List.head?_append, List.head?_append,
      List.head?_eq_some_head baseArcNonempty]
    rfl
  have cycleLastOption : cycle.traversed.getLast? =
      some (suffixArc.getLast suffixArcNonempty) := by
    rw [cycleGrouped, List.getLast?_append,
      List.getLast?_eq_some_getLast suffixArcNonempty]
    simp
  have basedLastOption : based.traversed.getLast? =
      some (suffixArc.getLast suffixArcNonempty) := by
    rw [basedGrouped, List.getLast?_append,
      List.getLast?_eq_some_getLast suffixArcNonempty]
    simp
  have cycleHead : cycle.traversed.head cycle.nonempty =
      baseArc.head baseArcNonempty :=
    List.head_of_head?_eq_some cycleHeadOption
  have basedHead : based.traversed.head based.nonempty =
      baseArc.head baseArcNonempty :=
    List.head_of_head?_eq_some basedHeadOption
  have cycleLast : cycle.traversed.getLast cycle.nonempty =
      suffixArc.getLast suffixArcNonempty :=
    List.getLast_of_getLast?_eq_some cycleLastOption
  have basedLast : based.traversed.getLast based.nonempty =
      suffixArc.getLast suffixArcNonempty :=
    List.getLast_of_getLast?_eq_some basedLastOption
  intro closing
  apply cycleClosingFree
  unfold ClosingCusp at closing ⊢
  rw [basedLast, basedHead] at closing
  rw [cycleLast, cycleHead]
  exact closing

/-- Package the exact same-base first-return splice together with the free
closing property required to invoke minimality of the original cycle. -/
theorem bungee_firstIntersection_nonclosingSameBase
    (certificate : Certificate)
    (structural : certificate.StructurallyWellFormed)
    (cycle : certificate.fullGraph.EdgeSimpleCycle)
    {before between after : List certificate.fullGraph.DirectedEdge}
    {outgoingAtHit middle partner last :
      certificate.fullGraph.DirectedEdge}
    (cycleSteps : cycle.traversed =
      before ++ outgoingAtHit :: between ++ middle :: partner :: after)
    (cusp : certificate.Cusp middle partner)
    (later : certificate.CuspFreeContinuation middle last)
    (hit : last.target = outgoingAtHit.source)
    (uniqueIntersection : ∀ vertex,
      vertex ∈ later.path.vertices.tail →
      vertex ∈ cycle.vertices → vertex = last.target)
    (cycleClosingFree : ¬certificate.ClosingCusp cycle)
    (baseHitClosingFree : before = [] →
      ¬certificate.Cusp last
        ((partner :: after).getLast (by simp)).reverse) :
    ∃ based : certificate.fullGraph.EdgeSimpleCycle,
      based.start = cycle.start ∧
      ¬certificate.ClosingCusp based ∧
      based.traversed =
        Graph.EdgeWalk.reverseTraversal (partner :: after) ++
          later.path.traversed ++
          Graph.EdgeWalk.reverseTraversal before := by
  rcases CuspFreeContinuation.bungee_firstIntersection_exactSameBaseCycle
      structural cycle cycleSteps cusp later hit uniqueIntersection with
    ⟨based, basedStarts, basedSteps⟩
  have basedClosingFree := certificate.bungee_exactSameBase_closingFree
    cycle based later cycleSteps basedSteps cycleClosingFree baseHitClosingFree
  exact ⟨based, basedStarts, basedClosingFree, basedSteps⟩

/-- Numeric core of the bungee minimality comparison. The removed arc has no
internal cusps, its old incoming boundary is free, and the replacement uses
its unique available cusp at the later-path exit boundary. -/
theorem bungee_minimal_count_constraints (certificate : Certificate)
    (cycle based : certificate.fullGraph.EdgeSimpleCycle)
    {before between after : List certificate.fullGraph.DirectedEdge}
    {outgoingAtHit middle partner last :
      certificate.fullGraph.DirectedEdge}
    (later : certificate.CuspFreeContinuation middle last)
    (cycleSteps : cycle.traversed =
      before ++ outgoingAtHit :: between ++ middle :: partner :: after)
    (basedSteps : based.traversed =
      Graph.EdgeWalk.reverseTraversal (partner :: after) ++
        later.path.traversed ++
        Graph.EdgeWalk.reverseTraversal before)
    (cusp : certificate.Cusp middle partner)
    (minimal : certificate.cuspCount cycle.traversed ≤
      certificate.cuspCount based.traversed) :
    certificate.CuspFreeTraversal
        ((outgoingAtHit :: between) ++ [middle]) ∧
      certificate.cuspBoundaryCount before
        ((outgoingAtHit :: between) ++ [middle]) = 0 ∧
      certificate.cuspBoundaryCount
        (Graph.EdgeWalk.reverseTraversal (partner :: after) ++
          later.path.traversed)
        (Graph.EdgeWalk.reverseTraversal before) = 1 := by
  let removed := (outgoingAtHit :: between) ++ [middle]
  let suffix := partner :: after
  let reversedSuffix := Graph.EdgeWalk.reverseTraversal suffix
  let reversedBefore := Graph.EdgeWalk.reverseTraversal before
  have removedNonempty : removed ≠ [] := by simp [removed]
  have suffixNonempty : suffix ≠ [] := by simp [suffix]
  have reversedSuffixNonempty : reversedSuffix ≠ [] := by
    simp [reversedSuffix, suffix, Graph.EdgeWalk.reverseTraversal]
  have originalEquation : cycle.traversed =
      (before ++ removed) ++ suffix := by
    simpa [removed, suffix, List.append_assoc] using cycleSteps
  have replacementEquation : based.traversed =
      (reversedSuffix ++ later.path.traversed) ++ reversedBefore := by
    simpa [reversedSuffix, reversedBefore, List.append_assoc] using basedSteps
  have removedTailNonempty : between ++ [middle] ≠ [] := by simp
  have removedTailLast :
      (between ++ [middle]).getLast removedTailNonempty = middle := by
    rw [List.getLast_append_of_ne_nil removedTailNonempty (by simp)]
    simp
  have removedLast : removed.getLast removedNonempty = middle := by
    change (outgoingAtHit :: (between ++ [middle])).getLast _ = middle
    rw [List.getLast_cons removedTailNonempty]
    exact removedTailLast
  have oldLeftLast :
      (before ++ removed).getLast (by simp [removed]) = middle := by
    rw [List.getLast_append_of_ne_nil (by simp [removed]) removedNonempty,
      removedLast]
  have oldBoundaryCusp : certificate.Cusp
      ((before ++ removed).getLast (by simp [removed]))
      (suffix.head suffixNonempty) := by
    rw [oldLeftLast]
    simpa [suffix] using cusp
  have oldBoundaryOne : certificate.cuspBoundaryCount
      (before ++ removed) suffix = 1 :=
    certificate.cuspBoundaryCount_eq_one
      (by simp [removed]) suffixNonempty oldBoundaryCusp
  have reversedSuffixLast :
      reversedSuffix.getLast reversedSuffixNonempty = partner.reverse := by
    simpa [reversedSuffix, suffix] using
      (Graph.EdgeWalk.getLast_reverseTraversal suffix suffixNonempty)
  have replacementJoinFree : ¬certificate.Cusp
      (reversedSuffix.getLast reversedSuffixNonempty)
      (later.path.traversed.head later.nonempty) := by
    rw [reversedSuffixLast]
    intro joinCusp
    apply later.initialFree
    unfold Cusp at cusp joinCusp ⊢
    exact cusp.trans joinCusp
  have replacementBoundaryZero : certificate.cuspBoundaryCount
      reversedSuffix later.path.traversed = 0 :=
    certificate.cuspBoundaryCount_eq_zero reversedSuffixNonempty
      later.nonempty replacementJoinFree
  have oldFormula : certificate.cuspCount cycle.traversed =
      certificate.cuspCount before +
        certificate.cuspCount removed +
        certificate.cuspBoundaryCount before removed +
        certificate.cuspCount suffix + 1 := by
    rw [originalEquation, certificate.cuspCount_append,
      certificate.cuspCount_append, oldBoundaryOne]
  have replacementFormula : certificate.cuspCount based.traversed =
      certificate.cuspCount reversedSuffix +
        certificate.cuspCount later.path.traversed +
        certificate.cuspBoundaryCount reversedSuffix later.path.traversed +
        certificate.cuspCount reversedBefore +
        certificate.cuspBoundaryCount
          (reversedSuffix ++ later.path.traversed) reversedBefore := by
    rw [replacementEquation, certificate.cuspCount_append,
      certificate.cuspCount_append]
  have laterCountZero := certificate.cuspCount_eq_zero_of_free later.cuspFree
  have suffixCount := certificate.cuspCount_reverseTraversal suffix
  have beforeCount := certificate.cuspCount_reverseTraversal before
  have newBoundaryBound := certificate.cuspBoundaryCount_le_one
    (reversedSuffix ++ later.path.traversed) reversedBefore
  have normalizedMinimal := minimal
  rw [oldFormula, replacementFormula,
    laterCountZero, replacementBoundaryZero] at normalizedMinimal
  change certificate.cuspCount reversedSuffix =
      certificate.cuspCount suffix at suffixCount
  change certificate.cuspCount reversedBefore =
      certificate.cuspCount before at beforeCount
  have removedCountZero : certificate.cuspCount removed = 0 := by
    omega
  have oldIncomingBoundaryZero :
      certificate.cuspBoundaryCount before removed = 0 := by
    omega
  have newExitBoundaryOne : certificate.cuspBoundaryCount
      (reversedSuffix ++ later.path.traversed) reversedBefore = 1 := by
    omega
  exact ⟨(certificate.cuspCount_eq_zero_iff removed).mp removedCountZero,
    oldIncomingBoundaryZero, newExitBoundaryOne⟩

/-- Numeric core of the symmetric after-cusp replacement. Minimality forces
the skipped post-cusp arc to be free, its exit into the old suffix to be free,
and the later path to use the unique available cusp at that same suffix. -/
theorem bungee_afterCusp_minimal_count_constraints
    (certificate : Certificate)
    (cycle based : certificate.fullGraph.EdgeSimpleCycle)
    {initial between suffix : List certificate.fullGraph.DirectedEdge}
    {middle partner outgoingAtHit last :
      certificate.fullGraph.DirectedEdge}
    (later : certificate.CuspFreeContinuation middle last)
    (cycleSteps : cycle.traversed =
      initial ++ middle :: partner :: between ++ outgoingAtHit :: suffix)
    (basedSteps : based.traversed =
      (initial ++ [middle]) ++ later.path.traversed ++
        (outgoingAtHit :: suffix))
    (cusp : certificate.Cusp middle partner)
    (minimal : certificate.cuspCount cycle.traversed ≤
      certificate.cuspCount based.traversed) :
    certificate.CuspFreeTraversal (partner :: between) ∧
      certificate.cuspBoundaryCount (partner :: between)
        (outgoingAtHit :: suffix) = 0 ∧
      certificate.cuspBoundaryCount
        ((initial ++ [middle]) ++ later.path.traversed)
        (outgoingAtHit :: suffix) = 1 := by
  let baseArc := initial ++ [middle]
  let oldArc := partner :: between
  let suffixArc := outgoingAtHit :: suffix
  have baseArcNonempty : baseArc ≠ [] := by simp [baseArc]
  have oldArcNonempty : oldArc ≠ [] := by simp [oldArc]
  have suffixArcNonempty : suffixArc ≠ [] := by simp [suffixArc]
  have baseArcLastOption : baseArc.getLast? = some middle := by
    rw [show baseArc = initial ++ [middle] by rfl, List.getLast?_append]
    simp
  have baseArcLast : baseArc.getLast baseArcNonempty = middle :=
    List.getLast_of_getLast?_eq_some baseArcLastOption
  have selectedBoundaryCusp : certificate.Cusp
      (baseArc.getLast baseArcNonempty)
      (oldArc.head oldArcNonempty) := by
    rw [baseArcLast]
    simpa [oldArc] using cusp
  have selectedBoundaryOne := certificate.cuspBoundaryCount_eq_one
    baseArcNonempty oldArcNonempty selectedBoundaryCusp
  have replacementBoundaryFree : ¬certificate.Cusp
      (baseArc.getLast baseArcNonempty)
      (later.path.traversed.head later.nonempty) := by
    rw [baseArcLast]
    exact later.initialFree
  have replacementBoundaryZero := certificate.cuspBoundaryCount_eq_zero
    baseArcNonempty later.nonempty replacementBoundaryFree
  have originalEquation : cycle.traversed =
      (baseArc ++ oldArc) ++ suffixArc := by
    simpa [baseArc, oldArc, suffixArc, List.append_assoc] using cycleSteps
  have candidateEquation : based.traversed =
      (baseArc ++ later.path.traversed) ++ suffixArc := by
    simpa [baseArc, suffixArc, List.append_assoc] using basedSteps
  have oldFormula : certificate.cuspCount cycle.traversed =
      certificate.cuspCount baseArc + certificate.cuspCount oldArc + 1 +
        certificate.cuspCount suffixArc +
        certificate.cuspBoundaryCount (baseArc ++ oldArc) suffixArc := by
    rw [originalEquation, certificate.cuspCount_append,
      certificate.cuspCount_append, selectedBoundaryOne]
  have candidateFormula : certificate.cuspCount based.traversed =
      certificate.cuspCount baseArc +
        certificate.cuspCount later.path.traversed + 0 +
        certificate.cuspCount suffixArc +
        certificate.cuspBoundaryCount
          (baseArc ++ later.path.traversed) suffixArc := by
    rw [candidateEquation, certificate.cuspCount_append,
      certificate.cuspCount_append, replacementBoundaryZero]
  have laterCountZero := certificate.cuspCount_eq_zero_of_free later.cuspFree
  have newBoundaryBound := certificate.cuspBoundaryCount_le_one
    (baseArc ++ later.path.traversed) suffixArc
  have normalizedMinimal := minimal
  rw [oldFormula, candidateFormula, laterCountZero] at normalizedMinimal
  have oldArcCountZero : certificate.cuspCount oldArc = 0 := by omega
  have oldExitBoundaryZero :
      certificate.cuspBoundaryCount (baseArc ++ oldArc) suffixArc = 0 := by
    omega
  have newExitBoundaryOne : certificate.cuspBoundaryCount
      (baseArc ++ later.path.traversed) suffixArc = 1 := by
    omega
  have oldArcExitBoundaryZero : certificate.cuspBoundaryCount
      oldArc suffixArc = 0 := by
    have baseOldNonempty : baseArc ++ oldArc ≠ [] := by
      simp [baseArcNonempty]
    have sameLast : (baseArc ++ oldArc).getLast baseOldNonempty =
        oldArc.getLast oldArcNonempty :=
      List.getLast_append_of_ne_nil baseOldNonempty oldArcNonempty
    have combinedFree :=
      (certificate.cuspBoundaryCount_eq_zero_iff
        baseOldNonempty suffixArcNonempty).mp oldExitBoundaryZero
    have oldFree : ¬certificate.Cusp (oldArc.getLast oldArcNonempty)
        (suffixArc.head suffixArcNonempty) := by
      rw [← sameLast]
      exact combinedFree
    exact certificate.cuspBoundaryCount_eq_zero oldArcNonempty
      suffixArcNonempty oldFree
  exact ⟨(certificate.cuspCount_eq_zero_iff oldArc).mp oldArcCountZero,
    oldArcExitBoundaryZero, newExitBoundaryOne⟩

/-- Boundary-color consequence of the symmetric minimality comparison: the
later path joins the reverse of the skipped old arc without a cusp. -/
theorem bungee_afterCusp_joinFree_of_minimal
    (certificate : Certificate)
    (cycle based : certificate.fullGraph.EdgeSimpleCycle)
    {initial between suffix : List certificate.fullGraph.DirectedEdge}
    {middle partner outgoingAtHit last :
      certificate.fullGraph.DirectedEdge}
    (later : certificate.CuspFreeContinuation middle last)
    (cycleSteps : cycle.traversed =
      initial ++ middle :: partner :: between ++ outgoingAtHit :: suffix)
    (basedSteps : based.traversed =
      (initial ++ [middle]) ++ later.path.traversed ++
        (outgoingAtHit :: suffix))
    (cusp : certificate.Cusp middle partner)
    (minimal : certificate.cuspCount cycle.traversed ≤
      certificate.cuspCount based.traversed) :
    ¬certificate.Cusp last
      ((partner :: between).getLast (by simp)).reverse := by
  rcases certificate.bungee_afterCusp_minimal_count_constraints cycle based
      later cycleSteps basedSteps cusp minimal with
    ⟨_oldArcFree, oldExitZero, newExitOne⟩
  let oldArc := partner :: between
  let suffixArc := outgoingAtHit :: suffix
  let baseLater := (initial ++ [middle]) ++ later.path.traversed
  have oldArcNonempty : oldArc ≠ [] := by simp [oldArc]
  have suffixArcNonempty : suffixArc ≠ [] := by simp [suffixArc]
  have baseLaterNonempty : baseLater ≠ [] := by simp [baseLater]
  have oldExitFree :=
    (certificate.cuspBoundaryCount_eq_zero_iff
      oldArcNonempty suffixArcNonempty).mp oldExitZero
  have newExitCusp :=
    (certificate.cuspBoundaryCount_eq_one_iff
      baseLaterNonempty suffixArcNonempty).mp newExitOne
  have baseLaterLastOption : baseLater.getLast? = some last := by
    change ((initial ++ [middle]) ++ later.path.traversed).getLast? =
      some last
    rw [List.getLast?_append,
      List.getLast?_eq_some_getLast later.nonempty, later.lastEdge]
    rfl
  have baseLaterLast : baseLater.getLast baseLaterNonempty = last :=
    List.getLast_of_getLast?_eq_some baseLaterLastOption
  have suffixArcHead : suffixArc.head suffixArcNonempty = outgoingAtHit := by
    simp [suffixArc]
  have newExitCuspExact : certificate.Cusp last outgoingAtHit := by
    rw [← baseLaterLast, ← suffixArcHead]
    exact newExitCusp
  have oldExitFreeExact : ¬certificate.Cusp
      (oldArc.getLast oldArcNonempty) outgoingAtHit := by
    rw [← suffixArcHead]
    exact oldExitFree
  intro badJoin
  apply oldExitFreeExact
  unfold Cusp at newExitCuspExact badJoin ⊢
  rw [Graph.DirectedEdge.reverse_reverse] at badJoin
  exact badJoin.symm.trans newExitCuspExact

/-- Minimality of the old non-closing cycle forces the whole removed arc from
the first hit through the chosen incoming cusp edge to be internally
cusp-free. -/
theorem bungee_removedArc_cuspFree_of_minimal (certificate : Certificate)
    (cycle based : certificate.fullGraph.EdgeSimpleCycle)
    {before between after : List certificate.fullGraph.DirectedEdge}
    {outgoingAtHit middle partner last :
      certificate.fullGraph.DirectedEdge}
    (later : certificate.CuspFreeContinuation middle last)
    (cycleSteps : cycle.traversed =
      before ++ outgoingAtHit :: between ++ middle :: partner :: after)
    (basedSteps : based.traversed =
      Graph.EdgeWalk.reverseTraversal (partner :: after) ++
        later.path.traversed ++
        Graph.EdgeWalk.reverseTraversal before)
    (cusp : certificate.Cusp middle partner)
    (minimal : certificate.cuspCount cycle.traversed ≤
      certificate.cuspCount based.traversed) :
    certificate.CuspFreeTraversal
      ((outgoingAtHit :: between) ++ [middle]) :=
  (certificate.bungee_minimal_count_constraints cycle based later cycleSteps
    basedSteps cusp minimal).1

/-- When the old prefix before the hit is nonempty, the two forced boundary
values from minimality imply that the later path joins the removed old arc
without a cusp. -/
theorem bungee_removedArc_joinFree_of_minimal (certificate : Certificate)
    (cycle based : certificate.fullGraph.EdgeSimpleCycle)
    {before between after : List certificate.fullGraph.DirectedEdge}
    {outgoingAtHit middle partner last :
      certificate.fullGraph.DirectedEdge}
    (later : certificate.CuspFreeContinuation middle last)
    (cycleSteps : cycle.traversed =
      before ++ outgoingAtHit :: between ++ middle :: partner :: after)
    (basedSteps : based.traversed =
      Graph.EdgeWalk.reverseTraversal (partner :: after) ++
        later.path.traversed ++
        Graph.EdgeWalk.reverseTraversal before)
    (cusp : certificate.Cusp middle partner)
    (minimal : certificate.cuspCount cycle.traversed ≤
      certificate.cuspCount based.traversed)
    (beforeNonempty : before ≠ []) :
    ¬certificate.Cusp last outgoingAtHit := by
  rcases certificate.bungee_minimal_count_constraints cycle based later
      cycleSteps basedSteps cusp minimal with
    ⟨_removedFree, oldBoundaryZero, newBoundaryOne⟩
  let removed := (outgoingAtHit :: between) ++ [middle]
  let reversedSuffix :=
    Graph.EdgeWalk.reverseTraversal (partner :: after)
  let reversedBefore := Graph.EdgeWalk.reverseTraversal before
  have removedNonempty : removed ≠ [] := by simp [removed]
  have reversedBeforeNonempty : reversedBefore ≠ [] := by
    simpa [reversedBefore, Graph.EdgeWalk.reverseTraversal] using
      beforeNonempty
  have newLeftNonempty :
      reversedSuffix ++ later.path.traversed ≠ [] := by
    simp [later.nonempty]
  have oldBoundaryFree :=
    (certificate.cuspBoundaryCount_eq_zero_iff
      beforeNonempty removedNonempty).mp oldBoundaryZero
  have newBoundaryCusp :=
    (certificate.cuspBoundaryCount_eq_one_iff
      newLeftNonempty reversedBeforeNonempty).mp newBoundaryOne
  have removedHead : removed.head removedNonempty = outgoingAtHit := by
    simp [removed]
  have oldBoundaryFreeExact : ¬certificate.Cusp
      (before.getLast beforeNonempty) outgoingAtHit := by
    rw [← removedHead]
    exact oldBoundaryFree
  have newLeftLast :
      (reversedSuffix ++ later.path.traversed).getLast newLeftNonempty =
        last := by
    rw [List.getLast_append_of_ne_nil newLeftNonempty later.nonempty,
      later.lastEdge]
  have reversedBeforeHead :
      reversedBefore.head reversedBeforeNonempty =
        (before.getLast beforeNonempty).reverse := by
    simpa [reversedBefore] using
      (Graph.EdgeWalk.head_reverseTraversal before beforeNonempty)
  have newBoundaryCuspExact : certificate.Cusp last
      (before.getLast beforeNonempty).reverse := by
    rw [← newLeftLast, ← reversedBeforeHead]
    exact newBoundaryCusp
  intro badJoin
  apply oldBoundaryFreeExact
  unfold Cusp at newBoundaryCuspExact badJoin ⊢
  rw [Graph.DirectedEdge.reverse_reverse] at newBoundaryCuspExact
  exact newBoundaryCuspExact.symm.trans badJoin

/-- For a strict (non-base) first hit, the later continuation and the removed
old arc close into a genuinely cusp-free exact-occurrence cycle. -/
theorem bungee_cuspFreeCycle_of_minimal_nonempty
    (certificate : Certificate)
    (structural : certificate.StructurallyWellFormed)
    (cycle based : certificate.fullGraph.EdgeSimpleCycle)
    {before between after : List certificate.fullGraph.DirectedEdge}
    {outgoingAtHit middle partner last :
      certificate.fullGraph.DirectedEdge}
    (later : certificate.CuspFreeContinuation middle last)
    (cycleSteps : cycle.traversed =
      before ++ outgoingAtHit :: between ++ middle :: partner :: after)
    (basedSteps : based.traversed =
      Graph.EdgeWalk.reverseTraversal (partner :: after) ++
        later.path.traversed ++
        Graph.EdgeWalk.reverseTraversal before)
    (cusp : certificate.Cusp middle partner)
    (hit : last.target = outgoingAtHit.source)
    (uniqueIntersection : ∀ vertex,
      vertex ∈ later.path.vertices.tail →
      vertex ∈ cycle.vertices → vertex = last.target)
    (minimal : certificate.cuspCount cycle.traversed ≤
      certificate.cuspCount based.traversed)
    (beforeNonempty : before ≠ []) :
    ∃ closed : certificate.fullGraph.EdgeSimpleCycle,
      certificate.CuspFreeCycle closed := by
  have removedFree := certificate.bungee_removedArc_cuspFree_of_minimal
    cycle based later cycleSteps basedSteps cusp minimal
  have joinFree := certificate.bungee_removedArc_joinFree_of_minimal
    cycle based later cycleSteps basedSteps cusp minimal beforeNonempty
  rcases cycle.middlePath cycleSteps with
    ⟨returnPath, returnStartsAtHit, returnFinishesAtCusp, returnSteps,
      returnVertexSubset, returnEdgeSubset⟩
  have returnNonempty : returnPath.traversed ≠ [] := by
    simp [returnSteps]
  have returnStarts : returnPath.start = last.target :=
    returnStartsAtHit.trans hit.symm
  have returnFinishes : returnPath.finish = later.path.start :=
    returnFinishesAtCusp.trans later.startsAt.symm
  have middleMembership : middle ∈ cycle.traversed := by
    rw [cycleSteps]
    simp
  have partnerMembership : partner ∈ cycle.traversed := by
    rw [cycleSteps]
    simp
  have cuspMeeting : middle.target = partner.source := by
    have fullChain := cycle.walk.toChain
    rw [cycleSteps] at fullChain
    have regrouped : certificate.fullGraph.EdgeChain cycle.start
        ((before ++ outgoingAtHit :: between) ++
          middle :: partner :: after) cycle.start := by
      simpa [List.append_assoc] using fullChain
    rcases regrouped.split_append with
      ⟨splitVertex, _prefixChain, suffixChain⟩
    cases suffixChain with
    | cons _middle middleStarts middleTail =>
        cases middleTail with
        | cons _partner partnerStarts partnerTail =>
            exact partnerStarts.symm
  rcases CuspFreeContinuation.firstIntersection_withCycle_cycle structural
      cycle later middleMembership partnerMembership cuspMeeting cusp
      returnPath returnNonempty returnStarts returnFinishes returnVertexSubset
      returnEdgeSubset uniqueIntersection with
    ⟨closed, _closedStarts, closedSteps⟩
  have returnHeadOption : returnPath.traversed.head? = some outgoingAtHit := by
    rw [returnSteps]
    simp
  have returnHead : returnPath.traversed.head returnNonempty =
      outgoingAtHit := List.head_of_head?_eq_some returnHeadOption
  have listJoinFree : ¬certificate.Cusp
      (later.path.traversed.getLast later.nonempty)
      (returnPath.traversed.head returnNonempty) := by
    rw [later.lastEdge, returnHead]
    exact joinFree
  have returnTraversalFree : certificate.CuspFreeTraversal
      returnPath.traversed := by
    rw [returnSteps]
    exact removedFree
  have closedTraversalFree : certificate.CuspFreeTraversal
      closed.traversed := by
    rw [closedSteps]
    exact CuspFreeTraversal.append certificate later.cuspFree
      returnTraversalFree later.nonempty returnNonempty listJoinFree
  have returnLastOption : returnPath.traversed.getLast? = some middle := by
    rw [returnSteps, List.getLast?_append]
    simp
  have closedLastOption : closed.traversed.getLast? = some middle := by
    rw [closedSteps, List.getLast?_append, returnLastOption]
    rfl
  have closedLast : closed.traversed.getLast closed.nonempty = middle :=
    List.getLast_of_getLast?_eq_some closedLastOption
  have closedHeadOption : closed.traversed.head? =
      some (later.path.traversed.head later.nonempty) := by
    rw [closedSteps, List.head?_append,
      List.head?_eq_some_head later.nonempty]
    rfl
  have closedHead : closed.traversed.head closed.nonempty =
      later.path.traversed.head later.nonempty :=
    List.head_of_head?_eq_some closedHeadOption
  have closedClosingFree : ¬certificate.ClosingCusp closed := by
    intro closing
    unfold ClosingCusp at closing
    rw [closedLast, closedHead] at closing
    exact later.initialFree closing
  have closedFreeIff : certificate.CuspFreeCycle closed ↔
      certificate.CuspFreeTraversal closed.traversed ∧
        ¬certificate.ClosingCusp closed := by
    cases traversalEquation : closed.traversed with
    | nil => exact False.elim (closed.nonempty traversalEquation)
    | cons first rest =>
        simp [CuspFreeCycle, ClosingCusp, traversalEquation]
  exact ⟨closed, closedFreeIff.2
    ⟨closedTraversalFree, closedClosingFree⟩⟩

/-- The complete same-base minimality step for an oriented first
intersection: construct the non-closing splice, invoke minimality, and recover
cusp-freedom of the removed old arc. -/
theorem bungee_firstIntersection_removedArc_cuspFree
    (certificate : Certificate)
    (structural : certificate.StructurallyWellFormed)
    (cycle : certificate.fullGraph.EdgeSimpleCycle)
    {before between after : List certificate.fullGraph.DirectedEdge}
    {outgoingAtHit middle partner last :
      certificate.fullGraph.DirectedEdge}
    (cycleSteps : cycle.traversed =
      before ++ outgoingAtHit :: between ++ middle :: partner :: after)
    (cusp : certificate.Cusp middle partner)
    (later : certificate.CuspFreeContinuation middle last)
    (hit : last.target = outgoingAtHit.source)
    (uniqueIntersection : ∀ vertex,
      vertex ∈ later.path.vertices.tail →
      vertex ∈ cycle.vertices → vertex = last.target)
    (cycleClosingFree : ¬certificate.ClosingCusp cycle)
    (baseHitClosingFree : before = [] →
      ¬certificate.Cusp last
        ((partner :: after).getLast (by simp)).reverse)
    (minimal : ∀ other : certificate.fullGraph.EdgeSimpleCycle,
      other.start = cycle.start → ¬certificate.ClosingCusp other →
      certificate.cuspCount cycle.traversed ≤
        certificate.cuspCount other.traversed) :
    certificate.CuspFreeTraversal
      ((outgoingAtHit :: between) ++ [middle]) := by
  rcases certificate.bungee_firstIntersection_nonclosingSameBase structural
      cycle cycleSteps cusp later hit uniqueIntersection cycleClosingFree
      baseHitClosingFree with
    ⟨based, basedStarts, basedClosingFree, basedSteps⟩
  exact certificate.bungee_removedArc_cuspFree_of_minimal cycle based later
    cycleSteps basedSteps cusp
    (minimal based basedStarts basedClosingFree)

/-- If the first return is the old base and the later endpoint is free against
the reversed final old edge, the same-base splice contradicts minimality
immediately: there is no boundary slot in the empty old prefix for the cusp
that the count inequality would require. -/
theorem no_minimal_bungee_firstIntersection_atBase
    (certificate : Certificate)
    (structural : certificate.StructurallyWellFormed)
    (cycle : certificate.fullGraph.EdgeSimpleCycle)
    {between after : List certificate.fullGraph.DirectedEdge}
    {outgoingAtHit middle partner last :
      certificate.fullGraph.DirectedEdge}
    (cycleSteps : cycle.traversed =
      outgoingAtHit :: between ++ middle :: partner :: after)
    (cusp : certificate.Cusp middle partner)
    (later : certificate.CuspFreeContinuation middle last)
    (hit : last.target = outgoingAtHit.source)
    (uniqueIntersection : ∀ vertex,
      vertex ∈ later.path.vertices.tail →
      vertex ∈ cycle.vertices → vertex = last.target)
    (cycleClosingFree : ¬certificate.ClosingCusp cycle)
    (endpointFree : ¬certificate.Cusp last
      ((partner :: after).getLast (by simp)).reverse)
    (minimal : ∀ other : certificate.fullGraph.EdgeSimpleCycle,
      other.start = cycle.start → ¬certificate.ClosingCusp other →
      certificate.cuspCount cycle.traversed ≤
        certificate.cuspCount other.traversed) : False := by
  have expandedSteps : cycle.traversed =
      ([] : List certificate.fullGraph.DirectedEdge) ++
        outgoingAtHit :: between ++ middle :: partner :: after := by
    simpa using cycleSteps
  have baseHitClosingFree :
      ([] : List certificate.fullGraph.DirectedEdge) = [] →
        ¬certificate.Cusp last
          ((partner :: after).getLast (by simp)).reverse := by
    intro _
    exact endpointFree
  rcases certificate.bungee_firstIntersection_nonclosingSameBase structural
      cycle expandedSteps cusp later hit uniqueIntersection cycleClosingFree
      baseHitClosingFree with
    ⟨based, basedStarts, basedClosingFree, basedSteps⟩
  have constraints := certificate.bungee_minimal_count_constraints
    cycle based later expandedSteps basedSteps cusp
      (minimal based basedStarts basedClosingFree)
  have impossibleBoundary := constraints.2.2
  simp [Graph.EdgeWalk.reverseTraversal, cuspBoundaryCount] at impossibleBoundary

/-- The complementary base-hit orientation is impossible as well. If the
later endpoint is free against the old first edge, rotate the exact
later/old-prefix cycle to the old base. Its count omits the selected old cusp,
strictly contradicting minimality. -/
theorem no_minimal_bungee_firstIntersection_atBase_forward
    (certificate : Certificate)
    (structural : certificate.StructurallyWellFormed)
    (cycle : certificate.fullGraph.EdgeSimpleCycle)
    {between after : List certificate.fullGraph.DirectedEdge}
    {outgoingAtHit middle partner last :
      certificate.fullGraph.DirectedEdge}
    (cycleSteps : cycle.traversed =
      outgoingAtHit :: between ++ middle :: partner :: after)
    (cusp : certificate.Cusp middle partner)
    (later : certificate.CuspFreeContinuation middle last)
    (hit : last.target = outgoingAtHit.source)
    (uniqueIntersection : ∀ vertex,
      vertex ∈ later.path.vertices.tail →
      vertex ∈ cycle.vertices → vertex = last.target)
    (endpointFree : ¬certificate.Cusp last outgoingAtHit)
    (minimal : ∀ other : certificate.fullGraph.EdgeSimpleCycle,
      other.start = cycle.start → ¬certificate.ClosingCusp other →
      certificate.cuspCount cycle.traversed ≤
        certificate.cuspCount other.traversed) : False := by
  have expandedSteps : cycle.traversed =
      ([] : List certificate.fullGraph.DirectedEdge) ++
        outgoingAtHit :: between ++ middle :: partner :: after := by
    simpa using cycleSteps
  rcases cycle.middlePath expandedSteps with
    ⟨returnPath, returnStartsAtHit, returnFinishesAtCusp, returnSteps,
      returnVertexSubset, returnEdgeSubset⟩
  have returnNonempty : returnPath.traversed ≠ [] := by
    simp [returnSteps]
  have returnStarts : returnPath.start = last.target :=
    returnStartsAtHit.trans hit.symm
  have returnFinishes : returnPath.finish = later.path.start :=
    returnFinishesAtCusp.trans later.startsAt.symm
  have middleMembership : middle ∈ cycle.traversed := by
    rw [cycleSteps]
    simp
  have partnerMembership : partner ∈ cycle.traversed := by
    rw [cycleSteps]
    simp
  have cuspMeeting : middle.target = partner.source := by
    have fullChain := cycle.walk.toChain
    rw [cycleSteps] at fullChain
    have regrouped : certificate.fullGraph.EdgeChain cycle.start
        ((outgoingAtHit :: between) ++
          middle :: partner :: after) cycle.start := by
      simpa [List.append_assoc] using fullChain
    rcases regrouped.split_append with
      ⟨splitVertex, _prefixChain, suffixChain⟩
    cases suffixChain with
    | cons _middle middleStarts middleTail =>
        cases middleTail with
        | cons _partner partnerStarts partnerTail =>
            exact partnerStarts.symm
  rcases CuspFreeContinuation.firstIntersection_withCycle_cycle structural
      cycle later middleMembership partnerMembership cuspMeeting cusp
      returnPath returnNonempty returnStarts returnFinishes returnVertexSubset
      returnEdgeSubset uniqueIntersection with
    ⟨closed, _closedStarts, closedSteps⟩
  have closedDecomposition : closed.traversed =
      later.path.traversed ++ outgoingAtHit :: (between ++ [middle]) := by
    rw [closedSteps, returnSteps]
    simp
  rcases closed.rotateAt_exists closedDecomposition with
    ⟨based, basedStartsAtHit, basedSteps⟩
  have hitIsBase : outgoingAtHit.source = cycle.start := by
    have chain := cycle.walk.toChain
    rw [cycleSteps] at chain
    exact chain.head_source
  have basedStarts : based.start = cycle.start :=
    basedStartsAtHit.trans hitIsBase
  have basedHeadOption : based.traversed.head? = some outgoingAtHit := by
    rw [basedSteps]
    simp
  have basedHead : based.traversed.head based.nonempty = outgoingAtHit :=
    List.head_of_head?_eq_some basedHeadOption
  have basedLastOption : based.traversed.getLast? = some last := by
    rw [basedSteps, List.getLast?_append,
      List.getLast?_eq_some_getLast later.nonempty, later.lastEdge]
    rfl
  have basedLast : based.traversed.getLast based.nonempty = last :=
    List.getLast_of_getLast?_eq_some basedLastOption
  have basedClosingFree : ¬certificate.ClosingCusp based := by
    intro closing
    unfold ClosingCusp at closing
    rw [basedLast, basedHead] at closing
    exact endpointFree closing
  have removedNonempty : (outgoingAtHit :: between) ++ [middle] ≠ [] := by
    simp
  have removedLastOption :
      ((outgoingAtHit :: between) ++ [middle]).getLast? = some middle := by
    rw [List.getLast?_append]
    simp
  have removedLast :
      ((outgoingAtHit :: between) ++ [middle]).getLast removedNonempty =
        middle := List.getLast_of_getLast?_eq_some removedLastOption
  have candidateBoundaryFree : ¬certificate.Cusp
      (((outgoingAtHit :: between) ++ [middle]).getLast removedNonempty)
      (later.path.traversed.head later.nonempty) := by
    rw [removedLast]
    exact later.initialFree
  have candidateBoundaryZero := certificate.cuspBoundaryCount_eq_zero
    removedNonempty later.nonempty candidateBoundaryFree
  have candidateBoundaryZeroNormalized : certificate.cuspBoundaryCount
      (outgoingAtHit :: (between ++ [middle])) later.path.traversed = 0 := by
    simpa only [List.cons_append] using candidateBoundaryZero
  have oldBoundaryCusp : certificate.Cusp
      (((outgoingAtHit :: between) ++ [middle]).getLast removedNonempty)
      ((partner :: after).head (by simp)) := by
    rw [removedLast]
    simpa using cusp
  have oldBoundaryOne := certificate.cuspBoundaryCount_eq_one
    removedNonempty (by simp : partner :: after ≠ []) oldBoundaryCusp
  have oldFormula : certificate.cuspCount cycle.traversed =
      certificate.cuspCount ((outgoingAtHit :: between) ++ [middle]) +
        certificate.cuspCount (partner :: after) + 1 := by
    have regrouped : cycle.traversed =
        ((outgoingAtHit :: between) ++ [middle]) ++ (partner :: after) := by
      simpa [List.append_assoc] using cycleSteps
    rw [regrouped, certificate.cuspCount_append, oldBoundaryOne]
  have basedFormula : certificate.cuspCount based.traversed =
      certificate.cuspCount ((outgoingAtHit :: between) ++ [middle]) := by
    rw [basedSteps, certificate.cuspCount_append,
      certificate.cuspCount_eq_zero_of_free later.cuspFree,
      candidateBoundaryZeroNormalized]
    simp only [List.cons_append, Nat.add_zero]
  have minimalBound := minimal based basedStarts basedClosingFree
  rw [oldFormula, basedFormula] at minimalBound
  omega

/-- The two base-hit endpoint orientations are exhaustive because the old
cycle itself closes freely. Hence a minimal non-closing cycle admits no
first-return continuation whose first intersection is its base. -/
theorem no_minimal_bungee_firstIntersection_atBase_anyOrientation
    (certificate : Certificate)
    (structural : certificate.StructurallyWellFormed)
    (cycle : certificate.fullGraph.EdgeSimpleCycle)
    {between after : List certificate.fullGraph.DirectedEdge}
    {outgoingAtHit middle partner last :
      certificate.fullGraph.DirectedEdge}
    (cycleSteps : cycle.traversed =
      outgoingAtHit :: between ++ middle :: partner :: after)
    (cusp : certificate.Cusp middle partner)
    (later : certificate.CuspFreeContinuation middle last)
    (hit : last.target = outgoingAtHit.source)
    (uniqueIntersection : ∀ vertex,
      vertex ∈ later.path.vertices.tail →
      vertex ∈ cycle.vertices → vertex = last.target)
    (cycleClosingFree : ¬certificate.ClosingCusp cycle)
    (minimal : ∀ other : certificate.fullGraph.EdgeSimpleCycle,
      other.start = cycle.start → ¬certificate.ClosingCusp other →
      certificate.cuspCount cycle.traversed ≤
        certificate.cuspCount other.traversed) : False := by
  have cycleHeadOption : cycle.traversed.head? = some outgoingAtHit := by
    rw [cycleSteps]
    simp
  have cycleHead : cycle.traversed.head cycle.nonempty = outgoingAtHit :=
    List.head_of_head?_eq_some cycleHeadOption
  have suffixNonempty : partner :: after ≠ [] := by simp
  have cycleLastOption : cycle.traversed.getLast? =
      some ((partner :: after).getLast suffixNonempty) := by
    have grouped : cycle.traversed =
        ((outgoingAtHit :: between) ++ [middle]) ++ (partner :: after) := by
      simpa [List.append_assoc] using cycleSteps
    rw [grouped, List.getLast?_append,
      List.getLast?_eq_some_getLast suffixNonempty]
    simp
  have cycleLast : cycle.traversed.getLast cycle.nonempty =
      (partner :: after).getLast suffixNonempty :=
    List.getLast_of_getLast?_eq_some cycleLastOption
  by_cases forwardFree : ¬certificate.Cusp last
      (cycle.traversed.head cycle.nonempty)
  · have endpointFree : ¬certificate.Cusp last outgoingAtHit := by
      rw [← cycleHead]
      exact forwardFree
    exact certificate.no_minimal_bungee_firstIntersection_atBase_forward
      structural cycle cycleSteps cusp later hit uniqueIntersection
      endpointFree minimal
  · have reverseFree : ¬certificate.Cusp last
        (cycle.traversed.getLast cycle.nonempty).reverse := by
      intro reverseCusp
      apply cycleClosingFree
      unfold ClosingCusp Cusp at cycleClosingFree ⊢
      have forwardCusp : certificate.Cusp last
          (cycle.traversed.head cycle.nonempty) :=
        Classical.byContradiction (fun absent => forwardFree absent)
      unfold Cusp at forwardCusp reverseCusp
      rw [Graph.DirectedEdge.reverse_reverse] at reverseCusp
      exact reverseCusp.symm.trans forwardCusp
    have endpointFree : ¬certificate.Cusp last
        ((partner :: after).getLast suffixNonempty).reverse := by
      rw [← cycleLast]
      exact reverseFree
    exact certificate.no_minimal_bungee_firstIntersection_atBase structural
      cycle cycleSteps cusp later hit uniqueIntersection cycleClosingFree
      endpointFree minimal

theorem cuspFreeCycle_iff (certificate : Certificate)
    (cycle : certificate.fullGraph.EdgeSimpleCycle) :
    certificate.CuspFreeCycle cycle ↔
      certificate.CuspFreeTraversal cycle.traversed ∧
        ¬certificate.ClosingCusp cycle := by
  cases traversalEquation : cycle.traversed with
  | nil => exact False.elim (cycle.nonempty traversalEquation)
  | cons first rest =>
      simp [CuspFreeCycle, ClosingCusp, traversalEquation]

theorem closingCusp_reverse_iff (certificate : Certificate)
    (cycle : certificate.fullGraph.EdgeSimpleCycle) :
    certificate.ClosingCusp cycle.reverse ↔
      certificate.ClosingCusp cycle := by
  have reversed := (certificate.cusp_reverse_iff
    (cycle.traversed.getLast cycle.nonempty)
    (cycle.traversed.head cycle.nonempty)).symm
  simpa [ClosingCusp, Graph.EdgeSimpleCycle.reverse,
    Graph.EdgeWalk.reverseTraversal] using reversed

/-- At a freely closing cycle base, an incoming edge is cusp-free with at
least one of the two possible first directions around the cycle. -/
theorem initial_or_reverse_initial_free (certificate : Certificate)
    (cycle : certificate.fullGraph.EdgeSimpleCycle)
    (closingFree : ¬certificate.ClosingCusp cycle)
    (incoming : certificate.fullGraph.DirectedEdge) :
    (¬certificate.Cusp incoming
        (cycle.traversed.head cycle.nonempty)) ∨
      (¬certificate.Cusp incoming
        (cycle.traversed.getLast cycle.nonempty).reverse) := by
  classical
  by_cases firstFree : ¬certificate.Cusp incoming
      (cycle.traversed.head cycle.nonempty)
  · exact .inl firstFree
  · right
    intro reverseCusp
    apply closingFree
    unfold ClosingCusp Cusp at closingFree ⊢
    have firstCusp : certificate.Cusp incoming
        (cycle.traversed.head cycle.nonempty) :=
      Classical.byContradiction (fun absent => firstFree absent)
    unfold Cusp at firstCusp reverseCusp
    rw [Graph.DirectedEdge.reverse_reverse] at reverseCusp
    exact reverseCusp.symm.trans firstCusp

/-- Choose the orientation of a freely closing simple cycle so a prescribed
incoming edge does not cusp with its first traversal edge. -/
theorem orient_cycle_initial_free (certificate : Certificate)
    (cycle : certificate.fullGraph.EdgeSimpleCycle)
    (closingFree : ¬certificate.ClosingCusp cycle)
    (incoming : certificate.fullGraph.DirectedEdge) :
    ∃ oriented : certificate.fullGraph.EdgeSimpleCycle,
      oriented.start = cycle.start ∧
      ¬certificate.ClosingCusp oriented ∧
      ¬certificate.Cusp incoming
        (oriented.traversed.head oriented.nonempty) ∧
      certificate.cuspCount oriented.traversed =
        certificate.cuspCount cycle.traversed := by
  rcases certificate.initial_or_reverse_initial_free cycle closingFree incoming with
    forwardFree | reverseFree
  · exact ⟨cycle, rfl, closingFree, forwardFree, rfl⟩
  · have reverseClosingFree : ¬certificate.ClosingCusp cycle.reverse := by
      intro reverseClosing
      exact closingFree
        ((certificate.closingCusp_reverse_iff cycle).mp reverseClosing)
    refine ⟨cycle.reverse, rfl, reverseClosingFree, ?_, ?_⟩
    · simpa [Graph.EdgeSimpleCycle.reverse,
        Graph.EdgeWalk.reverseTraversal] using reverseFree
    · exact certificate.cuspCount_reverseTraversal cycle.traversed

theorem CuspFreeCycle.no_cusp_of_successor (certificate : Certificate)
    {cycle : certificate.fullGraph.EdgeSimpleCycle}
    (free : certificate.CuspFreeCycle cycle)
    {incoming outgoing : certificate.fullGraph.DirectedEdge}
    (successor : cycle.CyclicSuccessor incoming outgoing) :
    ¬certificate.Cusp incoming outgoing := by
  rcases successor with internal | closing
  · rcases internal with ⟨before, after, traversalEquation⟩
    have suffixFree := CuspFreeTraversal.suffix certificate
      (initial := before)
      (suffix := incoming :: outgoing :: after) (by
        rw [← traversalEquation]
        exact free.1)
    exact suffixFree.1
  · rcases closing with ⟨middle, traversalEquation⟩
    have closingFree := free.2
    rw [traversalEquation] at closingFree
    change ¬certificate.Cusp
      ((outgoing :: (middle ++ [incoming])).getLast (by simp)) outgoing at closingFree
    have lastEquation :
        ((outgoing :: (middle ++ [incoming])).getLast (by simp)) = incoming := by
      calc
        ((outgoing :: middle) ++ [incoming]).getLast (by simp) =
            [incoming].getLast (by simp) :=
          List.getLast_append_of_ne_nil (by simp) (by simp)
        _ = incoming := List.getLast_singleton _
    rw [lastEquation] at closingFree
    exact closingFree

/-- A cusp-free simple cycle cannot traverse two distinct full-edge
occurrences carrying the same par target. Equal orientations would repeat a
cycle source or target; opposite orientations make the two occurrences
cyclically consecutive and expose the forbidden par cusp. -/
theorem CuspFreeCycle.not_both_same_par (certificate : Certificate)
    {cycle : certificate.fullGraph.EdgeSimpleCycle}
    (free : certificate.CuspFreeCycle cycle)
    {first second : certificate.fullGraph.DirectedEdge}
    (firstMembership : first ∈ cycle.traversed)
    (secondMembership : second ∈ cycle.traversed)
    {conclusion : Vertex}
    (firstTarget :
      certificate.fullEdgeParTargets[first.index]? = some (some conclusion))
    (secondTarget :
      certificate.fullEdgeParTargets[second.index]? = some (some conclusion))
    (differentIndex : first.index ≠ second.index) : False := by
  have firstEdgeLookup :
      certificate.fullEdges[first.index]? = some first.edge := first.lookup
  have secondEdgeLookup :
      certificate.fullEdges[second.index]? = some second.edge := second.lookup
  have firstAnnotation :
      certificate.fullEdgeAnnotations[first.index]? =
        some (first.edge, some conclusion) :=
    certificate.fullEdgeAnnotation_lookup_iff.mpr
      ⟨firstEdgeLookup, firstTarget⟩
  have secondAnnotation :
      certificate.fullEdgeAnnotations[second.index]? =
        some (second.edge, some conclusion) :=
    certificate.fullEdgeAnnotation_lookup_iff.mpr
      ⟨secondEdgeLookup, secondTarget⟩
  have firstSecond : first.edge.second = conclusion :=
    certificate.fullEdgeAnnotation_some_second firstAnnotation
  have secondSecond : second.edge.second = conclusion :=
    certificate.fullEdgeAnnotation_some_second secondAnnotation
  have different : first ≠ second := by
    intro same
    exact differentIndex (congrArg Graph.DirectedEdge.index same)
  cases firstDirection : first.forward with
  | false =>
      cases secondDirection : second.forward with
      | false =>
          have sameSource : first.source = second.source := by
            simp [Graph.DirectedEdge.source, firstDirection, secondDirection,
              firstSecond, secondSecond]
          exact different
            (cycle.eq_of_source_eq firstMembership secondMembership sameSource)
      | true =>
          have meeting : second.target = first.source := by
            simp [Graph.DirectedEdge.source, Graph.DirectedEdge.target,
              firstDirection, secondDirection, firstSecond, secondSecond]
          have successor := cycle.successor_of_target_eq_source
            secondMembership firstMembership different.symm meeting
          have noCusp := CuspFreeCycle.no_cusp_of_successor certificate
            free successor
          apply noCusp
          unfold Cusp
          have secondColor :
              certificate.incidenceColor second = .par conclusion :=
            (certificate.incidenceColor_eq_par_iff second conclusion).2
              ⟨secondDirection, secondTarget⟩
          have firstReverseDirection : first.reverse.forward = true := by
            change (!first.forward) = true
            rw [firstDirection]
            rfl
          have firstReverseColor :
              certificate.incidenceColor first.reverse = .par conclusion :=
            (certificate.incidenceColor_eq_par_iff first.reverse conclusion).2
              ⟨firstReverseDirection, firstTarget⟩
          rw [secondColor, firstReverseColor]
  | true =>
      cases secondDirection : second.forward with
      | false =>
          have meeting : first.target = second.source := by
            simp [Graph.DirectedEdge.source, Graph.DirectedEdge.target,
              firstDirection, secondDirection, firstSecond, secondSecond]
          have successor := cycle.successor_of_target_eq_source
            firstMembership secondMembership different meeting
          have noCusp := CuspFreeCycle.no_cusp_of_successor certificate
            free successor
          apply noCusp
          unfold Cusp
          have firstColor :
              certificate.incidenceColor first = .par conclusion :=
            (certificate.incidenceColor_eq_par_iff first conclusion).2
              ⟨firstDirection, firstTarget⟩
          have secondReverseDirection : second.reverse.forward = true := by
            change (!second.forward) = true
            rw [secondDirection]
            rfl
          have secondReverseColor :
              certificate.incidenceColor second.reverse = .par conclusion :=
            (certificate.incidenceColor_eq_par_iff second.reverse conclusion).2
              ⟨secondReverseDirection, secondTarget⟩
          rw [firstColor, secondReverseColor]
      | true =>
          have sameTarget : first.target = second.target := by
            simp [Graph.DirectedEdge.target, firstDirection, secondDirection,
              firstSecond, secondSecond]
          exact different
            (cycle.eq_of_target_eq firstMembership secondMembership sameTarget)

/-- The exact full-edge index occurs in this edge-identity-aware cycle. -/
def CycleUsesIndex {certificate : Certificate}
    (cycle : certificate.fullGraph.EdgeSimpleCycle) (index : Nat) : Prop :=
  ∃ directed ∈ cycle.traversed, directed.index = index

/-- Every suffix of the certificate's link list is par-pair sparse at its
absolute full-edge offset when the requested indices come from a cusp-free
simple cycle. -/
theorem CuspFreeCycle.parPairSparse_suffix (certificate : Certificate)
    {cycle : certificate.fullGraph.EdgeSimpleCycle}
    (free : certificate.CuspFreeCycle cycle)
    {priorLinks suffix : List Link}
    (linksEquation : certificate.links = priorLinks ++ suffix) :
    ParPairSparse suffix (linkFullEdges priorLinks).length
      (CycleUsesIndex cycle) := by
  induction suffix generalizing priorLinks with
  | nil => trivial
  | cons link rest ih =>
      cases link with
      | «axiom» left right =>
          change ParPairSparse rest ((linkFullEdges priorLinks).length + 1)
            (CycleUsesIndex cycle)
          have restEquation : certificate.links =
              (priorLinks ++ [.axiom left right]) ++ rest := by
            simpa [List.append_assoc] using linksEquation
          have tailSparse := ih
            (priorLinks := priorLinks ++ [.axiom left right])
            restEquation
          simpa using tailSparse
      | tensor left right conclusion =>
          change ParPairSparse rest ((linkFullEdges priorLinks).length + 2)
            (CycleUsesIndex cycle)
          have restEquation : certificate.links =
              (priorLinks ++ [.tensor left right conclusion]) ++ rest := by
            simpa [List.append_assoc] using linksEquation
          have tailSparse := ih
            (priorLinks := priorLinks ++ [.tensor left right conclusion])
            restEquation
          simpa using tailSparse
      | par left right conclusion =>
          change
            (¬(CycleUsesIndex cycle (linkFullEdges priorLinks).length ∧
              CycleUsesIndex cycle ((linkFullEdges priorLinks).length + 1))) ∧
              ParPairSparse rest ((linkFullEdges priorLinks).length + 2)
                (CycleUsesIndex cycle)
          constructor
          · rintro ⟨firstUsed, secondUsed⟩
            rcases firstUsed with
              ⟨firstDirected, firstMembership, firstIndex⟩
            rcases secondUsed with
              ⟨secondDirected, secondMembership, secondIndex⟩
            have firstOffsetTarget :
                certificate.fullEdgeParTargets[
                    (linkFullEdges priorLinks).length]? =
                  some (some conclusion) := by
              rw [← certificate.linkFullEdgeParTargets_certificate]
              rw [linksEquation, linkFullEdgeParTargets_append]
              rw [← linkFullEdgeParTargets_length priorLinks]
              simp
            have secondOffsetTarget :
                certificate.fullEdgeParTargets[
                    (linkFullEdges priorLinks).length + 1]? =
                  some (some conclusion) := by
              rw [← certificate.linkFullEdgeParTargets_certificate]
              rw [linksEquation, linkFullEdgeParTargets_append]
              rw [← linkFullEdgeParTargets_length priorLinks]
              simp
            have firstTarget :
                certificate.fullEdgeParTargets[firstDirected.index]? =
                  some (some conclusion) := by
              simpa [firstIndex] using firstOffsetTarget
            have secondTarget :
                certificate.fullEdgeParTargets[secondDirected.index]? =
                  some (some conclusion) := by
              simpa [secondIndex] using secondOffsetTarget
            have differentIndex :
                firstDirected.index ≠ secondDirected.index := by
              omega
            exact CuspFreeCycle.not_both_same_par certificate free
              firstMembership secondMembership firstTarget secondTarget
              differentIndex
          · have restEquation : certificate.links =
                (priorLinks ++ [.par left right conclusion]) ++ rest := by
              simpa [List.append_assoc] using linksEquation
            have tailSparse := ih
              (priorLinks := priorLinks ++ [.par left right conclusion])
              restEquation
            simpa using tailSparse

/-- Proposition-level colored acyclicity used by the splitting theorem: there
is no nonempty simple cycle whose every local transition avoids a cusp. -/
def CuspAcyclic (certificate : Certificate) : Prop :=
  ∀ cycle : certificate.fullGraph.EdgeSimpleCycle,
    ¬certificate.CuspFreeCycle cycle

/-- Strict first returns to the old cycle are impossible for a minimal freely
closing cycle in a cusp-acyclic graph. This is the non-base branch of the
bungee contradiction. -/
theorem CuspAcyclic.no_minimal_bungee_firstIntersection_nonempty
    (certificate : Certificate) (acyclic : certificate.CuspAcyclic)
    (structural : certificate.StructurallyWellFormed)
    (cycle : certificate.fullGraph.EdgeSimpleCycle)
    {before between after : List certificate.fullGraph.DirectedEdge}
    {outgoingAtHit middle partner last :
      certificate.fullGraph.DirectedEdge}
    (cycleSteps : cycle.traversed =
      before ++ outgoingAtHit :: between ++ middle :: partner :: after)
    (cusp : certificate.Cusp middle partner)
    (later : certificate.CuspFreeContinuation middle last)
    (hit : last.target = outgoingAtHit.source)
    (uniqueIntersection : ∀ vertex,
      vertex ∈ later.path.vertices.tail →
      vertex ∈ cycle.vertices → vertex = last.target)
    (cycleClosingFree : ¬certificate.ClosingCusp cycle)
    (minimal : ∀ other : certificate.fullGraph.EdgeSimpleCycle,
      other.start = cycle.start → ¬certificate.ClosingCusp other →
      certificate.cuspCount cycle.traversed ≤
        certificate.cuspCount other.traversed)
    (beforeNonempty : before ≠ []) : False := by
  have baseHitClosingFree : before = [] →
      ¬certificate.Cusp last
        ((partner :: after).getLast (by simp)).reverse := by
    intro beforeEmpty
    exact False.elim (beforeNonempty beforeEmpty)
  rcases certificate.bungee_firstIntersection_nonclosingSameBase structural
      cycle cycleSteps cusp later hit uniqueIntersection cycleClosingFree
      baseHitClosingFree with
    ⟨based, basedStarts, basedClosingFree, basedSteps⟩
  rcases certificate.bungee_cuspFreeCycle_of_minimal_nonempty structural
      cycle based later cycleSteps basedSteps cusp hit uniqueIntersection
      (minimal based basedStarts basedClosingFree) beforeNonempty with
    ⟨closed, closedFree⟩
  exact acyclic closed closedFree

/-- Unified oriented bungee contradiction, including both strict and
hit-at-base first intersections. -/
theorem CuspAcyclic.no_minimal_bungee_firstIntersection
    (certificate : Certificate) (acyclic : certificate.CuspAcyclic)
    (structural : certificate.StructurallyWellFormed)
    (cycle : certificate.fullGraph.EdgeSimpleCycle)
    {before between after : List certificate.fullGraph.DirectedEdge}
    {outgoingAtHit middle partner last :
      certificate.fullGraph.DirectedEdge}
    (cycleSteps : cycle.traversed =
      before ++ outgoingAtHit :: between ++ middle :: partner :: after)
    (cusp : certificate.Cusp middle partner)
    (later : certificate.CuspFreeContinuation middle last)
    (hit : last.target = outgoingAtHit.source)
    (uniqueIntersection : ∀ vertex,
      vertex ∈ later.path.vertices.tail →
      vertex ∈ cycle.vertices → vertex = last.target)
    (cycleClosingFree : ¬certificate.ClosingCusp cycle)
    (minimal : ∀ other : certificate.fullGraph.EdgeSimpleCycle,
      other.start = cycle.start → ¬certificate.ClosingCusp other →
      certificate.cuspCount cycle.traversed ≤
        certificate.cuspCount other.traversed) : False := by
  by_cases beforeEmpty : before = []
  · subst before
    have baseSteps : cycle.traversed =
        outgoingAtHit :: between ++ middle :: partner :: after := by
      simpa using cycleSteps
    exact certificate.no_minimal_bungee_firstIntersection_atBase_anyOrientation
      structural cycle baseSteps cusp later hit uniqueIntersection
      cycleClosingFree minimal
  · exact acyclic.no_minimal_bungee_firstIntersection_nonempty certificate
      structural cycle cycleSteps cusp later hit uniqueIntersection
      cycleClosingFree minimal beforeEmpty

/-- Degenerate base case for the exhaustive bungee classification.  The later
continuation returns to the source of the selected incoming cusp edge, which is
also the old cycle base.  If the new endpoint closes freely against that edge,
use the one-edge old return.  Otherwise reverse the old post-cusp arc; the old
cycle's free closing transition makes that orientation close freely.  Either
candidate removes the selected cusp and contradicts same-base minimality. -/
theorem no_minimal_bungee_atIncoming_base
    (certificate : Certificate)
    (structural : certificate.StructurallyWellFormed)
    (cycle : certificate.fullGraph.EdgeSimpleCycle)
    {after : List certificate.fullGraph.DirectedEdge}
    {middle partner last : certificate.fullGraph.DirectedEdge}
    (cycleSteps : cycle.traversed = middle :: partner :: after)
    (cusp : certificate.Cusp middle partner)
    (later : certificate.CuspFreeContinuation middle last)
    (hit : last.target = middle.source)
    (uniqueIntersection : ∀ vertex,
      vertex ∈ later.path.vertices.tail →
      vertex ∈ cycle.vertices → vertex = last.target)
    (cycleClosingFree : ¬certificate.ClosingCusp cycle)
    (minimal : ∀ other : certificate.fullGraph.EdgeSimpleCycle,
      other.start = cycle.start → ¬certificate.ClosingCusp other →
      certificate.cuspCount cycle.traversed ≤
        certificate.cuspCount other.traversed) : False := by
  have middleMembership : middle ∈ cycle.traversed := by
    rw [cycleSteps]
    simp
  have partnerMembership : partner ∈ cycle.traversed := by
    rw [cycleSteps]
    simp
  have fullChain := cycle.walk.toChain
  rw [cycleSteps] at fullChain
  have middleSource : middle.source = cycle.start := fullChain.head_source
  have cuspMeeting : middle.target = partner.source := by
    cases fullChain with
    | cons _middle middleStarts middleTail =>
        cases middleTail with
        | cons _partner partnerStarts partnerTail =>
            exact partnerStarts.symm
  have cycleHeadOption : cycle.traversed.head? = some middle := by
    rw [cycleSteps]
    simp
  have cycleHead : cycle.traversed.head cycle.nonempty = middle :=
    List.head_of_head?_eq_some cycleHeadOption
  have oldTailNonempty : partner :: after ≠ [] := by simp
  have cycleLastOption : cycle.traversed.getLast? =
      some ((partner :: after).getLast oldTailNonempty) := by
    rw [cycleSteps, List.getLast?_eq_some_getLast (by simp :
      middle :: partner :: after ≠ [])]
    exact congrArg some (List.getLast_cons oldTailNonempty)
  have cycleLast : cycle.traversed.getLast cycle.nonempty =
      (partner :: after).getLast oldTailNonempty :=
    List.getLast_of_getLast?_eq_some cycleLastOption
  have oldCount : certificate.cuspCount cycle.traversed =
      certificate.cuspCount (partner :: after) + 1 := by
    rw [cycleSteps]
    simp [cuspCount, cusp, Nat.add_comm]
  by_cases endpointFree : ¬certificate.Cusp last middle
  · have oneEdgeSteps : cycle.traversed =
        ([] : List certificate.fullGraph.DirectedEdge) ++
          middle :: partner :: after := by
      simpa using cycleSteps
    rcases cycle.prefixPath oneEdgeSteps with
      ⟨returnPath, returnStartsAtBase, returnFinishesAtMiddle,
        returnSteps⟩
    have returnNonempty : returnPath.traversed ≠ [] := by
      simp [returnSteps]
    have returnStarts : returnPath.start = last.target :=
      returnStartsAtBase.trans (middleSource.symm.trans hit.symm)
    have returnFinishes : returnPath.finish = later.path.start :=
      returnFinishesAtMiddle.trans later.startsAt.symm
    have returnEdgeDirectedSubset : ∀ directed,
        directed ∈ returnPath.traversed → directed ∈ cycle.traversed := by
      intro directed membership
      rw [returnSteps] at membership
      simp at membership
      subst directed
      exact middleMembership
    have returnVertexSubset : ∀ vertex,
        vertex ∈ returnPath.vertices → vertex ∈ cycle.vertices := by
      apply cycle.path_vertices_subset returnPath
      · rw [returnStartsAtBase, ← middleSource]
        exact (cycle.directed_endpoints_mem_vertices middleMembership).1
      · exact returnEdgeDirectedSubset
    have returnEdgeSubset : ∀ index,
        index ∈ returnPath.traversed.map Graph.DirectedEdge.index →
          index ∈ cycle.traversed.map Graph.DirectedEdge.index := by
      intro index membership
      rcases List.mem_map.mp membership with
        ⟨directed, directedMembership, indexEquation⟩
      exact List.mem_map.mpr
        ⟨directed, returnEdgeDirectedSubset directed directedMembership,
          indexEquation⟩
    rcases CuspFreeContinuation.firstIntersection_withCycle_cycle structural
        cycle later middleMembership partnerMembership cuspMeeting cusp
        returnPath returnNonempty returnStarts returnFinishes
        returnVertexSubset returnEdgeSubset uniqueIntersection with
      ⟨closed, _closedStarts, closedSteps⟩
    have closedDecomposition : closed.traversed =
        later.path.traversed ++ middle :: [] := by
      rw [closedSteps, returnSteps]
      simp
    rcases closed.rotateAt_exists closedDecomposition with
      ⟨based, basedStartsAtMiddle, basedSteps⟩
    have basedStarts : based.start = cycle.start :=
      basedStartsAtMiddle.trans middleSource
    have basedHeadOption : based.traversed.head? = some middle := by
      rw [basedSteps]
      simp
    have basedHead : based.traversed.head based.nonempty = middle :=
      List.head_of_head?_eq_some basedHeadOption
    have basedLastOption : based.traversed.getLast? = some last := by
      rw [basedSteps, List.getLast?_append,
        List.getLast?_eq_some_getLast later.nonempty, later.lastEdge]
      rfl
    have basedLast : based.traversed.getLast based.nonempty = last :=
      List.getLast_of_getLast?_eq_some basedLastOption
    have basedClosingFree : ¬certificate.ClosingCusp based := by
      intro closing
      unfold ClosingCusp at closing
      rw [basedLast, basedHead] at closing
      exact endpointFree closing
    have joinFree : ¬certificate.Cusp
        (([middle] : List certificate.fullGraph.DirectedEdge).getLast (by simp))
        (later.path.traversed.head later.nonempty) := by
      simpa using later.initialFree
    have basedCount : certificate.cuspCount based.traversed = 0 := by
      rw [basedSteps, certificate.cuspCount_append,
        certificate.cuspCount_eq_zero_of_free later.cuspFree,
        certificate.cuspBoundaryCount_eq_zero (by simp) later.nonempty
          joinFree]
      simp [cuspCount]
    have bound := minimal based basedStarts basedClosingFree
    rw [oldCount, basedCount] at bound
    omega
  · have endpointCusp : certificate.Cusp last middle :=
      Classical.byContradiction (fun absent => endpointFree absent)
    let reversedAfter := Graph.EdgeWalk.reverseTraversal after
    have reverseSteps : cycle.reverse.traversed =
        reversedAfter ++ partner.reverse :: middle.reverse :: [] := by
      change Graph.EdgeWalk.reverseTraversal cycle.traversed = _
      rw [cycleSteps]
      simp [Graph.EdgeSimpleCycle.reverse, Graph.EdgeWalk.reverseTraversal,
        reversedAfter, List.map_append, List.append_assoc]
    rcases cycle.reverse.prefixPath reverseSteps with
      ⟨returnPath, returnStartsAtBase, returnFinishesAtPartner,
        returnSteps⟩
    have returnNonempty : returnPath.traversed ≠ [] := by
      simp [returnSteps]
    have returnStarts : returnPath.start = last.target := by
      exact returnStartsAtBase.trans (middleSource.symm.trans hit.symm)
    have returnFinishes : returnPath.finish = later.path.start := by
      rw [returnFinishesAtPartner, Graph.DirectedEdge.reverse_target]
      exact cuspMeeting.symm.trans later.startsAt.symm
    have returnEdgeDirectedSubsetReverse : ∀ directed,
        directed ∈ returnPath.traversed →
          directed ∈ cycle.reverse.traversed := by
      intro directed membership
      have regrouped : cycle.reverse.traversed =
          (reversedAfter ++ [partner.reverse]) ++ [middle.reverse] := by
        simpa [List.append_assoc] using reverseSteps
      rw [regrouped]
      exact List.mem_append.mpr (.inl (by
        simpa [returnSteps] using membership))
    have returnStartInReverse : returnPath.start ∈ cycle.reverse.vertices := by
      rw [returnStartsAtBase]
      simp [Graph.EdgeSimpleCycle.vertices, Graph.EdgeWalk.visitedVertices]
    have returnVertexSubset : ∀ vertex,
        vertex ∈ returnPath.vertices → vertex ∈ cycle.vertices := by
      intro vertex membership
      apply (cycle.mem_reverse_vertices_iff vertex).mp
      exact cycle.reverse.path_vertices_subset returnPath returnStartInReverse
        returnEdgeDirectedSubsetReverse vertex membership
    have returnEdgeSubset : ∀ index,
        index ∈ returnPath.traversed.map Graph.DirectedEdge.index →
          index ∈ cycle.traversed.map Graph.DirectedEdge.index := by
      intro index membership
      rcases List.mem_map.mp membership with
        ⟨directed, directedMembership, indexEquation⟩
      have inReverse : index ∈
          cycle.reverse.traversed.map Graph.DirectedEdge.index :=
        List.mem_map.mpr ⟨directed,
          returnEdgeDirectedSubsetReverse directed directedMembership,
          indexEquation⟩
      simpa [Graph.EdgeSimpleCycle.reverse, Graph.EdgeWalk.reverseTraversal,
        List.map_map, Function.comp_def] using inReverse
    rcases CuspFreeContinuation.firstIntersection_withCycle_cycle structural
        cycle later middleMembership partnerMembership cuspMeeting cusp
        returnPath returnNonempty returnStarts returnFinishes
        returnVertexSubset returnEdgeSubset uniqueIntersection with
      ⟨closed, _closedStarts, closedSteps⟩
    cases returnEquation : returnPath.traversed with
    | nil => exact False.elim (returnNonempty returnEquation)
    | cons firstReturn returnRest =>
        have closedDecomposition : closed.traversed =
            later.path.traversed ++ firstReturn :: returnRest := by
          rw [closedSteps, returnEquation]
        rcases closed.rotateAt_exists closedDecomposition with
          ⟨based, basedStartsAtReturn, basedStepsRaw⟩
        have firstReturnSource : firstReturn.source = returnPath.start := by
          have chain := returnPath.walk.toChain
          rw [returnEquation] at chain
          exact chain.head_source
        have basedStarts : based.start = cycle.start :=
          basedStartsAtReturn.trans
            (firstReturnSource.trans returnStartsAtBase)
        have basedSteps : based.traversed =
            returnPath.traversed ++ later.path.traversed := by
          rw [returnEquation]
          simpa using basedStepsRaw
        have returnStepsExact : returnPath.traversed =
            Graph.EdgeWalk.reverseTraversal (partner :: after) := by
          rw [returnSteps]
          simp [reversedAfter, Graph.EdgeWalk.reverseTraversal,
            List.map_append, List.append_assoc]
        have returnHead : returnPath.traversed.head returnNonempty =
            ((partner :: after).getLast oldTailNonempty).reverse := by
          have optionEquation : returnPath.traversed.head? =
              some ((partner :: after).getLast oldTailNonempty).reverse := by
            rw [returnStepsExact,
              List.head?_eq_some_head (by
                simpa [Graph.EdgeWalk.reverseTraversal] using oldTailNonempty)]
            exact congrArg some
              (Graph.EdgeWalk.head_reverseTraversal (partner :: after)
                oldTailNonempty)
          exact List.head_of_head?_eq_some optionEquation
        have endpointReverseFree : ¬certificate.Cusp last
            ((partner :: after).getLast oldTailNonempty).reverse := by
          intro bad
          apply cycleClosingFree
          unfold ClosingCusp at ⊢
          rw [cycleLast, cycleHead]
          unfold Cusp at endpointCusp bad ⊢
          rw [Graph.DirectedEdge.reverse_reverse] at bad
          exact bad.symm.trans endpointCusp
        have basedHeadOption : based.traversed.head? =
            some (returnPath.traversed.head returnNonempty) := by
          rw [basedSteps, List.head?_append,
            List.head?_eq_some_head returnNonempty]
          rfl
        have basedHead : based.traversed.head based.nonempty =
            returnPath.traversed.head returnNonempty :=
          List.head_of_head?_eq_some basedHeadOption
        have basedLastOption : based.traversed.getLast? = some last := by
          rw [basedSteps, List.getLast?_append,
            List.getLast?_eq_some_getLast later.nonempty, later.lastEdge]
          rfl
        have basedLast : based.traversed.getLast based.nonempty = last :=
          List.getLast_of_getLast?_eq_some basedLastOption
        have basedClosingFree : ¬certificate.ClosingCusp based := by
          intro closing
          unfold ClosingCusp at closing
          rw [basedLast, basedHead, returnHead] at closing
          exact endpointReverseFree closing
        have returnLast : returnPath.traversed.getLast returnNonempty =
            partner.reverse := by
          have optionEquation : returnPath.traversed.getLast? =
              some partner.reverse := by
            rw [returnStepsExact,
              List.getLast?_eq_some_getLast (by
                simpa [Graph.EdgeWalk.reverseTraversal] using oldTailNonempty)]
            rw [Graph.EdgeWalk.getLast_reverseTraversal
              (partner :: after) oldTailNonempty]
            simp
          exact List.getLast_of_getLast?_eq_some optionEquation
        have joinFree : ¬certificate.Cusp
            (returnPath.traversed.getLast returnNonempty)
            (later.path.traversed.head later.nonempty) := by
          rw [returnLast]
          intro bad
          apply later.initialFree
          unfold Cusp at cusp bad ⊢
          exact cusp.trans bad
        have boundaryZero : certificate.cuspBoundaryCount
            returnPath.traversed later.path.traversed = 0 :=
          certificate.cuspBoundaryCount_eq_zero returnNonempty
            later.nonempty joinFree
        have basedCount : certificate.cuspCount based.traversed =
            certificate.cuspCount (partner :: after) := by
          rw [basedSteps, certificate.cuspCount_append,
            boundaryZero,
            returnStepsExact,
            certificate.cuspCount_reverseTraversal (partner :: after),
            certificate.cuspCount_eq_zero_of_free later.cuspFree]
          simp
        have bound := minimal based basedStarts basedClosingFree
        rw [oldCount, basedCount] at bound
        omega

/-- Symmetric bungee contradiction when the first cycle intersection lies
after the selected cusp. -/
theorem CuspAcyclic.no_minimal_bungee_afterCusp
    (certificate : Certificate) (acyclic : certificate.CuspAcyclic)
    (structural : certificate.StructurallyWellFormed)
    (cycle : certificate.fullGraph.EdgeSimpleCycle)
    {initial between suffix : List certificate.fullGraph.DirectedEdge}
    {middle partner outgoingAtHit last :
      certificate.fullGraph.DirectedEdge}
    (cycleSteps : cycle.traversed =
      initial ++ middle :: partner :: between ++ outgoingAtHit :: suffix)
    (cusp : certificate.Cusp middle partner)
    (later : certificate.CuspFreeContinuation middle last)
    (hit : last.target = outgoingAtHit.source)
    (uniqueIntersection : ∀ vertex,
      vertex ∈ later.path.vertices.tail →
      vertex ∈ cycle.vertices → vertex = last.target)
    (cycleClosingFree : ¬certificate.ClosingCusp cycle)
    (minimal : ∀ other : certificate.fullGraph.EdgeSimpleCycle,
      other.start = cycle.start → ¬certificate.ClosingCusp other →
      certificate.cuspCount cycle.traversed ≤
        certificate.cuspCount other.traversed) : False := by
  rcases CuspFreeContinuation.bungee_afterCusp_exactSameBaseCycle
      structural cycle cycleSteps cusp later hit uniqueIntersection with
    ⟨based, basedStarts, basedSteps⟩
  have basedClosingFree :=
    certificate.bungee_afterCusp_exactSameBase_closingFree cycle based later
      cycleSteps basedSteps cycleClosingFree
  have minimalBound := minimal based basedStarts basedClosingFree
  rcases certificate.bungee_afterCusp_minimal_count_constraints cycle based
      later cycleSteps basedSteps cusp minimalBound with
    ⟨oldArcFree, _oldExitFree, _newExitCusp⟩
  have joinFree := certificate.bungee_afterCusp_joinFree_of_minimal
    cycle based later cycleSteps basedSteps cusp minimalBound
  rcases cycle.segmentBeforeAfterCuspHit cycleSteps with
    ⟨oldPath, oldStarts, oldFinishes, oldSteps, oldVertexSubset,
      oldEdgeSubset⟩
  let returnPath := oldPath.reverse
  have oldNonempty : oldPath.traversed ≠ [] := by
    simp [oldSteps]
  have oldArcNonempty : partner :: between ≠ [] := by simp
  have oldLastOption : oldPath.traversed.getLast? =
      some ((partner :: between).getLast oldArcNonempty) := by
    rw [oldSteps, List.getLast?_eq_some_getLast oldArcNonempty]
  have oldLast : oldPath.traversed.getLast oldNonempty =
      (partner :: between).getLast oldArcNonempty :=
    List.getLast_of_getLast?_eq_some oldLastOption
  have oldHeadOption : oldPath.traversed.head? = some partner := by
    rw [oldSteps]
    simp
  have oldHead : oldPath.traversed.head oldNonempty = partner :=
    List.head_of_head?_eq_some oldHeadOption
  have returnNonempty : returnPath.traversed ≠ [] := by
    simp [returnPath, Graph.EdgeSimplePath.reverse,
      Graph.EdgeWalk.reverseTraversal, oldNonempty]
  have cuspMeeting : middle.target = partner.source := by
    have fullChain := cycle.walk.toChain
    rw [cycleSteps] at fullChain
    have regrouped : certificate.fullGraph.EdgeChain cycle.start
        (initial ++ (middle :: partner :: between ++
          outgoingAtHit :: suffix)) cycle.start := by
      simpa [List.append_assoc] using fullChain
    rcases regrouped.split_append with
      ⟨splitVertex, _initialChain, suffixChain⟩
    cases suffixChain with
    | cons _middle middleStarts middleTail =>
        cases middleTail with
        | cons _partner partnerStarts partnerTail =>
            exact partnerStarts.symm
  have returnStarts : returnPath.start = last.target := by
    change oldPath.finish = last.target
    exact oldFinishes.trans hit.symm
  have returnFinishes : returnPath.finish = later.path.start := by
    change oldPath.start = later.path.start
    exact oldStarts.trans (cuspMeeting.symm.trans later.startsAt.symm)
  have returnVertexSubset : ∀ vertex,
      vertex ∈ returnPath.vertices → vertex ∈ cycle.vertices := by
    intro vertex membership
    apply oldVertexSubset vertex
    simpa [returnPath] using membership
  have returnEdgeSubset : ∀ index,
      index ∈ returnPath.traversed.map Graph.DirectedEdge.index →
      index ∈ cycle.traversed.map Graph.DirectedEdge.index := by
    intro index membership
    apply oldEdgeSubset index
    simpa [returnPath, Graph.EdgeSimplePath.reverse,
      Graph.EdgeWalk.reverseTraversal, List.map_map, Function.comp_def] using
      membership
  have middleMembership : middle ∈ cycle.traversed := by
    rw [cycleSteps]
    simp
  have partnerMembership : partner ∈ cycle.traversed := by
    rw [cycleSteps]
    simp
  rcases CuspFreeContinuation.firstIntersection_withCycle_cycle structural
      cycle later middleMembership partnerMembership cuspMeeting cusp
      returnPath returnNonempty returnStarts returnFinishes returnVertexSubset
      returnEdgeSubset uniqueIntersection with
    ⟨closed, _closedStarts, closedSteps⟩
  have oldTraversalFree : certificate.CuspFreeTraversal oldPath.traversed := by
    rw [oldSteps]
    exact oldArcFree
  have returnTraversalFree : certificate.CuspFreeTraversal
      returnPath.traversed := by
    change certificate.CuspFreeTraversal
      (Graph.EdgeWalk.reverseTraversal oldPath.traversed)
    exact (certificate.cuspFreeTraversal_reverse_iff oldPath.traversed).2
      oldTraversalFree
  have returnHead : returnPath.traversed.head returnNonempty =
      ((partner :: between).getLast (by simp)).reverse := by
    change (Graph.EdgeWalk.reverseTraversal oldPath.traversed).head _ = _
    calc
      (Graph.EdgeWalk.reverseTraversal oldPath.traversed).head _ =
          (oldPath.traversed.getLast oldNonempty).reverse :=
        Graph.EdgeWalk.head_reverseTraversal oldPath.traversed oldNonempty
      _ = ((partner :: between).getLast oldArcNonempty).reverse :=
        congrArg Graph.DirectedEdge.reverse oldLast
  have listJoinFree : ¬certificate.Cusp
      (later.path.traversed.getLast later.nonempty)
      (returnPath.traversed.head returnNonempty) := by
    rw [later.lastEdge, returnHead]
    exact joinFree
  have closedTraversalFree : certificate.CuspFreeTraversal
      closed.traversed := by
    rw [closedSteps]
    exact CuspFreeTraversal.append certificate later.cuspFree
      returnTraversalFree later.nonempty returnNonempty listJoinFree
  have returnLast : returnPath.traversed.getLast returnNonempty =
      partner.reverse := by
    change (Graph.EdgeWalk.reverseTraversal oldPath.traversed).getLast _ = _
    calc
      (Graph.EdgeWalk.reverseTraversal oldPath.traversed).getLast _ =
          (oldPath.traversed.head oldNonempty).reverse :=
        Graph.EdgeWalk.getLast_reverseTraversal oldPath.traversed oldNonempty
      _ = partner.reverse := congrArg Graph.DirectedEdge.reverse oldHead
  have closedLastOption : closed.traversed.getLast? = some partner.reverse := by
    rw [closedSteps, List.getLast?_append,
      List.getLast?_eq_some_getLast returnNonempty, returnLast]
    rfl
  have closedLast : closed.traversed.getLast closed.nonempty =
      partner.reverse :=
    List.getLast_of_getLast?_eq_some closedLastOption
  have closedHeadOption : closed.traversed.head? =
      some (later.path.traversed.head later.nonempty) := by
    rw [closedSteps, List.head?_append,
      List.head?_eq_some_head later.nonempty]
    rfl
  have closedHead : closed.traversed.head closed.nonempty =
      later.path.traversed.head later.nonempty :=
    List.head_of_head?_eq_some closedHeadOption
  have closedClosingFree : ¬certificate.ClosingCusp closed := by
    intro closing
    unfold ClosingCusp at closing
    rw [closedLast, closedHead] at closing
    apply later.initialFree
    unfold Cusp at cusp closing ⊢
    exact cusp.trans closing
  have closedFree := (certificate.cuspFreeCycle_iff closed).2
    ⟨closedTraversalFree, closedClosingFree⟩
  exact acyclic closed closedFree

/-- A first intersection at the source of the selected incoming cusp edge is
also impossible.  At the old base this is the preceding theorem.  With a
nonempty old prefix, reversing the ambient cycle moves the hit strictly after
the reversed selected cusp, where `no_minimal_bungee_afterCusp` applies. -/
theorem CuspAcyclic.no_minimal_bungee_atIncoming
    (certificate : Certificate) (acyclic : certificate.CuspAcyclic)
    (structural : certificate.StructurallyWellFormed)
    (cycle : certificate.fullGraph.EdgeSimpleCycle)
    {initial after : List certificate.fullGraph.DirectedEdge}
    {middle partner last : certificate.fullGraph.DirectedEdge}
    (cycleSteps : cycle.traversed =
      initial ++ middle :: partner :: after)
    (cusp : certificate.Cusp middle partner)
    (later : certificate.CuspFreeContinuation middle last)
    (hit : last.target = middle.source)
    (uniqueIntersection : ∀ vertex,
      vertex ∈ later.path.vertices.tail →
      vertex ∈ cycle.vertices → vertex = last.target)
    (cycleClosingFree : ¬certificate.ClosingCusp cycle)
    (minimal : ∀ other : certificate.fullGraph.EdgeSimpleCycle,
      other.start = cycle.start → ¬certificate.ClosingCusp other →
      certificate.cuspCount cycle.traversed ≤
        certificate.cuspCount other.traversed) : False := by
  by_cases initialEmpty : initial = []
  · subst initial
    have baseSteps : cycle.traversed = middle :: partner :: after := by
      simpa using cycleSteps
    exact certificate.no_minimal_bungee_atIncoming_base structural cycle
      baseSteps cusp later hit uniqueIntersection cycleClosingFree minimal
  · have fullChain := cycle.walk.toChain
    rw [cycleSteps] at fullChain
    have regrouped : certificate.fullGraph.EdgeChain cycle.start
        (initial ++ (middle :: partner :: after)) cycle.start := by
      simpa [List.append_assoc] using fullChain
    rcases regrouped.split_append with
      ⟨splitVertex, _initialChain, suffixChain⟩
    have cuspMeeting : middle.target = partner.source := by
      cases suffixChain with
      | cons _middle middleStarts middleTail =>
          cases middleTail with
          | cons _partner partnerStarts partnerTail =>
              exact partnerStarts.symm
    rcases cycle.prefixBefore cycleSteps with
      ⟨prefixPath, prefixStarts, prefixFinishes, prefixSteps,
        _prefixSubset⟩
    let reversedAfter := Graph.EdgeWalk.reverseTraversal after
    let reversedInitial := Graph.EdgeWalk.reverseTraversal initial
    have reversedInitialNonempty : reversedInitial ≠ [] := by
      simpa [reversedInitial, Graph.EdgeWalk.reverseTraversal] using initialEmpty
    have reverseFullSteps : cycle.reverse.traversed =
        reversedAfter ++ partner.reverse :: middle.reverse ::
          reversedInitial := by
      change Graph.EdgeWalk.reverseTraversal cycle.traversed = _
      rw [cycleSteps]
      simp [Graph.EdgeWalk.reverseTraversal, reversedAfter, reversedInitial,
        List.map_append, List.append_assoc]
    cases reversedInitialEquation : reversedInitial with
    | nil => exact reversedInitialNonempty reversedInitialEquation
    | cons outgoingAtHit suffix =>
        have reversedCycleSteps : cycle.reverse.traversed =
            reversedAfter ++ partner.reverse :: middle.reverse ::
              ([] : List certificate.fullGraph.DirectedEdge) ++
                outgoingAtHit :: suffix := by
          rw [reverseFullSteps, reversedInitialEquation]
          simp
        have reversedPrefixChain := prefixPath.reverse.walk.toChain
        change certificate.fullGraph.EdgeChain prefixPath.finish
          (Graph.EdgeWalk.reverseTraversal prefixPath.traversed)
            prefixPath.start at reversedPrefixChain
        rw [prefixSteps] at reversedPrefixChain
        change certificate.fullGraph.EdgeChain prefixPath.finish
          reversedInitial prefixPath.start at reversedPrefixChain
        rw [reversedInitialEquation] at reversedPrefixChain
        have outgoingSource : outgoingAtHit.source = middle.source :=
          reversedPrefixChain.head_source.trans prefixFinishes
        have reversedHit : last.target = outgoingAtHit.source :=
          hit.trans outgoingSource.symm
        let reversedLater := later.rebaseAtReversedPartner cuspMeeting cusp
        have reverseCusp : certificate.Cusp partner.reverse middle.reverse :=
          (certificate.cusp_reverse_iff middle partner).mp cusp
        have reverseUnique : ∀ vertex,
            vertex ∈ reversedLater.path.vertices.tail →
            vertex ∈ cycle.reverse.vertices →
              vertex = last.target := by
          intro vertex inLater inReverse
          apply uniqueIntersection vertex inLater
          exact (cycle.mem_reverse_vertices_iff vertex).mp inReverse
        have reverseClosingFree :
            ¬certificate.ClosingCusp cycle.reverse := by
          intro reverseClosing
          exact cycleClosingFree
            ((certificate.closingCusp_reverse_iff cycle).mp reverseClosing)
        have reverseMinimal : ∀ other :
            certificate.fullGraph.EdgeSimpleCycle,
            other.start = cycle.reverse.start →
            ¬certificate.ClosingCusp other →
            certificate.cuspCount cycle.reverse.traversed ≤
              certificate.cuspCount other.traversed := by
          intro other otherStarts otherClosingFree
          have originalBound := minimal other (by
            simpa [Graph.EdgeSimpleCycle.reverse] using otherStarts)
            otherClosingFree
          change certificate.cuspCount
              (Graph.EdgeWalk.reverseTraversal cycle.traversed) ≤
            certificate.cuspCount other.traversed
          rw [certificate.cuspCount_reverseTraversal cycle.traversed]
          exact originalBound
        exact acyclic.no_minimal_bungee_afterCusp certificate structural
          cycle.reverse reversedCycleSteps reverseCusp reversedLater
          reversedHit reverseUnique reverseClosingFree reverseMinimal

/-- Exhaustive first-intersection classifier for the bungee argument.  The
unique cycle occurrence leaving the hit lies either in the old prefix, at the
selected incoming edge, at its partner, or in the old suffix.  The first,
second, and fourth positions are discharged by the three bungee theorems; the
partner position would revisit the continuation's own start. -/
theorem CuspAcyclic.no_minimal_bungee
    (certificate : Certificate) (acyclic : certificate.CuspAcyclic)
    (structural : certificate.StructurallyWellFormed)
    (cycle : certificate.fullGraph.EdgeSimpleCycle)
    {initial after : List certificate.fullGraph.DirectedEdge}
    {middle partner last : certificate.fullGraph.DirectedEdge}
    (cycleSteps : cycle.traversed =
      initial ++ middle :: partner :: after)
    (cusp : certificate.Cusp middle partner)
    (later : certificate.CuspFreeContinuation middle last)
    (hitInCycle : last.target ∈ cycle.vertices)
    (uniqueIntersection : ∀ vertex,
      vertex ∈ later.path.vertices.tail →
      vertex ∈ cycle.vertices → vertex = last.target)
    (cycleClosingFree : ¬certificate.ClosingCusp cycle)
    (minimal : ∀ other : certificate.fullGraph.EdgeSimpleCycle,
      other.start = cycle.start → ¬certificate.ClosingCusp other →
      certificate.cuspCount cycle.traversed ≤
        certificate.cuspCount other.traversed) : False := by
  have hitSourceMembership : last.target ∈
      cycle.traversed.map Graph.DirectedEdge.source := by
    simpa [cycle.sources_eq_vertices] using hitInCycle
  rcases List.mem_map.mp hitSourceMembership with
    ⟨outgoingAtHit, outgoingMembership, sourceEquation⟩
  have hit : last.target = outgoingAtHit.source := sourceEquation.symm
  have fullChain := cycle.walk.toChain
  rw [cycleSteps] at fullChain
  have regrouped : certificate.fullGraph.EdgeChain cycle.start
      (initial ++ (middle :: partner :: after)) cycle.start := by
    simpa [List.append_assoc] using fullChain
  rcases regrouped.split_append with
    ⟨splitVertex, _initialChain, suffixChain⟩
  have cuspMeeting : middle.target = partner.source := by
    cases suffixChain with
    | cons _middle middleStarts middleTail =>
        cases middleTail with
        | cons _partner partnerStarts partnerTail =>
            exact partnerStarts.symm
  rw [cycleSteps, List.mem_append] at outgoingMembership
  rcases outgoingMembership with inInitial | inCuspAndAfter
  · rcases List.mem_iff_append.mp inInitial with
      ⟨before, between, initialSteps⟩
    have positionedSteps : cycle.traversed =
        before ++ outgoingAtHit :: between ++ middle :: partner :: after := by
      rw [cycleSteps, initialSteps]
    exact acyclic.no_minimal_bungee_firstIntersection certificate structural
      cycle positionedSteps cusp later hit uniqueIntersection cycleClosingFree
      minimal
  · simp only [List.mem_cons] at inCuspAndAfter
    rcases inCuspAndAfter with atMiddle | atPartner | inAfter
    · subst outgoingAtHit
      exact acyclic.no_minimal_bungee_atIncoming certificate structural cycle
        cycleSteps cusp later hit uniqueIntersection cycleClosingFree minimal
    · subst outgoingAtHit
      have lastMembership : last ∈ later.path.traversed := by
        have membership := List.getLast_mem later.nonempty
        rw [later.lastEdge] at membership
        exact membership
      have lastTargetInTail : last.target ∈ later.path.vertices.tail := by
        change last.target ∈
          later.path.traversed.map Graph.DirectedEdge.target
        exact List.mem_map.mpr ⟨last, lastMembership, rfl⟩
      have atStart : last.target = later.path.start :=
        sourceEquation.symm.trans
          (cuspMeeting.symm.trans later.startsAt.symm)
      apply later.path.start_not_mem_vertices_tail
      rw [← atStart]
      exact lastTargetInTail
    · rcases List.mem_iff_append.mp inAfter with
        ⟨between, suffix, afterSteps⟩
      have positionedSteps : cycle.traversed =
          initial ++ middle :: partner :: between ++ outgoingAtHit :: suffix := by
        rw [cycleSteps, afterSteps]
        simp [List.append_assoc]
      exact acyclic.no_minimal_bungee_afterCusp certificate structural cycle
        positionedSteps cusp later hit uniqueIntersection cycleClosingFree
        minimal

/-- The cusp-free prefix ending at a selected cusp edge on a minimal freely
closing cycle satisfies the universal separation field of `OrderingPath`.
Any violating later continuation is truncated at its first cycle intersection
and then contradicts the exhaustive bungee theorem. -/
def CuspFreeContinuation.toOrderingPathOfMinimalCycle
    {certificate : Certificate}
    (acyclic : certificate.CuspAcyclic)
    (structural : certificate.StructurallyWellFormed)
    {incoming middle partner : certificate.fullGraph.DirectedEdge}
    (first : certificate.CuspFreeContinuation incoming middle)
    (cycle : certificate.fullGraph.EdgeSimpleCycle)
    {initial after : List certificate.fullGraph.DirectedEdge}
    (cycleSteps : cycle.traversed =
      initial ++ middle :: partner :: after)
    (cusp : certificate.Cusp middle partner)
    (firstSubset : ∀ vertex,
      vertex ∈ first.path.vertices → vertex ∈ cycle.vertices)
    (cycleClosingFree : ¬certificate.ClosingCusp cycle)
    (minimal : ∀ other : certificate.fullGraph.EdgeSimpleCycle,
      other.start = cycle.start → ¬certificate.ClosingCusp other →
      certificate.cuspCount cycle.traversed ≤
        certificate.cuspCount other.traversed) :
    certificate.OrderingPath incoming middle := by
  refine { first with separated := ?_ }
  intro last later vertex inFirst inLater
  have inCycle := firstSubset vertex inFirst
  have intersects : ∃ candidate,
      candidate ∈ later.path.vertices.tail ∧
        candidate ∈ cycle.vertices := ⟨vertex, inLater, inCycle⟩
  rcases later.prefixToFirstIntersection cycle.vertices intersects with
    ⟨lastAtHit, truncated, hitInCycle, uniqueIntersection⟩
  exact acyclic.no_minimal_bungee certificate structural cycle cycleSteps cusp
    truncated hitInCycle uniqueIntersection cycleClosingFree minimal

/-- In the simple cycle produced by first-intersection normalization, the
transition from the later prefix into the old return suffix must be a cusp.
Otherwise both pieces and both closing boundaries are cusp-free, contradicting
colored acyclicity directly. -/
theorem CuspAcyclic.firstIntersection_boundary_cusp
    (certificate : Certificate) (acyclic : certificate.CuspAcyclic)
    {incoming middle last : certificate.fullGraph.DirectedEdge}
    (first : certificate.CuspFreeContinuation incoming middle)
    (later : certificate.CuspFreeContinuation middle last)
    (returnPath : certificate.fullGraph.EdgeSimplePath)
    (returnStarts : returnPath.start = last.target)
    (returnFinishes : returnPath.finish = middle.target)
    (returnSubset : ∀ candidate, candidate ∈ returnPath.vertices →
      candidate ∈ first.path.vertices)
    (returnFree : certificate.CuspFreeTraversal returnPath.traversed)
    (uniqueIntersection : ∀ vertex,
      vertex ∈ later.path.vertices.tail →
      vertex ∈ first.path.vertices → vertex = last.target)
    (returnLast : returnPath.traversed.getLast? = some middle) :
    certificate.Cusp last
      (returnPath.traversed.head (by
        intro empty
        simp [empty] at returnLast)) := by
  have returnNonempty : returnPath.traversed ≠ [] := by
    intro empty
    simp [empty] at returnLast
  rcases CuspFreeContinuation.firstIntersection_cycle first later returnPath
      returnStarts returnFinishes returnSubset uniqueIntersection returnLast with
    ⟨cycle, cycleSteps⟩
  apply Classical.byContradiction
  intro boundaryFree
  have joinFree : ¬certificate.Cusp
      (later.path.traversed.getLast later.nonempty)
      (returnPath.traversed.head returnNonempty) := by
    rw [later.lastEdge]
    exact boundaryFree
  have traversalFree : certificate.CuspFreeTraversal cycle.traversed := by
    rw [cycleSteps]
    exact CuspFreeTraversal.append certificate later.cuspFree returnFree
      later.nonempty returnNonempty joinFree
  have cycleLast : cycle.traversed.getLast cycle.nonempty = middle := by
    have cycleLastOption : cycle.traversed.getLast? = some middle := by
      rw [cycleSteps, List.getLast?_append, returnLast]
      rfl
    exact List.getLast_of_getLast?_eq_some cycleLastOption
  have cycleHead : cycle.traversed.head cycle.nonempty =
      later.path.traversed.head later.nonempty := by
    have cycleHeadOption : cycle.traversed.head? =
        some (later.path.traversed.head later.nonempty) := by
      rw [cycleSteps, List.head?_append,
        List.head?_eq_some_head later.nonempty]
      rfl
    exact List.head_of_head?_eq_some cycleHeadOption
  have closingFree : ¬certificate.ClosingCusp cycle := by
    intro closing
    unfold ClosingCusp at closing
    rw [cycleLast, cycleHead] at closing
    exact later.initialFree closing
  exact acyclic cycle ((certificate.cuspFreeCycle_iff cycle).2
    ⟨traversalFree, closingFree⟩)

/-- The normalized first-intersection cycle has exactly one internal cusp: the
forced splice cusp. -/
theorem CuspAcyclic.firstIntersection_cycle_cuspCount
    (certificate : Certificate) (acyclic : certificate.CuspAcyclic)
    {incoming middle last : certificate.fullGraph.DirectedEdge}
    (first : certificate.CuspFreeContinuation incoming middle)
    (later : certificate.CuspFreeContinuation middle last)
    (returnPath : certificate.fullGraph.EdgeSimplePath)
    (returnStarts : returnPath.start = last.target)
    (returnFinishes : returnPath.finish = middle.target)
    (returnSubset : ∀ candidate, candidate ∈ returnPath.vertices →
      candidate ∈ first.path.vertices)
    (returnFree : certificate.CuspFreeTraversal returnPath.traversed)
    (uniqueIntersection : ∀ vertex,
      vertex ∈ later.path.vertices.tail →
      vertex ∈ first.path.vertices → vertex = last.target)
    (returnLast : returnPath.traversed.getLast? = some middle) :
    ∃ cycle : certificate.fullGraph.EdgeSimpleCycle,
      certificate.cuspCount cycle.traversed = 1 := by
  have returnNonempty : returnPath.traversed ≠ [] := by
    intro empty
    simp [empty] at returnLast
  rcases CuspFreeContinuation.firstIntersection_cycle first later returnPath
      returnStarts returnFinishes returnSubset uniqueIntersection returnLast with
    ⟨cycle, cycleSteps⟩
  have boundary := acyclic.firstIntersection_boundary_cusp certificate first
    later returnPath returnStarts returnFinishes returnSubset returnFree
    uniqueIntersection returnLast
  have listBoundary : certificate.Cusp
      (later.path.traversed.getLast later.nonempty)
      (returnPath.traversed.head returnNonempty) := by
    rw [later.lastEdge]
    exact boundary
  refine ⟨cycle, ?_⟩
  rw [cycleSteps, certificate.cuspCount_append,
    certificate.cuspCount_eq_zero_of_free later.cuspFree,
    certificate.cuspCount_eq_zero_of_free returnFree,
    certificate.cuspBoundaryCount_eq_one later.nonempty returnNonempty
      listBoundary]

/-- A colored splitting vertex is one at which every based simple cycle closes
with a cusp. This is the representation-independent target of generalized
Yeo; later lemmas relate it to terminal tensor component separation. -/
def SplittingVertex (certificate : Certificate) (vertex : Vertex) : Prop :=
  ∀ cycle : certificate.fullGraph.EdgeSimpleCycle,
    cycle.start = vertex → certificate.ClosingCusp cycle

/-- A directed occurrence participates nontrivially in a local cusp. -/
def CuspingEdge (certificate : Certificate)
    (incoming : certificate.fullGraph.DirectedEdge) : Prop :=
  ∃ outgoing, certificate.Cusp incoming outgoing ∧
    incoming ≠ outgoing.reverse

/-- A nontrivially cusping occurrence necessarily carries a shared par color.
Two unique colors can agree only when both the stored occurrence index and its
orientation agree, which would make the purported partner the immediate
reverse excluded by `CuspingEdge`. -/
theorem CuspingEdge.incidenceColor_eq_par
    {certificate : Certificate}
    {incoming : certificate.fullGraph.DirectedEdge}
    (cusping : certificate.CuspingEdge incoming) :
    ∃ conclusion,
      certificate.incidenceColor incoming = .par conclusion := by
  rcases cusping with ⟨outgoing, cusp, different⟩
  apply Classical.byContradiction
  intro noParExists
  have incomingNotPar : ∀ conclusion,
      certificate.incidenceColor incoming ≠ .par conclusion := by
    intro conclusion equality
    exact noParExists ⟨conclusion, equality⟩
  have incomingUnique := certificate.incidenceColor_eq_unique_of_not_par
    incoming incomingNotPar
  have outgoingNotPar : ∀ conclusion,
      certificate.incidenceColor outgoing.reverse ≠ .par conclusion := by
    intro conclusion equality
    apply incomingNotPar conclusion
    unfold Cusp at cusp
    exact cusp.trans equality
  have outgoingUnique := certificate.incidenceColor_eq_unique_of_not_par
    outgoing.reverse outgoingNotPar
  unfold Cusp at cusp
  rw [incomingUnique, outgoingUnique] at cusp
  have sameIndex : incoming.index = outgoing.reverse.index := by
    injection cusp
  have sameForward : incoming.forward = outgoing.reverse.forward := by
    injection cusp
  exact different (Graph.DirectedEdge.eq_of_index_eq_of_forward_eq
    incoming outgoing.reverse sameIndex sameForward)

/-- Exact representation bridge for cusping occurrences: the occurrence is a
stored premise-to-conclusion edge of a concrete par link and its directed
target is that par conclusion. -/
theorem CuspingEdge.par_origin
    {certificate : Certificate}
    {incoming : certificate.fullGraph.DirectedEdge}
    (cusping : certificate.CuspingEdge incoming) :
    ∃ left right conclusion,
      Link.par left right conclusion ∈ certificate.links ∧
        incoming.target = conclusion ∧
        (incoming.edge = { first := left, second := conclusion } ∨
          incoming.edge = { first := right, second := conclusion }) := by
  rcases cusping.incidenceColor_eq_par with ⟨conclusion, color⟩
  have colorData :=
    (certificate.incidenceColor_eq_par_iff incoming conclusion).mp color
  have annotation : certificate.fullEdgeAnnotations[incoming.index]? =
      some (incoming.edge, some conclusion) :=
    certificate.fullEdgeAnnotation_lookup_iff.mpr
      ⟨incoming.lookup, colorData.2⟩
  rcases certificate.fullEdgeAnnotation_some_par_origin annotation with
    ⟨left, right, membership, edgeShape⟩
  have edgeSecond : incoming.edge.second = conclusion :=
    certificate.fullEdgeAnnotation_some_second annotation
  have target : incoming.target = conclusion := by
    simp [Graph.DirectedEdge.target, colorData.1, edgeSecond]
  exact ⟨left, right, conclusion, membership, target, edgeShape⟩

/-- Representation-specific carrier used by parametrized generalized Yeo:
positive occurrences aimed at the conclusion produced by a tensor or par
link.  Unlike the set of cusping occurrences, this carrier is also closed
under moving from a non-boundary connective conclusion to its parent link. -/
def SequentializationEdge (certificate : Certificate)
    (directed : certificate.fullGraph.DirectedEdge) : Prop :=
  directed.forward = true ∧
    ∃ link ∈ certificate.links, link.produces directed.target = true

/-- Every nontrivially cusping occurrence belongs to the parametrized-Yeo
sequentialization carrier. -/
theorem CuspingEdge.sequentializationEdge
    {certificate : Certificate}
    {incoming : certificate.fullGraph.DirectedEdge}
    (cusping : certificate.CuspingEdge incoming) :
    certificate.SequentializationEdge incoming := by
  rcases cusping.incidenceColor_eq_par with ⟨colorTarget, color⟩
  have forward :=
    (certificate.incidenceColor_eq_par_iff incoming colorTarget).mp color |>.1
  rcases cusping.par_origin with
    ⟨left, right, conclusion, membership, target, _edgeShape⟩
  refine ⟨forward, .par left right conclusion, membership, ?_⟩
  simp [Link.produces, target]

/-- A non-boundary connective occurrence has an exact forward parent
occurrence in the sequentialization carrier.  Node ownership supplies the
unique parent link; aligned tensor/par annotations supply its stored edge
index without conflating parallel equal-valued edges. -/
theorem parent_sequentializationEdge_exists
    {certificate : Certificate} (structural : certificate.StructurallyWellFormed)
    {vertex : Vertex} (inBounds : vertex < certificate.formulas.size)
    (notBoundary : vertex ∉ certificate.conclusions) :
    ∃ parent : certificate.fullGraph.DirectedEdge,
      parent.source = vertex ∧ certificate.SequentializationEdge parent := by
  have node := structural.2.2.2.2.2 vertex inBounds
  have parentCount : certificate.parentUseCount vertex = 1 := by
    simpa [Certificate.NodeWellFormed, notBoundary] using node.2
  unfold parentUseCount at parentCount
  rcases List.length_eq_one_iff.mp parentCount with
    ⟨parentLink, parentFilterEquation⟩
  have parentFiltered : parentLink ∈ certificate.links.filter
      (·.usesAsPremise vertex) := by
    rw [parentFilterEquation]
    simp
  rcases List.mem_filter.mp parentFiltered with
    ⟨parentMembership, parentUses⟩
  have premiseMembership : vertex ∈ parentLink.premises := by
    simpa [Link.usesAsPremise] using parentUses
  have parentWellFormed :=
    structural.2.2.2.2.1 parentLink parentMembership
  cases parentLink with
  | «axiom» first second => simp [Link.premises] at premiseMembership
  | tensor left right conclusion =>
      simp [Link.premises] at premiseMembership
      rcases certificate.tensor_incidenceColors_exist parentMembership
          parentWellFormed.1 with
        ⟨leftIncidence, rightIncidence, leftSource, _leftTarget, rightSource,
          _rightTarget, leftColor, rightColor, _different⟩
      have leftForward : leftIncidence.forward = true := by
        cases forward : leftIncidence.forward
        · simp [incidenceColor, forward] at leftColor
        · rfl
      have rightForward : rightIncidence.forward = true := by
        cases forward : rightIncidence.forward
        · simp [incidenceColor, forward] at rightColor
        · rfl
      rcases premiseMembership with rfl | rfl
      · refine ⟨leftIncidence, leftSource, leftForward,
          .tensor vertex right conclusion,
          parentMembership, ?_⟩
        simp [Link.produces, _leftTarget]
      · refine ⟨rightIncidence, rightSource, rightForward,
          .tensor left vertex conclusion,
          parentMembership, ?_⟩
        simp [Link.produces, _rightTarget]
  | par left right conclusion =>
      simp [Link.premises] at premiseMembership
      rcases certificate.par_incidenceColors_exist parentMembership with
        ⟨leftIncidence, rightIncidence, leftSource, _leftTarget, rightSource,
          _rightTarget, leftColor, rightColor⟩
      have leftForward :=
        (certificate.incidenceColor_eq_par_iff leftIncidence conclusion).mp
          leftColor |>.1
      have rightForward :=
        (certificate.incidenceColor_eq_par_iff rightIncidence conclusion).mp
          rightColor |>.1
      rcases premiseMembership with rfl | rfl
      · refine ⟨leftIncidence, leftSource, leftForward,
          .par vertex right conclusion,
          parentMembership, ?_⟩
        simp [Link.produces, _leftTarget]
      · refine ⟨rightIncidence, rightSource, rightForward,
          .par left vertex conclusion,
          parentMembership, ?_⟩
        simp [Link.produces, _rightTarget]

/-- At a forward outgoing occurrence, the only incoming occurrence that can
form a cusp with it is its exact reverse.  The proof uses occurrence index and
orientation, so equal-valued parallel edges remain distinct. -/
theorem cusp_eq_reverse_of_outgoing_forward
    (certificate : Certificate)
    (incoming outgoing : certificate.fullGraph.DirectedEdge)
    (outgoingForward : outgoing.forward = true)
    (cusp : certificate.Cusp incoming outgoing) :
    incoming = outgoing.reverse := by
  have outgoingColor : certificate.incidenceColor outgoing.reverse =
      .unique outgoing.index false := by
    simp [incidenceColor, Graph.DirectedEdge.reverse, outgoingForward]
  have incomingNotPar : ∀ conclusion,
      certificate.incidenceColor incoming ≠ .par conclusion := by
    intro conclusion incomingPar
    have impossible : LocalSwitchingColor.par conclusion =
        .unique outgoing.index false :=
      incomingPar.symm.trans (cusp.trans outgoingColor)
    cases impossible
  have incomingColor := certificate.incidenceColor_eq_unique_of_not_par
    incoming incomingNotPar
  unfold Cusp at cusp
  rw [incomingColor, outgoingColor] at cusp
  have sameIndex : incoming.index = outgoing.index := by
    injection cusp
  have incomingFalse : incoming.forward = false := by
    injection cusp
  apply Graph.DirectedEdge.eq_of_index_eq_of_forward_eq incoming
    outgoing.reverse
  · simpa using sameIndex
  · simpa [Graph.DirectedEdge.reverse, outgoingForward] using incomingFalse

/-- The exact parent occurrence of a sequentialization edge gives a one-edge
cusp-free continuation.  Its source and target are distinct by structural
looplessness, and the initial transition is free because both carrier edges
are forward while a cusp into a forward edge would force reversal. -/
def SequentializationEdge.parentContinuation
    {certificate : Certificate} (structural : certificate.StructurallyWellFormed)
    {incoming parent : certificate.fullGraph.DirectedEdge}
    (incomingEdge : certificate.SequentializationEdge incoming)
    (parentSource : parent.source = incoming.target)
    (parentEdge : certificate.SequentializationEdge parent) :
    certificate.CuspFreeContinuation incoming parent := by
  have endpointsDifferent := certificate.fullDirectedEdge_loopless structural parent
  let path : certificate.fullGraph.EdgeSimplePath :=
    { start := incoming.target
      finish := parent.target
      traversed := [parent]
      walk := by
        simpa using Graph.EdgeWalk.step (.refl incoming.target) parent
          parentSource rfl
      verticesNodup := by
        change (incoming.target :: parent.target :: []).Nodup
        have sourceTarget : incoming.target ≠ parent.target := by
          intro same
          apply endpointsDifferent
          exact parentSource.trans same
        simp [sourceTarget] }
  refine
    { path := path
      nonempty := by simp [path]
      startsAt := rfl
      endsAt := rfl
      cuspFree := by simp [path, CuspFreeTraversal]
      initialFree := ?_
      lastEdge := by simp [path] }
  intro cusp
  have reversed := certificate.cusp_eq_reverse_of_outgoing_forward
    incoming parent parentEdge.1 cusp
  have orientations := congrArg Graph.DirectedEdge.forward reversed
  rw [incomingEdge.1] at orientations
  simp [Graph.DirectedEdge.reverse, parentEdge.1] at orientations

/-- Parametrized-Yeo terminality step in the formula-occurrence
representation.  Moving from a non-boundary connective conclusion to its
exact parent occurrence is a strict `EdgeOrdering` step.  Any violation of the
one-edge path's universal separation clause would close with a prefix of the
later continuation to form a forbidden cusp-free exact cycle. -/
theorem CuspAcyclic.ordering_to_parent
    (certificate : Certificate) (acyclic : certificate.CuspAcyclic)
    (structural : certificate.StructurallyWellFormed)
    {incoming parent : certificate.fullGraph.DirectedEdge}
    (incomingEdge : certificate.SequentializationEdge incoming)
    (parentSource : parent.source = incoming.target)
    (parentEdge : certificate.SequentializationEdge parent) :
    certificate.EdgeOrdering incoming parent := by
  let first := incomingEdge.parentContinuation structural parentSource parentEdge
  have firstSteps : first.path.traversed = [parent] := rfl
  have firstVertices : first.path.vertices = [incoming.target, parent.target] := by
    simp [Graph.EdgeSimplePath.vertices, Graph.EdgeWalk.visitedVertices,
      firstSteps, first.startsAt]
  refine ⟨{ first with separated := ?_ }⟩
  intro later continuation vertex inFirst inLater
  have vertexCases : vertex = incoming.target ∨ vertex = parent.target := by
    simpa [firstVertices] using inFirst
  rcases vertexCases with atBase | atParentTarget
  · subst vertex
    rcases continuation.prefixToTailVertex inLater with
      ⟨last, ⟨returning⟩, lastTarget⟩
    have meeting : first.path.finish = returning.path.start :=
      first.endsAt.trans returning.startsAt.symm
    have closing : returning.path.finish = first.path.start :=
      returning.endsAt.trans (lastTarget.trans first.startsAt.symm)
    have vertexDisjoint : ∀ candidate,
        candidate ∈ first.path.vertices →
        candidate ∈ returning.path.vertices.tail.dropLast → False := by
      intro candidate inFirstPath inReturnInterior
      have candidateCases : candidate = incoming.target ∨
          candidate = parent.target := by
        simpa [firstVertices] using inFirstPath
      rcases candidateCases with candidateBase | candidateParent
      · subst candidate
        apply returning.path.finish_not_mem_vertices_tail_dropLast
          returning.nonempty
        rw [returning.endsAt, lastTarget]
        exact inReturnInterior
      · subst candidate
        apply returning.path.start_not_mem_vertices_tail
        rw [returning.startsAt]
        exact Graph.mem_of_mem_dropLast inReturnInterior
    have edgeDisjoint : ∀ index,
        index ∈ first.path.traversed.map Graph.DirectedEdge.index →
        index ∈ returning.path.traversed.map Graph.DirectedEdge.index →
          False := by
      intro index inFirstIndices inReturnIndices
      have indexParent : index = parent.index := by
        simpa [firstSteps] using inFirstIndices
      rcases List.mem_map.mp inReturnIndices with
        ⟨directed, directedMembership, directedIndex⟩
      have sameIndex : directed.index = parent.index :=
        directedIndex.trans indexParent
      rcases Graph.DirectedEdge.eq_or_eq_reverse_of_index_eq
          directed parent sameIndex with same | reversed
      · apply returning.path.directed_source_ne_finish returning.nonempty
          directedMembership
        calc
          directed.source = parent.source := congrArg _ same
          _ = incoming.target := parentSource
          _ = last.target := lastTarget.symm
          _ = returning.path.finish := returning.endsAt.symm
      · let head := returning.path.traversed.head returning.nonempty
        have headMembership : head ∈ returning.path.traversed :=
          List.head_mem returning.nonempty
        have sameSource : directed.source = head.source := by
          calc
            directed.source = parent.reverse.source := congrArg _ reversed
            _ = parent.target := Graph.DirectedEdge.reverse_source parent
            _ = returning.path.start := returning.startsAt.symm
            _ = head.source := (returning.path.head_source
              returning.nonempty).symm
        have directedIsHead := returning.path.eq_of_source_eq
          directedMembership headMembership sameSource
        have initialFree : ¬certificate.Cusp parent head := by
          simpa [head] using returning.initialFree
        apply initialFree
        rw [← directedIsHead, reversed]
        simp [Cusp]
    let closed := Graph.EdgeSimpleCycle.ofTwoPaths first.path returning.path
      first.nonempty returning.nonempty meeting closing vertexDisjoint
        edgeDisjoint
    have closedSteps : closed.traversed =
        first.path.traversed ++ returning.path.traversed := rfl
    have traversalFree : certificate.CuspFreeTraversal closed.traversed := by
      rw [closedSteps]
      apply CuspFreeTraversal.append certificate first.cuspFree
        returning.cuspFree first.nonempty returning.nonempty
      rw [first.lastEdge]
      exact returning.initialFree
    let returnLast := returning.path.traversed.getLast returning.nonempty
    have closingPairFree : ¬certificate.Cusp returnLast parent := by
      intro cusp
      have reversed := certificate.cusp_eq_reverse_of_outgoing_forward
        returnLast parent parentEdge.1 cusp
      apply edgeDisjoint parent.index
      · simp [firstSteps]
      · exact List.mem_map.mpr
          ⟨returnLast, List.getLast_mem returning.nonempty, by
            simpa [returnLast] using congrArg Graph.DirectedEdge.index reversed⟩
    have closedHeadOption : closed.traversed.head? = some parent := by
      rw [closedSteps, firstSteps]
      simp
    have closedHead : closed.traversed.head closed.nonempty = parent :=
      List.head_of_head?_eq_some closedHeadOption
    have closedLastOption : closed.traversed.getLast? = some returnLast := by
      rw [closedSteps, List.getLast?_append,
        List.getLast?_eq_some_getLast returning.nonempty]
      rfl
    have closedLast : closed.traversed.getLast closed.nonempty = returnLast :=
      List.getLast_of_getLast?_eq_some closedLastOption
    have closingFree : ¬certificate.ClosingCusp closed := by
      intro cusp
      unfold ClosingCusp at cusp
      rw [closedLast, closedHead] at cusp
      exact closingPairFree cusp
    exact acyclic closed ((certificate.cuspFreeCycle_iff closed).2
      ⟨traversalFree, closingFree⟩)
  · subst vertex
    apply continuation.path.start_not_mem_vertices_tail
    rw [continuation.startsAt]
    exact inLater

theorem SequentializationEdge.target_in_bounds
    {certificate : Certificate} (structural : certificate.StructurallyWellFormed)
    {directed : certificate.fullGraph.DirectedEdge}
    (sequentialization : certificate.SequentializationEdge directed) :
    directed.target < certificate.formulas.size := by
  rcases sequentialization.2 with ⟨link, membership, produces⟩
  have wellFormed := structural.2.2.2.2.1 link membership
  cases link with
  | «axiom» left right => simp [Link.produces] at produces
  | tensor left right conclusion =>
      have target : conclusion = directed.target := by
        simpa [Link.produces] using produces
      rw [← target]
      exact wellFormed.2.2.2.2.2.1
  | par left right conclusion =>
      have target : conclusion = directed.target := by
        simpa [Link.produces] using produces
      rw [← target]
      exact wellFormed.2.2.2.2.2.1

/-- Non-terminality of a carrier edge yields a strict carrier successor: its
unique parent occurrence. -/
theorem CuspAcyclic.ordering_of_sequentializationEdge_not_terminal
    (certificate : Certificate) (acyclic : certificate.CuspAcyclic)
    (structural : certificate.StructurallyWellFormed)
    {incoming : certificate.fullGraph.DirectedEdge}
    (incomingEdge : certificate.SequentializationEdge incoming)
    (notTerminal : incoming.target ∉ certificate.conclusions) :
    ∃ parent : certificate.fullGraph.DirectedEdge,
      certificate.EdgeOrdering incoming parent ∧
        certificate.SequentializationEdge parent := by
  have inBounds := incomingEdge.target_in_bounds structural
  rcases certificate.parent_sequentializationEdge_exists structural inBounds
      notTerminal with ⟨parent, parentSource, parentEdge⟩
  exact ⟨parent, acyclic.ordering_to_parent certificate structural incomingEdge
    parentSource parentEdge, parentEdge⟩

/-- Any stored connective supplies a concrete member of the parametrized-Yeo
carrier. -/
theorem sequentializationEdge_exists_of_connective
    {certificate : Certificate} (structural : certificate.StructurallyWellFormed)
    (connectiveExists : ∃ link ∈ certificate.links,
      link.isConnective = true) :
    ∃ directed : certificate.fullGraph.DirectedEdge,
      certificate.SequentializationEdge directed := by
  rcases connectiveExists with ⟨link, membership, connective⟩
  have wellFormed := structural.2.2.2.2.1 link membership
  cases link with
  | «axiom» left right => simp [Link.isConnective] at connective
  | tensor left right conclusion =>
      rcases certificate.tensor_incidenceColors_exist membership
          wellFormed.1 with
        ⟨leftIncidence, _rightIncidence, _leftSource, leftTarget,
          _rightSource, _rightTarget, leftColor, _rightColor, _different⟩
      have leftForward : leftIncidence.forward = true := by
        cases forward : leftIncidence.forward
        · simp [incidenceColor, forward] at leftColor
        · rfl
      refine ⟨leftIncidence, leftForward, .tensor left right conclusion,
        membership, ?_⟩
      simp [Link.produces, leftTarget]
  | par left right conclusion =>
      rcases certificate.par_incidenceColors_exist membership with
        ⟨leftIncidence, _rightIncidence, _leftSource, leftTarget,
          _rightSource, _rightTarget, leftColor, _rightColor⟩
      have leftForward :=
        (certificate.incidenceColor_eq_par_iff leftIncidence conclusion).mp
          leftColor |>.1
      refine ⟨leftIncidence, leftForward, .par left right conclusion,
        membership, ?_⟩
      simp [Link.produces, leftTarget]

theorem not_splittingVertex_witness (certificate : Certificate)
    {vertex : Vertex} (notSplitting : ¬certificate.SplittingVertex vertex) :
    ∃ cycle : certificate.fullGraph.EdgeSimpleCycle,
      cycle.start = vertex ∧ ¬certificate.ClosingCusp cycle := by
  classical
  apply Classical.byContradiction
  intro noWitness
  apply notSplitting
  intro cycle starts
  apply Classical.byContradiction
  intro notClosing
  exact noWitness ⟨cycle, starts, notClosing⟩

/-- Among all simple cycles based at a non-splitting vertex whose closing pair
is free, one has a minimal finite number of internal cusps. -/
theorem exists_minimal_nonclosing_cycle (certificate : Certificate)
    {vertex : Vertex} (notSplitting : ¬certificate.SplittingVertex vertex) :
    ∃ cycle : certificate.fullGraph.EdgeSimpleCycle,
      cycle.start = vertex ∧
      ¬certificate.ClosingCusp cycle ∧
      ∀ other : certificate.fullGraph.EdgeSimpleCycle,
        other.start = vertex → ¬certificate.ClosingCusp other →
          certificate.cuspCount cycle.traversed ≤
            certificate.cuspCount other.traversed := by
  let property : Nat → Prop := fun count =>
    ∃ cycle : certificate.fullGraph.EdgeSimpleCycle,
      cycle.start = vertex ∧ ¬certificate.ClosingCusp cycle ∧
        certificate.cuspCount cycle.traversed = count
  rcases certificate.not_splittingVertex_witness notSplitting with
    ⟨witness, starts, closingFree⟩
  have propertyExists : ∃ count, property count :=
    ⟨certificate.cuspCount witness.traversed,
      witness, starts, closingFree, rfl⟩
  rcases exists_least_nat property propertyExists with
    ⟨least, ⟨cycle, cycleStarts, cycleClosingFree, cycleCount⟩,
      leastBound⟩
  refine ⟨cycle, cycleStarts, cycleClosingFree, ?_⟩
  intro other otherStarts otherClosingFree
  rw [cycleCount]
  exact leastBound _ ⟨other, otherStarts, otherClosingFree, rfl⟩

/-- A minimal freely closing cycle can be oriented relative to an incoming
edge without changing its internal cusp count. -/
theorem exists_minimal_oriented_nonclosing_cycle (certificate : Certificate)
    (incoming : certificate.fullGraph.DirectedEdge)
    (notSplitting :
      ¬certificate.SplittingVertex incoming.target) :
    ∃ cycle : certificate.fullGraph.EdgeSimpleCycle,
      cycle.start = incoming.target ∧
      ¬certificate.ClosingCusp cycle ∧
      ¬certificate.Cusp incoming
        (cycle.traversed.head cycle.nonempty) ∧
      ∀ other : certificate.fullGraph.EdgeSimpleCycle,
        other.start = incoming.target →
        ¬certificate.ClosingCusp other →
        certificate.cuspCount cycle.traversed ≤
          certificate.cuspCount other.traversed := by
  rcases certificate.exists_minimal_nonclosing_cycle notSplitting with
    ⟨cycle, starts, closingFree, minimal⟩
  rcases certificate.orient_cycle_initial_free cycle closingFree incoming with
    ⟨oriented, sameStart, orientedClosingFree, initialFree, sameCount⟩
  refine ⟨oriented, sameStart.trans starts, orientedClosingFree,
    initialFree, ?_⟩
  intro other otherStarts otherClosingFree
  rw [sameCount]
  exact minimal other otherStarts otherClosingFree

theorem CuspAcyclic.minimal_nonclosing_cycle_has_cusp
    (certificate : Certificate) (acyclic : certificate.CuspAcyclic)
    {cycle : certificate.fullGraph.EdgeSimpleCycle}
    (closingFree : ¬certificate.ClosingCusp cycle) :
    0 < certificate.cuspCount cycle.traversed := by
  have notZero : certificate.cuspCount cycle.traversed ≠ 0 := by
    intro zero
    have traversalFree :=
      (certificate.cuspCount_eq_zero_iff cycle.traversed).mp zero
    exact acyclic cycle ((certificate.cuspFreeCycle_iff cycle).2
      ⟨traversalFree, closingFree⟩)
  omega

/-- Following a freely oriented non-splitting cycle up to its first internal
cusp yields a simple cusp-free continuation from the prescribed incoming edge
to a nontrivial cusping edge. The generalized-Yeo separation condition is the
remaining strengthening needed to turn this continuation into `EdgeOrdering`.
-/
theorem CuspAcyclic.continuation_to_first_cusping_edge
    (certificate : Certificate) (acyclic : certificate.CuspAcyclic)
    (incoming : certificate.fullGraph.DirectedEdge)
    (cycle : certificate.fullGraph.EdgeSimpleCycle)
    (startsAt : cycle.start = incoming.target)
    (closingFree : ¬certificate.ClosingCusp cycle)
    (initialFree : ¬certificate.Cusp incoming
      (cycle.traversed.head cycle.nonempty)) :
    ∃ cusping : certificate.fullGraph.DirectedEdge,
      Nonempty (certificate.CuspFreeContinuation incoming cusping) ∧
        certificate.CuspingEdge cusping := by
  have traversalNotFree :
      ¬certificate.CuspFreeTraversal cycle.traversed := by
    intro traversalFree
    exact acyclic cycle ((certificate.cuspFreeCycle_iff cycle).2
      ⟨traversalFree, closingFree⟩)
  rcases CuspFreeTraversal.exists_first_cusp_of_not_free certificate
      traversalNotFree with
    ⟨before, cusping, outgoing, after, traversalEquation,
      cusp, prefixFree⟩
  rcases cycle.prefixPath traversalEquation with
    ⟨path, pathStarts, pathFinishes, pathSteps⟩
  have pathNonempty : path.traversed ≠ [] := by
    rw [pathSteps]
    simp
  have prefixNonempty : before ++ [cusping] ≠ [] := by simp
  have headEquation : path.traversed.head pathNonempty =
      cycle.traversed.head cycle.nonempty := by
    simpa only [pathSteps, traversalEquation, List.append_assoc,
      List.singleton_append] using
      (List.head_append_of_ne_nil
        (l := before ++ [cusping]) (l' := outgoing :: after)
        (w₁ := by simp)
        prefixNonempty).symm
  have lastEquation : path.traversed.getLast pathNonempty = cusping := by
    simp [pathSteps]
  have differentIndex : cusping.index ≠ outgoing.index := by
    intro sameIndex
    have indicesNodup := cycle.edgeIndicesNodup
    rw [traversalEquation] at indicesNodup
    simp only [List.map_append, List.map_cons] at indicesNodup
    rw [sameIndex] at indicesNodup
    have suffixNodup :
        (outgoing.index :: outgoing.index ::
          after.map Graph.DirectedEdge.index).Nodup :=
      (List.nodup_append.mp indicesNodup).2.1
    exact (List.nodup_cons.mp suffixNodup).1 (by simp)
  have differentReverse : cusping ≠ outgoing.reverse := by
    intro same
    apply differentIndex
    simpa using congrArg Graph.DirectedEdge.index same
  refine ⟨cusping, ⟨?_⟩, outgoing, cusp, differentReverse⟩
  exact
    { path := path
      nonempty := pathNonempty
      startsAt := pathStarts.trans startsAt
      endsAt := pathFinishes
      cuspFree := by simpa [pathSteps] using prefixFree
      initialFree := by simpa [headEquation] using initialFree
      lastEdge := lastEquation }

/-- A cusp-acyclic non-splitting target already yields the unseparated
continuation part of the generalized-Yeo order. The bungee lemma is precisely
the remaining proof that a minimal choice also satisfies `OrderingPath`'s
universal separation field. -/
theorem CuspAcyclic.continuation_of_not_splitting
    (certificate : Certificate) (acyclic : certificate.CuspAcyclic)
    (incoming : certificate.fullGraph.DirectedEdge)
    (notSplitting :
      ¬certificate.SplittingVertex incoming.target) :
    ∃ cusping : certificate.fullGraph.DirectedEdge,
      Nonempty (certificate.CuspFreeContinuation incoming cusping) ∧
        certificate.CuspingEdge cusping := by
  rcases certificate.exists_minimal_oriented_nonclosing_cycle incoming
      notSplitting with
    ⟨cycle, starts, closingFree, initialFree, _minimal⟩
  exact CuspAcyclic.continuation_to_first_cusping_edge certificate acyclic
    incoming cycle starts closingFree initialFree

/-- Strengthened generalized-Yeo step: a cusp-acyclic non-splitting target
produces a genuine strict `EdgeOrdering` successor that is itself a cusping
edge.  The universal separation proof is supplied by the completed bungee
classifier, not assumed as an extra hypothesis. -/
theorem CuspAcyclic.ordering_of_not_splitting
    (certificate : Certificate) (acyclic : certificate.CuspAcyclic)
    (structural : certificate.StructurallyWellFormed)
    (incoming : certificate.fullGraph.DirectedEdge)
    (notSplitting :
      ¬certificate.SplittingVertex incoming.target) :
    ∃ cusping : certificate.fullGraph.DirectedEdge,
      certificate.EdgeOrdering incoming cusping ∧
        certificate.CuspingEdge cusping := by
  rcases certificate.exists_minimal_oriented_nonclosing_cycle incoming
      notSplitting with
    ⟨cycle, startsAt, closingFree, initialFree, minimal⟩
  have traversalNotFree :
      ¬certificate.CuspFreeTraversal cycle.traversed := by
    intro traversalFree
    exact acyclic cycle ((certificate.cuspFreeCycle_iff cycle).2
      ⟨traversalFree, closingFree⟩)
  rcases CuspFreeTraversal.exists_first_cusp_of_not_free certificate
      traversalNotFree with
    ⟨before, cusping, outgoing, after, traversalEquation,
      cusp, prefixFree⟩
  rcases cycle.prefixPath traversalEquation with
    ⟨path, pathStarts, pathFinishes, pathSteps⟩
  have pathNonempty : path.traversed ≠ [] := by
    rw [pathSteps]
    simp
  have prefixNonempty : before ++ [cusping] ≠ [] := by simp
  have headEquation : path.traversed.head pathNonempty =
      cycle.traversed.head cycle.nonempty := by
    simpa only [pathSteps, traversalEquation, List.append_assoc,
      List.singleton_append] using
      (List.head_append_of_ne_nil
        (l := before ++ [cusping]) (l' := outgoing :: after)
        (w₁ := by simp) prefixNonempty).symm
  have lastEquation : path.traversed.getLast pathNonempty = cusping := by
    simp [pathSteps]
  let first : certificate.CuspFreeContinuation incoming cusping :=
    { path := path
      nonempty := pathNonempty
      startsAt := pathStarts.trans startsAt
      endsAt := pathFinishes
      cuspFree := by simpa [pathSteps] using prefixFree
      initialFree := by simpa [headEquation] using initialFree
      lastEdge := lastEquation }
  have pathEdgeSubset : ∀ directed,
      directed ∈ path.traversed → directed ∈ cycle.traversed := by
    intro directed membership
    have grouped : cycle.traversed =
        (before ++ [cusping]) ++ outgoing :: after := by
      simpa [List.append_assoc] using traversalEquation
    rw [grouped]
    exact List.mem_append.mpr (.inl (by
      simpa [pathSteps] using membership))
  have pathStartInCycle : path.start ∈ cycle.vertices := by
    rw [pathStarts]
    simp [Graph.EdgeSimpleCycle.vertices]
  have firstSubset : ∀ vertex,
      vertex ∈ first.path.vertices → vertex ∈ cycle.vertices := by
    intro vertex membership
    exact cycle.path_vertices_subset path pathStartInCycle pathEdgeSubset
      vertex membership
  have minimalAtCycle : ∀ other : certificate.fullGraph.EdgeSimpleCycle,
      other.start = cycle.start → ¬certificate.ClosingCusp other →
      certificate.cuspCount cycle.traversed ≤
        certificate.cuspCount other.traversed := by
    intro other otherStarts otherClosingFree
    exact minimal other (otherStarts.trans startsAt) otherClosingFree
  let ordering := first.toOrderingPathOfMinimalCycle acyclic structural cycle
    traversalEquation cusp firstSubset closingFree minimalAtCycle
  have differentIndex : cusping.index ≠ outgoing.index := by
    intro sameIndex
    have indicesNodup := cycle.edgeIndicesNodup
    rw [traversalEquation] at indicesNodup
    simp only [List.map_append, List.map_cons] at indicesNodup
    rw [sameIndex] at indicesNodup
    have suffixNodup :
        (outgoing.index :: outgoing.index ::
          after.map Graph.DirectedEdge.index).Nodup :=
      (List.nodup_append.mp indicesNodup).2.1
    exact (List.nodup_cons.mp suffixNodup).1 (by simp)
  have differentReverse : cusping ≠ outgoing.reverse := by
    intro same
    apply differentIndex
    simpa using congrArg Graph.DirectedEdge.index same
  exact ⟨cusping, ⟨ordering⟩, outgoing, cusp, differentReverse⟩

/-- Parametrized generalized Yeo on the representation-specific carrier.
Every cusping occurrence lies in the carrier, and every non-terminal carrier
target has a strict carrier successor. Therefore a finite maximal carrier
occurrence targets a vertex that is both colored-splitting and on the public
boundary. -/
theorem CuspAcyclic.exists_terminal_splitting_target
    (certificate : Certificate) (acyclic : certificate.CuspAcyclic)
    (structural : certificate.StructurallyWellFormed)
    (connectiveExists : ∃ link ∈ certificate.links,
      link.isConnective = true) :
    ∃ maximal : certificate.fullGraph.DirectedEdge,
      certificate.SequentializationEdge maximal ∧
        maximal.target ∈ certificate.conclusions ∧
        certificate.SplittingVertex maximal.target := by
  classical
  letI : BEq certificate.fullGraph.DirectedEdge :=
    ⟨fun first second => decide (first = second)⟩
  letI : LawfulBEq certificate.fullGraph.DirectedEdge := inferInstance
  let values : List certificate.fullGraph.DirectedEdge :=
    certificate.fullGraph.directedEdges.eraseDups.filter fun directed =>
      decide (certificate.SequentializationEdge directed)
  have valuesNodup : values.Nodup := by
    exact (eraseDups_nodup_generic
      certificate.fullGraph.directedEdges).filter _
  rcases certificate.sequentializationEdge_exists_of_connective structural
      connectiveExists with ⟨seed, seedEdge⟩
  have seedInValues : seed ∈ values := by
    simp [values, seed.mem_directedEdges, seedEdge]
  have valuesNonempty : values ≠ [] := by
    intro empty
    rw [empty] at seedInValues
    simp at seedInValues
  rcases exists_relation_maximal values valuesNodup valuesNonempty
      certificate.EdgeOrdering
      (fun value => EdgeOrdering.irrefl certificate value)
      (fun {_first _middle _last} firstMiddle middleLast =>
        EdgeOrdering.transitive certificate firstMiddle middleLast) with
    ⟨maximal, maximalInValues, noSuccessor⟩
  have maximalEdge : certificate.SequentializationEdge maximal := by
    have filtered := List.mem_filter.mp maximalInValues
    exact of_decide_eq_true filtered.2
  have maximalTerminal : maximal.target ∈ certificate.conclusions := by
    apply Classical.byContradiction
    intro notTerminal
    rcases acyclic.ordering_of_sequentializationEdge_not_terminal certificate
        structural maximalEdge notTerminal with
      ⟨successor, ordering, successorEdge⟩
    have successorInValues : successor ∈ values := by
      simp [values, successor.mem_directedEdges, successorEdge]
    exact noSuccessor successor successorInValues ordering
  have maximalSplitting : certificate.SplittingVertex maximal.target := by
    apply Classical.byContradiction
    intro notSplitting
    rcases acyclic.ordering_of_not_splitting certificate structural maximal
        notSplitting with
      ⟨successor, ordering, successorCusping⟩
    have successorEdge := successorCusping.sequentializationEdge
    have successorInValues : successor ∈ values := by
      simp [values, successor.mem_directedEdges, successorEdge]
    exact noSuccessor successor successorInValues ordering
  exact ⟨maximal, maximalEdge, maximalTerminal, maximalSplitting⟩

/-- Generalized-Yeo maximality consequence for a nonempty edge-colored graph.
Both orientations of every stored edge form a finite carrier.  A maximal
`EdgeOrdering` occurrence cannot point to a non-splitting vertex, since the
preceding theorem would construct a strict successor in the same carrier. -/
theorem CuspAcyclic.exists_splittingVertex_of_directedEdge
    (certificate : Certificate) (acyclic : certificate.CuspAcyclic)
    (structural : certificate.StructurallyWellFormed)
    (seed : certificate.fullGraph.DirectedEdge) :
    ∃ vertex, certificate.SplittingVertex vertex := by
  classical
  letI : BEq certificate.fullGraph.DirectedEdge :=
    ⟨fun first second => decide (first = second)⟩
  letI : LawfulBEq certificate.fullGraph.DirectedEdge := inferInstance
  let values : List certificate.fullGraph.DirectedEdge :=
    certificate.fullGraph.directedEdges.eraseDups
  have valuesNodup : values.Nodup := by
    exact eraseDups_nodup_generic _
  have seedInValues : seed ∈ values := by
    simpa only [values, List.mem_eraseDups] using seed.mem_directedEdges
  have valuesNonempty : values ≠ [] := by
    intro empty
    rw [empty] at seedInValues
    simp at seedInValues
  rcases exists_relation_maximal values valuesNodup valuesNonempty
      certificate.EdgeOrdering
      (fun value => EdgeOrdering.irrefl certificate value)
      (fun {_first _middle _last} firstMiddle middleLast =>
        EdgeOrdering.transitive certificate firstMiddle middleLast) with
    ⟨maximal, maximalInValues, noSuccessor⟩
  apply Classical.byContradiction
  intro noSplitting
  have targetNotSplitting :
      ¬certificate.SplittingVertex maximal.target := by
    intro splitting
    exact noSplitting ⟨maximal.target, splitting⟩
  rcases acyclic.ordering_of_not_splitting certificate structural maximal
      targetNotSplitting with
    ⟨successor, maximalBeforeSuccessor, _successorCusping⟩
  have successorInValues : successor ∈ values := by
    simpa only [values, List.mem_eraseDups] using
      successor.mem_directedEdges
  exact noSuccessor successor successorInValues maximalBeforeSuccessor

/-- Restrict finite maximality to genuinely cusping occurrences.  Starting
from one such occurrence, the maximal target is a colored splitting vertex;
the exact color-origin theorem then identifies it as the conclusion of a
stored par link. -/
theorem CuspAcyclic.exists_splitting_par_of_cuspingEdge
    (certificate : Certificate) (acyclic : certificate.CuspAcyclic)
    (structural : certificate.StructurallyWellFormed)
    (seed : certificate.fullGraph.DirectedEdge)
    (seedCusping : certificate.CuspingEdge seed) :
    ∃ left right conclusion,
      Link.par left right conclusion ∈ certificate.links ∧
        certificate.SplittingVertex conclusion := by
  classical
  letI : BEq certificate.fullGraph.DirectedEdge :=
    ⟨fun first second => decide (first = second)⟩
  letI : LawfulBEq certificate.fullGraph.DirectedEdge := inferInstance
  let values : List certificate.fullGraph.DirectedEdge :=
    certificate.fullGraph.directedEdges.eraseDups.filter fun directed =>
      decide (certificate.CuspingEdge directed)
  have valuesNodup : values.Nodup := by
    exact (eraseDups_nodup_generic
      certificate.fullGraph.directedEdges).filter _
  have seedInValues : seed ∈ values := by
    simp [values, seed.mem_directedEdges, seedCusping]
  have valuesNonempty : values ≠ [] := by
    intro empty
    rw [empty] at seedInValues
    simp at seedInValues
  rcases exists_relation_maximal values valuesNodup valuesNonempty
      certificate.EdgeOrdering
      (fun value => EdgeOrdering.irrefl certificate value)
      (fun {_first _middle _last} firstMiddle middleLast =>
        EdgeOrdering.transitive certificate firstMiddle middleLast) with
    ⟨maximal, maximalInValues, noSuccessor⟩
  have maximalCusping : certificate.CuspingEdge maximal := by
    have filtered := List.mem_filter.mp maximalInValues
    exact of_decide_eq_true filtered.2
  by_cases splitting : certificate.SplittingVertex maximal.target
  · rcases maximalCusping.par_origin with
      ⟨left, right, conclusion, membership, target, _edgeShape⟩
    subst conclusion
    exact ⟨left, right, maximal.target, membership, splitting⟩
  · rcases acyclic.ordering_of_not_splitting certificate structural maximal
        splitting with
      ⟨successor, maximalBeforeSuccessor, successorCusping⟩
    have successorInValues : successor ∈ values := by
      simp [values, successor.mem_directedEdges, successorCusping]
    exact False.elim
      (noSuccessor successor successorInValues maximalBeforeSuccessor)

/-- In a cusp-acyclic graph, a non-splitting vertex has a based simple cycle
whose closing pair is free but which contains an internal, nontrivial cusping
edge occurrence. -/
theorem CuspAcyclic.cusping_cycle_of_not_splitting
    (certificate : Certificate) (acyclic : certificate.CuspAcyclic)
    {vertex : Vertex} (notSplitting : ¬certificate.SplittingVertex vertex) :
    ∃ (cycle : certificate.fullGraph.EdgeSimpleCycle),
      ∃ before : List certificate.fullGraph.DirectedEdge,
      ∃ incoming outgoing : certificate.fullGraph.DirectedEdge,
      ∃ after : List certificate.fullGraph.DirectedEdge,
      cycle.start = vertex ∧
        ¬certificate.ClosingCusp cycle ∧
        cycle.traversed = before ++ incoming :: outgoing :: after ∧
        certificate.CuspingEdge incoming := by
  rcases certificate.not_splittingVertex_witness notSplitting with
    ⟨cycle, starts, closingFree⟩
  have traversalNotFree :
      ¬certificate.CuspFreeTraversal cycle.traversed := by
    intro traversalFree
    exact acyclic cycle
      ((certificate.cuspFreeCycle_iff cycle).2
        ⟨traversalFree, closingFree⟩)
  rcases CuspFreeTraversal.exists_cusp_of_not_free certificate
      traversalNotFree with
    ⟨before, incoming, outgoing, after, traversalEquation, cusp⟩
  have differentIndex : incoming.index ≠ outgoing.index := by
    intro sameIndex
    have indicesNodup := cycle.edgeIndicesNodup
    rw [traversalEquation] at indicesNodup
    simp only [List.map_append, List.map_cons] at indicesNodup
    rw [sameIndex] at indicesNodup
    have suffixNodup :
        (outgoing.index :: outgoing.index ::
          after.map Graph.DirectedEdge.index).Nodup :=
      (List.nodup_append.mp indicesNodup).2.1
    exact (List.nodup_cons.mp suffixNodup).1 (by simp)
  have differentReverse : incoming ≠ outgoing.reverse := by
    intro same
    apply differentIndex
    simpa using congrArg Graph.DirectedEdge.index same
  exact ⟨cycle, before, incoming, outgoing, after, starts, closingFree,
    traversalEquation, outgoing, cusp, differentReverse⟩

/-- Danos--Regnier switching correctness excludes every cusp-free simple
cycle in the unswitched occurrence multigraph. A hypothetical cycle selects a
par-sparse set of exact edge indices, hence survives inside one switching;
that contradicts the switching's tree property. -/
theorem DeclarativelyCorrect.cuspAcyclic {certificate : Certificate}
    (correct : certificate.DeclarativelyCorrect) :
    certificate.CuspAcyclic := by
  intro cycle free
  have sparse : ParPairSparse certificate.links 0
      (CycleUsesIndex cycle) := by
    have suffixSparse := CuspFreeCycle.parPairSparse_suffix certificate free
      (priorLinks := []) (suffix := certificate.links) (by simp)
    simpa using suffixSparse
  rcases fullSwitchingSelection_covering_exists sparse with
    ⟨selected, retained, mask, selection, keeps⟩
  have ordinarySelection :
      ChoiceSelection certificate.parChoices selected := by
    simpa using selection.choiceSelection
  have switchingTree :
      (certificate.graphForSelection selected).IsTree :=
    correct.2 _ ⟨selected, ordinarySelection, rfl⟩
  have aligned : certificate.fullGraph.edges.length = mask.length := by
    change (linkFullEdges certificate.links).length = mask.length
    exact selection.mask_length.symm
  have allKept : ∀ directed ∈ cycle.traversed,
      mask[directed.index]? = some true := by
    intro directed membership
    have indexInBounds :
        directed.index < (linkFullEdges certificate.links).length := by
      exact (List.getElem?_eq_some_iff.mp directed.lookup).1
    apply keeps directed.index indexInBounds
    simpa using
      (show CycleUsesIndex cycle directed.index from
        ⟨directed, membership, rfl⟩)
  rcases cycle.retainEdges aligned allKept with ⟨retainedCycle⟩
  have retainedEdges :
      (certificate.fullGraph.retainEdges mask).edges = retained := by
    change Graph.retainEdgesByMask certificate.fullEdges mask = retained
    simpa [retainByMask] using selection.retained_eq_retainByMask.symm
  have edgePermutation :
      (certificate.graphForSelection selected).edges.Perm
        (certificate.fullGraph.retainEdges mask).edges := by
    rw [retainedEdges]
    exact selection.edgePermutation.symm
  have retainedTree :
      (certificate.fullGraph.retainEdges mask).IsTree :=
    switchingTree.permuteEdges rfl edgePermutation
  exact retainedTree.no_edgeSimpleCycle retainedCycle

theorem fixedEdges_subset_fullEdges (certificate : Certificate) :
    ∀ edge ∈ certificate.fixedEdges, edge ∈ certificate.fullEdges := by
  intro edge membership
  simp only [fixedEdges, fullEdges, List.mem_flatMap] at membership ⊢
  rcases membership with ⟨link, linkMembership, emitted⟩
  refine ⟨link, linkMembership, ?_⟩
  cases link <;> simp_all

theorem parChoice_edges_mem_fullEdges (certificate : Certificate)
    {choice : Edge × Edge} (membership : choice ∈ certificate.parChoices) :
    choice.1 ∈ certificate.fullEdges ∧
      choice.2 ∈ certificate.fullEdges := by
  simp only [parChoices, List.mem_filterMap] at membership
  rcases membership with ⟨link, linkMembership, emitted⟩
  cases link with
  | «axiom» left right => simp at emitted
  | tensor left right conclusion => simp at emitted
  | par left right conclusion =>
      simp at emitted
      subst choice
      simp only [fullEdges, List.mem_flatMap]
      constructor <;> exact ⟨.par left right conclusion, linkMembership, by simp⟩

theorem ChoiceSelection.selected_origin
    {choices : List (Edge × Edge)} {selected : List Edge}
    (selection : ChoiceSelection choices selected)
    {edge : Edge} (membership : edge ∈ selected) :
    ∃ choice ∈ choices, edge = choice.1 ∨ edge = choice.2 := by
  induction selection with
  | nil => simp at membership
  | @left left right rest selected prior ih =>
      simp at membership
      rcases membership with same | tailMembership
      · exact ⟨(left, right), by simp, Or.inl same⟩
      · rcases ih tailMembership with ⟨choice, choiceMembership, endpoint⟩
        exact ⟨choice, by simp [choiceMembership], endpoint⟩
  | @right left right rest selected prior ih =>
      simp at membership
      rcases membership with same | tailMembership
      · exact ⟨(left, right), by simp, Or.inr same⟩
      · rcases ih tailMembership with ⟨choice, choiceMembership, endpoint⟩
        exact ⟨choice, by simp [choiceMembership], endpoint⟩

theorem graphForSelection_edges_subset_fullEdges (certificate : Certificate)
    {selected : List Edge}
    (selection : ChoiceSelection certificate.parChoices selected) :
    ∀ edge ∈ (certificate.graphForSelection selected).edges,
      edge ∈ certificate.fullEdges := by
  intro edge membership
  change edge ∈ certificate.fixedEdges ++ selected at membership
  rw [List.mem_append] at membership
  rcases membership with fixed | selectedMembership
  · exact certificate.fixedEdges_subset_fullEdges edge fixed
  · rcases selection.selected_origin selectedMembership with
      ⟨choice, choiceMembership, endpoint⟩
    have choiceEdges := certificate.parChoice_edges_mem_fullEdges choiceMembership
    rcases endpoint with rfl | rfl
    · exact choiceEdges.1
    · exact choiceEdges.2

def fullGraphWithoutVertex (certificate : Certificate)
    (removed : Vertex) : Graph where
  vertexCount := certificate.formulas.size
  edges := certificate.fullEdges.filter fun edge => !edge.incident removed

/-- A duplicate-free walk in the full occurrence graph with one vertex deleted
cannot visit that vertex, provided its starting point is different.  This is
the vertex-level side of the bridge from ordinary reachability to exact
occurrence-aware paths. -/
theorem fullGraphWithoutVertex_simpleWalk_avoids
    (certificate : Certificate) (removed : Vertex)
    {start finish : Vertex} {steps : Nat} {visited : List Vertex}
    (simple : (certificate.fullGraphWithoutVertex removed).SimpleWalk
      start steps visited finish)
    (startNe : start ≠ removed) : removed ∉ visited := by
  induction simple with
  | refl => simpa using fun same => startNe same.symm
  | @step priorSteps priorVisited middle current prior adjacency fresh ih =>
      rcases adjacency with ⟨edge, edgeMembership, endpoints⟩
      have nonincident := (List.mem_filter.mp edgeMembership).2
      have currentNe : current ≠ removed := by
        intro same
        subst current
        rcases endpoints with forward | backward
        · rcases forward with ⟨_, edgeSecond⟩
          simp [Edge.incident, edgeSecond] at nonincident
        · rcases backward with ⟨edgeFirst, _⟩
          simp [Edge.incident, edgeFirst] at nonincident
      rw [List.mem_append]
      simp only [List.mem_singleton]
      intro membership
      rcases membership with earlier | atCurrent
      · exact ih earlier
      · exact currentNe atCurrent.symm

def tensorLeftReachable (certificate : Certificate)
    (left conclusion : Vertex) : List Vertex :=
  (certificate.fullGraphWithoutVertex conclusion).closureN
    certificate.formulas.size [left]

def tensorLeftVertices (certificate : Certificate)
    (left conclusion : Vertex) : List Vertex :=
  (List.range certificate.formulas.size).filter fun vertex =>
    vertex != conclusion &&
      (certificate.tensorLeftReachable left conclusion).contains vertex

def tensorRightVertices (certificate : Certificate)
    (left conclusion : Vertex) : List Vertex :=
  (List.range certificate.formulas.size).filter fun vertex =>
    vertex != conclusion &&
      !(certificate.tensorLeftReachable left conclusion).contains vertex

def tensorOtherConclusions (certificate : Certificate)
    (conclusion : Vertex) : List Vertex :=
  certificate.conclusions.erase conclusion

def tensorLeftBoundary (certificate : Certificate)
    (left conclusion : Vertex) : List Vertex :=
  (certificate.tensorOtherConclusions conclusion).filter
      (certificate.tensorLeftVertices left conclusion).contains ++ [left]

def tensorRightBoundary (certificate : Certificate)
    (left right conclusion : Vertex) : List Vertex :=
  (certificate.tensorOtherConclusions conclusion).filter
      (certificate.tensorRightVertices left conclusion).contains ++ [right]

theorem fullGraphWithoutVertex_bounded {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    (removed : Vertex) :
    (certificate.fullGraphWithoutVertex removed).Bounded := by
  intro edge edgeMembership
  change edge ∈ certificate.fullEdges.filter
    (fun candidate => !candidate.incident removed) at edgeMembership
  have fullMembership := (List.mem_filter.mp edgeMembership).1
  simp only [fullEdges, List.mem_flatMap] at fullMembership
  rcases fullMembership with ⟨link, linkMembership, emitted⟩
  have linkWellFormed := structural.2.2.2.2.1 link linkMembership
  cases link with
  | «axiom» first second =>
      simp at emitted
      subst edge
      exact ⟨linkWellFormed.2.1, linkWellFormed.2.2.1,
        linkWellFormed.1⟩
  | tensor first second result =>
      simp at emitted
      rcases emitted with rfl | rfl
      · exact ⟨linkWellFormed.2.2.2.1,
          linkWellFormed.2.2.2.2.2.1, linkWellFormed.2.1⟩
      · exact ⟨linkWellFormed.2.2.2.2.1,
          linkWellFormed.2.2.2.2.2.1, linkWellFormed.2.2.1⟩
  | par first second result =>
      simp at emitted
      rcases emitted with rfl | rfl
      · exact ⟨linkWellFormed.2.2.2.1,
          linkWellFormed.2.2.2.2.2.1, linkWellFormed.2.1⟩
      · exact ⟨linkWellFormed.2.2.2.2.1,
          linkWellFormed.2.2.2.2.2.1, linkWellFormed.2.2.1⟩

theorem fullGraphWithoutVertex_adjacent_of_fullEdge
    {certificate : Certificate} {removed : Vertex} {edge : Edge}
    (membership : edge ∈ certificate.fullEdges)
    (avoids : edge.incident removed = false) :
    (certificate.fullGraphWithoutVertex removed).Adjacent
      edge.first edge.second := by
  refine ⟨edge, ?_, .inl ⟨rfl, rfl⟩⟩
  change edge ∈ certificate.fullEdges.filter
    (fun candidate => !candidate.incident removed)
  simp [membership, avoids]

theorem graphForSelection_adjacent_fullGraphWithout
    {certificate : Certificate} {selected : List Edge}
    (selection : ChoiceSelection certificate.parChoices selected)
    {removed start finish : Vertex}
    (startNotRemoved : start ≠ removed)
    (finishNotRemoved : finish ≠ removed)
    (adjacency : (certificate.graphForSelection selected).Adjacent
      start finish) :
    (certificate.fullGraphWithoutVertex removed).Adjacent start finish := by
  rcases adjacency with ⟨edge, edgeMembership, direction⟩
  have fullMembership := certificate.graphForSelection_edges_subset_fullEdges
    selection edge edgeMembership
  have avoids : edge.incident removed = false := by
    rcases direction with forward | backward
    · simp [Edge.incident, forward, startNotRemoved, finishNotRemoved]
    · simp [Edge.incident, backward, startNotRemoved, finishNotRemoved]
  refine ⟨edge, ?_, direction⟩
  change edge ∈ certificate.fullEdges.filter
    (fun candidate => !candidate.incident removed)
  simp [fullMembership, avoids]

theorem fullGraphWithoutVertex_link_vertices_walk
    {certificate : Certificate} {removed : Vertex} {link : Link}
    (linkMembership : link ∈ certificate.links)
    (avoids : removed ∉ link.vertices)
    {start finish : Vertex}
    (startMembership : start ∈ link.vertices)
    (finishMembership : finish ∈ link.vertices) :
    (certificate.fullGraphWithoutVertex removed).Walk start finish := by
  cases link with
  | «axiom» first second =>
      simp [Link.vertices] at avoids startMembership finishMembership
      have firstNotRemoved : first ≠ removed := Ne.symm avoids.1
      have secondNotRemoved : second ≠ removed := Ne.symm avoids.2
      let edge : Edge := { first, second }
      have edgeMembership : edge ∈ certificate.fullEdges := by
        simp only [fullEdges, List.mem_flatMap]
        exact ⟨.axiom first second, linkMembership, by simp [edge]⟩
      have adjacency :
          (certificate.fullGraphWithoutVertex removed).Adjacent first second :=
        fullGraphWithoutVertex_adjacent_of_fullEdge edgeMembership (by
          simp [edge, Edge.incident, firstNotRemoved, secondNotRemoved])
      have firstToSecond :
          (certificate.fullGraphWithoutVertex removed).Walk first second :=
        .step (.refl first) adjacency
      rcases startMembership with rfl | rfl <;>
      rcases finishMembership with rfl | rfl
      · exact .refl _
      · exact firstToSecond
      · exact firstToSecond.reverse
      · exact .refl _
  | tensor first second result =>
      simp [Link.vertices] at avoids startMembership finishMembership
      have firstNotRemoved : first ≠ removed := Ne.symm avoids.1
      have secondNotRemoved : second ≠ removed := Ne.symm avoids.2.1
      have resultNotRemoved : result ≠ removed := Ne.symm avoids.2.2
      let firstEdge : Edge := { first := first, second := result }
      let secondEdge : Edge := { first := second, second := result }
      have firstEdgeMembership : firstEdge ∈ certificate.fullEdges := by
        simp only [fullEdges, List.mem_flatMap]
        exact ⟨.tensor first second result, linkMembership, by
          simp [firstEdge]⟩
      have secondEdgeMembership : secondEdge ∈ certificate.fullEdges := by
        simp only [fullEdges, List.mem_flatMap]
        exact ⟨.tensor first second result, linkMembership, by
          simp [secondEdge]⟩
      have firstAdjacency :
          (certificate.fullGraphWithoutVertex removed).Adjacent first result :=
        fullGraphWithoutVertex_adjacent_of_fullEdge firstEdgeMembership (by
          simp [firstEdge, Edge.incident, firstNotRemoved, resultNotRemoved])
      have secondAdjacency :
          (certificate.fullGraphWithoutVertex removed).Adjacent second result :=
        fullGraphWithoutVertex_adjacent_of_fullEdge secondEdgeMembership (by
          simp [secondEdge, Edge.incident, secondNotRemoved, resultNotRemoved])
      have toResult : ∀ vertex,
          vertex = first ∨ vertex = second ∨ vertex = result →
          (certificate.fullGraphWithoutVertex removed).Walk vertex result := by
        intro vertex membership
        rcases membership with rfl | rfl | rfl
        · exact .step (.refl _) firstAdjacency
        · exact .step (.refl _) secondAdjacency
        · exact .refl _
      exact (toResult start startMembership).trans
        (toResult finish finishMembership).reverse
  | par first second result =>
      simp [Link.vertices] at avoids startMembership finishMembership
      have firstNotRemoved : first ≠ removed := Ne.symm avoids.1
      have secondNotRemoved : second ≠ removed := Ne.symm avoids.2.1
      have resultNotRemoved : result ≠ removed := Ne.symm avoids.2.2
      let firstEdge : Edge := { first := first, second := result }
      let secondEdge : Edge := { first := second, second := result }
      have firstEdgeMembership : firstEdge ∈ certificate.fullEdges := by
        simp only [fullEdges, List.mem_flatMap]
        exact ⟨.par first second result, linkMembership, by
          simp [firstEdge]⟩
      have secondEdgeMembership : secondEdge ∈ certificate.fullEdges := by
        simp only [fullEdges, List.mem_flatMap]
        exact ⟨.par first second result, linkMembership, by
          simp [secondEdge]⟩
      have firstAdjacency :
          (certificate.fullGraphWithoutVertex removed).Adjacent first result :=
        fullGraphWithoutVertex_adjacent_of_fullEdge firstEdgeMembership (by
          simp [firstEdge, Edge.incident, firstNotRemoved, resultNotRemoved])
      have secondAdjacency :
          (certificate.fullGraphWithoutVertex removed).Adjacent second result :=
        fullGraphWithoutVertex_adjacent_of_fullEdge secondEdgeMembership (by
          simp [secondEdge, Edge.incident, secondNotRemoved, resultNotRemoved])
      have toResult : ∀ vertex,
          vertex = first ∨ vertex = second ∨ vertex = result →
          (certificate.fullGraphWithoutVertex removed).Walk vertex result := by
        intro vertex membership
        rcases membership with rfl | rfl | rfl
        · exact .step (.refl _) firstAdjacency
        · exact .step (.refl _) secondAdjacency
        · exact .refl _
      exact (toResult start startMembership).trans
        (toResult finish finishMembership).reverse
/-- Induce a locally numbered certificate on a listed subset and an explicitly
chosen boundary. Crossing links are omitted, so callers must separately prove
or check that the proposed partition covers every remaining link. -/
def restrictTo? (certificate : Certificate) (vertices boundary : List Vertex) :
    Option Certificate := do
  let formulas ← vertices.mapM certificate.formula?
  let conclusions ← boundary.mapM vertices.idxOf?
  pure {
    formulas := formulas.toArray
    links := certificate.links.filterMap (Link.restrictTo? vertices)
    conclusions }

theorem restrictTo?_eq_some_exists (certificate : Certificate)
    (vertices boundary : List Vertex)
    (verticesInBounds : ∀ vertex ∈ vertices,
      vertex < certificate.formulas.size)
    (boundaryContained : ∀ vertex ∈ boundary, vertex ∈ vertices) :
    ∃ restricted, certificate.restrictTo? vertices boundary = some restricted := by
  have formulasDefined : ∀ vertex ∈ vertices,
      ∃ formula, certificate.formula? vertex = some formula := by
    intro vertex membership
    have inBounds := verticesInBounds vertex membership
    exact ⟨certificate.formulas[vertex], by
      simp [formula?, inBounds]⟩
  rcases list_mapM_eq_some_of_forall vertices certificate.formula?
      formulasDefined with ⟨formulas, formulasEquation⟩
  have indicesDefined : ∀ vertex ∈ boundary,
      ∃ index, vertices.idxOf? vertex = some index := by
    intro vertex membership
    have contained := boundaryContained vertex membership
    cases equation : vertices.idxOf? vertex with
    | none =>
        have absent := (List.idxOf?_eq_none_iff).mp equation
        exact False.elim (absent contained)
    | some index => exact ⟨index, rfl⟩
  rcases list_mapM_eq_some_of_forall boundary vertices.idxOf?
      indicesDefined with ⟨conclusions, conclusionsEquation⟩
  refine ⟨{
    formulas := formulas.toArray
    links := certificate.links.filterMap (Link.restrictTo? vertices)
    conclusions := conclusions }, ?_⟩
  simp [restrictTo?, formulasEquation, conclusionsEquation]

/-- Exact value returned by `restrictTo?` when all requested occurrences are
in bounds and every requested boundary occurrence belongs to the restricted
vertex list.  This is the rewriting interface used by the structural and
switching-preservation proofs for tensor splitting. -/
theorem restrictTo?_eq_some_of_conditions (certificate : Certificate)
    (vertices boundary : List Vertex)
    (verticesInBounds : ∀ vertex ∈ vertices,
      vertex < certificate.formulas.size)
    (boundaryContained : ∀ vertex ∈ boundary, vertex ∈ vertices)
    (fallback : Formula) :
    certificate.restrictTo? vertices boundary = some {
      formulas := (vertices.map fun vertex =>
        certificate.formulas.getD vertex fallback).toArray
      links := certificate.links.filterMap (Link.restrictTo? vertices)
      conclusions := boundary.map vertices.idxOf } := by
  have formulasEquation :
      vertices.mapM certificate.formula? = some
        (vertices.map fun vertex => certificate.formulas.getD vertex fallback) := by
    apply list_mapM_eq_some_map_of_forall
    intro vertex membership
    have inBounds := verticesInBounds vertex membership
    simp [formula?, inBounds]
  have conclusionsEquation :
      boundary.mapM vertices.idxOf? = some (boundary.map vertices.idxOf) := by
    apply list_mapM_eq_some_map_of_forall
    intro vertex membership
    exact idxOf?_eq_some_idxOf_of_mem
      (boundaryContained vertex membership)
  simp [restrictTo?, formulasEquation, conclusionsEquation]

/-- Looking up a retained occurrence at its local index returns exactly the
formula that labelled the original occurrence. -/
theorem restrictTo?_formula?_idxOf
    {certificate restricted : Certificate}
    {vertices boundary : List Vertex}
    (verticesInBounds : ∀ vertex ∈ vertices,
      vertex < certificate.formulas.size)
    (boundaryContained : ∀ vertex ∈ boundary, vertex ∈ vertices)
    (equation : certificate.restrictTo? vertices boundary = some restricted)
    {vertex : Vertex} (membership : vertex ∈ vertices) :
    restricted.formula? (vertices.idxOf vertex) = certificate.formula? vertex := by
  let fallback : Formula := .atom "" false
  have exactEquation := certificate.restrictTo?_eq_some_of_conditions
    vertices boundary verticesInBounds boundaryContained fallback
  rw [exactEquation] at equation
  cases equation
  have retained := list_map_getElem?_idxOf_eq_some vertices
    (fun candidate => certificate.formulas.getD candidate fallback) membership
  have vertexInBounds := verticesInBounds vertex membership
  simpa [formula?, retained, vertexInBounds] using retained

/-- A successful occurrence restriction preserves the exact ordered formula
labels of its requested boundary.  Local vertex names disappear from the
statement, which is the interface needed by recursive sequentialization. -/
theorem restrictTo?_conclusionFormulas?_eq_some
    {certificate restricted : Certificate}
    {vertices boundary : List Vertex}
    (verticesInBounds : ∀ vertex ∈ vertices,
      vertex < certificate.formulas.size)
    (boundaryContained : ∀ vertex ∈ boundary, vertex ∈ vertices)
    (equation : certificate.restrictTo? vertices boundary = some restricted)
    (fallback : Formula) :
    restricted.conclusionFormulas? = some
      (boundary.map fun vertex => certificate.formulas.getD vertex fallback) := by
  have conclusionsEquation :
      restricted.conclusions = boundary.map vertices.idxOf := by
    have exactEquation := certificate.restrictTo?_eq_some_of_conditions
      vertices boundary verticesInBounds boundaryContained fallback
    rw [exactEquation] at equation
    cases equation
    rfl
  unfold conclusionFormulas?
  rw [conclusionsEquation]
  rw [List.mapM_map]
  apply list_mapM_eq_some_map_of_forall
  intro vertex membership
  change restricted.formula? (vertices.idxOf vertex) = _
  rw [certificate.restrictTo?_formula?_idxOf verticesInBounds
    boundaryContained equation (boundaryContained vertex membership)]
  have inBounds := verticesInBounds vertex
    (boundaryContained vertex membership)
  simp [formula?, inBounds]

theorem restrictTo?_formulas_size {certificate restricted : Certificate}
    {vertices boundary : List Vertex}
    (equation : certificate.restrictTo? vertices boundary = some restricted) :
    restricted.formulas.size = vertices.length := by
  unfold restrictTo? at equation
  cases formulasEquation : vertices.mapM certificate.formula? with
  | none => simp [formulasEquation] at equation
  | some formulas =>
      cases conclusionsEquation : boundary.mapM vertices.idxOf? with
      | none => simp [formulasEquation, conclusionsEquation] at equation
      | some conclusions =>
          simp [formulasEquation, conclusionsEquation] at equation
          subst restricted
          simpa using list_mapM_length_of_eq_some formulasEquation

theorem restrictTo?_conclusions_length
    {certificate restricted : Certificate} {vertices boundary : List Vertex}
    (equation : certificate.restrictTo? vertices boundary = some restricted) :
    restricted.conclusions.length = boundary.length := by
  unfold restrictTo? at equation
  cases formulasEquation : vertices.mapM certificate.formula? with
  | none => simp [formulasEquation] at equation
  | some formulas =>
      cases conclusionsEquation : boundary.mapM vertices.idxOf? with
      | none => simp [formulasEquation, conclusionsEquation] at equation
      | some conclusions =>
          simp [formulasEquation, conclusionsEquation] at equation
          subst restricted
          exact list_mapM_length_of_eq_some conclusionsEquation

theorem restrictTo?_links
    {certificate restricted : Certificate} {vertices boundary : List Vertex}
    (equation : certificate.restrictTo? vertices boundary = some restricted) :
    restricted.links = certificate.links.filterMap
      (Link.restrictTo? vertices) := by
  unfold restrictTo? at equation
  cases formulasEquation : vertices.mapM certificate.formula? with
  | none => simp [formulasEquation] at equation
  | some formulas =>
      cases conclusionsEquation : boundary.mapM vertices.idxOf? with
      | none => simp [formulasEquation, conclusionsEquation] at equation
      | some conclusions =>
          simp [formulasEquation, conclusionsEquation] at equation
          subst restricted
          rfl

theorem restrictTo?_conclusions
    {certificate restricted : Certificate} {vertices boundary : List Vertex}
    (verticesInBounds : ∀ vertex ∈ vertices,
      vertex < certificate.formulas.size)
    (boundaryContained : ∀ vertex ∈ boundary, vertex ∈ vertices)
    (equation : certificate.restrictTo? vertices boundary = some restricted) :
    restricted.conclusions = boundary.map vertices.idxOf := by
  let fallback : Formula := .atom "" false
  have exactEquation := certificate.restrictTo?_eq_some_of_conditions
    vertices boundary verticesInBounds boundaryContained fallback
  rw [exactEquation] at equation
  cases equation
  rfl

theorem restrictTo?_idxOf_mem_conclusions_iff
    {certificate restricted : Certificate} {vertices boundary : List Vertex}
    (verticesInBounds : ∀ vertex ∈ vertices,
      vertex < certificate.formulas.size)
    (boundaryContained : ∀ vertex ∈ boundary, vertex ∈ vertices)
    (equation : certificate.restrictTo? vertices boundary = some restricted)
    {vertex : Vertex} (vertexContained : vertex ∈ vertices) :
    vertices.idxOf vertex ∈ restricted.conclusions ↔ vertex ∈ boundary := by
  rw [certificate.restrictTo?_conclusions verticesInBounds
    boundaryContained equation]
  constructor
  · intro membership
    rcases List.mem_map.mp membership with
      ⟨boundaryVertex, boundaryMembership, sameIndex⟩
    have same := idxOf_injective_of_mem
      (boundaryContained boundaryVertex boundaryMembership)
      vertexContained sameIndex
    simpa [same] using boundaryMembership
  · intro membership
    exact List.mem_map.mpr ⟨vertex, membership, rfl⟩

private theorem restrictTo?_filter_count_eq_of_partition
    {certificate restricted : Certificate}
    {vertices boundary : List Vertex} {terminalLink : Link}
    (certificateEquation :
      certificate.restrictTo? vertices boundary = some restricted)
    (after before : Link → Bool)
    (partition : ∀ link ∈ certificate.links,
      link = terminalLink ∨
        (∀ vertex ∈ link.vertices, vertex ∈ vertices) ∨
        (∀ vertex ∈ link.vertices, vertex ∉ vertices))
    (terminalRejected : before terminalLink = false)
    (avoidingRejected : ∀ link,
      (∀ vertex ∈ link.vertices, vertex ∉ vertices) → before link = false)
    (preserved : ∀ link transformed,
      link.restrictTo? vertices = some transformed →
        after transformed = before link) :
    (restricted.links.filter after).length =
      (certificate.links.filter before).length := by
  rw [certificate.restrictTo?_links certificateEquation]
  apply length_filter_filterMap_eq
  intro link membership
  cases linkEquation : link.restrictTo? vertices with
  | none =>
      rcases partition link membership with terminal | contained | avoids
      · subst link
        exact terminalRejected
      · have accepted := Link.restrictTo?_eq_some_of_vertices
          link vertices contained
        rw [accepted] at linkEquation
        cases linkEquation
      · exact avoidingRejected link avoids
  | some transformed =>
      exact preserved link transformed linkEquation

/-- Local link typing is invariant under restriction to a vertex set containing
all endpoints of the link. -/
theorem LinkWellFormed.restrictTo
    {certificate restricted : Certificate}
    {vertices boundary : List Vertex}
    (verticesInBounds : ∀ vertex ∈ vertices,
      vertex < certificate.formulas.size)
    (boundaryContained : ∀ vertex ∈ boundary, vertex ∈ vertices)
    (certificateEquation :
      certificate.restrictTo? vertices boundary = some restricted)
    {link restrictedLink : Link}
    (wellFormed : certificate.LinkWellFormed link)
    (linkEquation : link.restrictTo? vertices = some restrictedLink) :
    restricted.LinkWellFormed restrictedLink := by
  have contained := Link.vertices_mem_of_restrictTo?_eq_some linkEquation
  have exactLinkEquation := Link.restrictTo?_eq_some_of_vertices
    link vertices contained
  rw [exactLinkEquation] at linkEquation
  cases linkEquation
  have formulasSize := certificate.restrictTo?_formulas_size certificateEquation
  cases link with
  | «axiom» left right =>
      have leftContained := contained left (by simp [Link.vertices])
      have rightContained := contained right (by simp [Link.vertices])
      have leftInBounds : vertices.idxOf left < restricted.formulas.size := by
        rw [formulasSize]
        exact List.idxOf_lt_length_of_mem leftContained
      have rightInBounds : vertices.idxOf right < restricted.formulas.size := by
        rw [formulasSize]
        exact List.idxOf_lt_length_of_mem rightContained
      have different : vertices.idxOf left ≠ vertices.idxOf right := by
        intro same
        exact wellFormed.1
          (idxOf_injective_of_mem leftContained rightContained same)
      rcases wellFormed with ⟨_, _, _, typing⟩
      refine ⟨different, leftInBounds, rightInBounds, ?_⟩
      rw [certificate.restrictTo?_formula?_idxOf verticesInBounds
        boundaryContained certificateEquation leftContained]
      rw [certificate.restrictTo?_formula?_idxOf verticesInBounds
        boundaryContained certificateEquation rightContained]
      exact typing
  | tensor left right conclusion =>
      have leftContained := contained left (by simp [Link.vertices])
      have rightContained := contained right (by simp [Link.vertices])
      have conclusionContained := contained conclusion (by simp [Link.vertices])
      have leftInBounds : vertices.idxOf left < restricted.formulas.size := by
        rw [formulasSize]
        exact List.idxOf_lt_length_of_mem leftContained
      have rightInBounds : vertices.idxOf right < restricted.formulas.size := by
        rw [formulasSize]
        exact List.idxOf_lt_length_of_mem rightContained
      have conclusionInBounds :
          vertices.idxOf conclusion < restricted.formulas.size := by
        rw [formulasSize]
        exact List.idxOf_lt_length_of_mem conclusionContained
      have leftRightDifferent : vertices.idxOf left ≠ vertices.idxOf right := by
        intro same
        exact wellFormed.1
          (idxOf_injective_of_mem leftContained rightContained same)
      have leftConclusionDifferent :
          vertices.idxOf left ≠ vertices.idxOf conclusion := by
        intro same
        exact wellFormed.2.1
          (idxOf_injective_of_mem leftContained conclusionContained same)
      have rightConclusionDifferent :
          vertices.idxOf right ≠ vertices.idxOf conclusion := by
        intro same
        exact wellFormed.2.2.1
          (idxOf_injective_of_mem rightContained conclusionContained same)
      rcases wellFormed with ⟨_, _, _, _, _, _, typing⟩
      refine ⟨leftRightDifferent, leftConclusionDifferent,
        rightConclusionDifferent, leftInBounds, rightInBounds,
        conclusionInBounds, ?_⟩
      rw [certificate.restrictTo?_formula?_idxOf verticesInBounds
        boundaryContained certificateEquation leftContained]
      rw [certificate.restrictTo?_formula?_idxOf verticesInBounds
        boundaryContained certificateEquation rightContained]
      rw [certificate.restrictTo?_formula?_idxOf verticesInBounds
        boundaryContained certificateEquation conclusionContained]
      exact typing
  | par left right conclusion =>
      have leftContained := contained left (by simp [Link.vertices])
      have rightContained := contained right (by simp [Link.vertices])
      have conclusionContained := contained conclusion (by simp [Link.vertices])
      have leftInBounds : vertices.idxOf left < restricted.formulas.size := by
        rw [formulasSize]
        exact List.idxOf_lt_length_of_mem leftContained
      have rightInBounds : vertices.idxOf right < restricted.formulas.size := by
        rw [formulasSize]
        exact List.idxOf_lt_length_of_mem rightContained
      have conclusionInBounds :
          vertices.idxOf conclusion < restricted.formulas.size := by
        rw [formulasSize]
        exact List.idxOf_lt_length_of_mem conclusionContained
      have leftRightDifferent : vertices.idxOf left ≠ vertices.idxOf right := by
        intro same
        exact wellFormed.1
          (idxOf_injective_of_mem leftContained rightContained same)
      have leftConclusionDifferent :
          vertices.idxOf left ≠ vertices.idxOf conclusion := by
        intro same
        exact wellFormed.2.1
          (idxOf_injective_of_mem leftContained conclusionContained same)
      have rightConclusionDifferent :
          vertices.idxOf right ≠ vertices.idxOf conclusion := by
        intro same
        exact wellFormed.2.2.1
          (idxOf_injective_of_mem rightContained conclusionContained same)
      rcases wellFormed with ⟨_, _, _, _, _, _, typing⟩
      refine ⟨leftRightDifferent, leftConclusionDifferent,
        rightConclusionDifferent, leftInBounds, rightInBounds,
        conclusionInBounds, ?_⟩
      rw [certificate.restrictTo?_formula?_idxOf verticesInBounds
        boundaryContained certificateEquation leftContained]
      rw [certificate.restrictTo?_formula?_idxOf verticesInBounds
        boundaryContained certificateEquation rightContained]
      rw [certificate.restrictTo?_formula?_idxOf verticesInBounds
        boundaryContained certificateEquation conclusionContained]
      exact typing

theorem restrictTo?_linksWellFormed
    {certificate restricted : Certificate}
    {vertices boundary : List Vertex}
    (verticesInBounds : ∀ vertex ∈ vertices,
      vertex < certificate.formulas.size)
    (boundaryContained : ∀ vertex ∈ boundary, vertex ∈ vertices)
    (certificateEquation :
      certificate.restrictTo? vertices boundary = some restricted)
    (linksWellFormed : ∀ link ∈ certificate.links,
      certificate.LinkWellFormed link) :
    ∀ link ∈ restricted.links, restricted.LinkWellFormed link := by
  intro link membership
  rw [certificate.restrictTo?_links certificateEquation] at membership
  rcases List.mem_filterMap.mp membership with
    ⟨original, originalMembership, linkEquation⟩
  exact (linksWellFormed original originalMembership).restrictTo
    verticesInBounds boundaryContained certificateEquation linkEquation

/-- All structural obligations for a restriction except per-occurrence source
and parent ownership.  The omitted ownership field is where component closure
is used by tensor splitting. -/
theorem restrictTo?_structuralPrefix
    {certificate restricted : Certificate}
    {vertices boundary : List Vertex}
    (verticesInBounds : ∀ vertex ∈ vertices,
      vertex < certificate.formulas.size)
    (boundaryContained : ∀ vertex ∈ boundary, vertex ∈ vertices)
    (verticesNonempty : 0 < vertices.length)
    (boundaryNonempty : 0 < boundary.length)
    (boundaryNodup : boundary.Nodup)
    (linksWellFormed : ∀ link ∈ certificate.links,
      certificate.LinkWellFormed link)
    (certificateEquation :
      certificate.restrictTo? vertices boundary = some restricted) :
    0 < restricted.formulas.size ∧
      0 < restricted.conclusions.length ∧
      (∀ vertex ∈ restricted.conclusions,
        vertex < restricted.formulas.size) ∧
      restricted.conclusions.eraseDups.length =
        restricted.conclusions.length ∧
      (∀ link ∈ restricted.links, restricted.LinkWellFormed link) := by
  have formulasSize := certificate.restrictTo?_formulas_size certificateEquation
  have conclusionsLength :=
    certificate.restrictTo?_conclusions_length certificateEquation
  have conclusionsEquation := certificate.restrictTo?_conclusions
    verticesInBounds boundaryContained certificateEquation
  have localBoundaryNodup : (boundary.map vertices.idxOf).Nodup := by
    apply nodup_map_of_injective_on boundaryNodup
    intro first firstMembership second secondMembership same
    exact idxOf_injective_of_mem
      (boundaryContained first firstMembership)
      (boundaryContained second secondMembership) same
  refine ⟨by simpa [formulasSize] using verticesNonempty,
    by simpa [conclusionsLength] using boundaryNonempty, ?_, ?_,
    certificate.restrictTo?_linksWellFormed verticesInBounds
      boundaryContained certificateEquation linksWellFormed⟩
  · intro localVertex localMembership
    rw [conclusionsEquation] at localMembership
    rcases List.mem_map.mp localMembership with
      ⟨originalVertex, originalMembership, rfl⟩
    rw [formulasSize]
    exact List.idxOf_lt_length_of_mem
      (boundaryContained originalVertex originalMembership)
  · rw [conclusionsEquation,
      eraseDups_eq_self_of_nodup localBoundaryNodup]

/-- Restricting links commutes exactly with extracting par switching choices.
Unlike fixed tensor edges, this identity needs no component-closure premise:
the two alternatives together mention all three vertices of a par link. -/
theorem restrictTo?_parChoices
    {certificate restricted : Certificate} {vertices boundary : List Vertex}
    (certificateEquation :
      certificate.restrictTo? vertices boundary = some restricted) :
    restricted.parChoices = certificate.parChoices.filterMap
      (ParChoice.restrictTo? vertices) := by
  unfold Certificate.parChoices
  rw [certificate.restrictTo?_links certificateEquation]
  let emitChoice : Link → Option (Edge × Edge) := fun
    | .par left right conclusion =>
        some ({ first := left, second := conclusion },
          { first := right, second := conclusion })
    | _ => none
  change
    ((certificate.links.filterMap (Link.restrictTo? vertices)).filterMap
      emitChoice) =
    (certificate.links.filterMap emitChoice).filterMap
      (ParChoice.restrictTo? vertices)
  induction certificate.links with
  | nil => rfl
  | cons head tail ih =>
      cases head with
      | «axiom» left right =>
          cases leftEquation : vertices.idxOf? left <;>
          cases rightEquation : vertices.idxOf? right <;>
            simp [Link.restrictTo?, emitChoice, leftEquation, rightEquation, ih]
      | tensor left right conclusion =>
          cases leftEquation : vertices.idxOf? left <;>
          cases rightEquation : vertices.idxOf? right <;>
          cases conclusionEquation : vertices.idxOf? conclusion <;>
            simp [Link.restrictTo?, emitChoice, leftEquation, rightEquation,
              conclusionEquation, ih]
      | par left right conclusion =>
          cases leftEquation : vertices.idxOf? left <;>
          cases rightEquation : vertices.idxOf? right <;>
          cases conclusionEquation : vertices.idxOf? conclusion <;>
            simp [Link.restrictTo?, Edge.restrictTo?, ParChoice.restrictTo?,
              emitChoice, leftEquation, rightEquation, conclusionEquation, ih]

/-- Fixed switching edges commute with component restriction when every input
link is either the removed terminal tensor, wholly inside, or wholly outside
the component. -/
theorem restrictTo?_fixedEdges_of_tensor_partition
    {certificate restricted : Certificate} {vertices boundary : List Vertex}
    {left right conclusion : Vertex}
    (certificateEquation :
      certificate.restrictTo? vertices boundary = some restricted)
    (conclusionOutside : conclusion ∉ vertices)
    (partition : ∀ link ∈ certificate.links,
      link = .tensor left right conclusion ∨
        (∀ vertex ∈ link.vertices, vertex ∈ vertices) ∨
        (∀ vertex ∈ link.vertices, vertex ∉ vertices)) :
    restricted.fixedEdges = certificate.fixedEdges.filterMap
      (Edge.restrictTo? vertices) := by
  unfold Certificate.fixedEdges
  rw [certificate.restrictTo?_links certificateEquation]
  let emitFixed : Link → List Edge := fun
    | .axiom first second => [{ first, second }]
    | .tensor first second result =>
        [{ first := first, second := result },
         { first := second, second := result }]
    | .par _ _ _ => []
  change
    (certificate.links.filterMap (Link.restrictTo? vertices)).flatMap
        emitFixed =
      (certificate.links.flatMap emitFixed).filterMap
        (Edge.restrictTo? vertices)
  suffices general : ∀ links : List Link,
      (∀ link ∈ links, link ∈ certificate.links) →
      (links.filterMap (Link.restrictTo? vertices)).flatMap emitFixed =
        (links.flatMap emitFixed).filterMap (Edge.restrictTo? vertices) by
    exact general certificate.links (by simp)
  intro links subset
  induction links with
  | nil => rfl
  | cons head tail ih =>
      have headMembership := subset head (by simp)
      have tailSubset : ∀ link ∈ tail, link ∈ certificate.links := by
        intro link membership
        exact subset link (by simp [membership])
      have tailEquality := ih tailSubset
      cases head with
      | «axiom» first second =>
          cases firstEquation : vertices.idxOf? first <;>
          cases secondEquation : vertices.idxOf? second <;>
            simp [Link.restrictTo?, Edge.restrictTo?, emitFixed,
              firstEquation, secondEquation, tailEquality]
      | tensor first second result =>
          rcases partition (.tensor first second result) headMembership with
            terminal | contained | avoids
          · cases terminal
            have conclusionNone : vertices.idxOf? conclusion = none :=
              (List.idxOf?_eq_none_iff).mpr conclusionOutside
            simp [Link.restrictTo?, Edge.restrictTo?, emitFixed,
              conclusionNone, tailEquality]
          · have firstContained := contained first (by simp [Link.vertices])
            have secondContained := contained second (by simp [Link.vertices])
            have resultContained := contained result (by simp [Link.vertices])
            have firstEquation := idxOf?_eq_some_idxOf_of_mem firstContained
            have secondEquation := idxOf?_eq_some_idxOf_of_mem secondContained
            have resultEquation := idxOf?_eq_some_idxOf_of_mem resultContained
            simp [Link.restrictTo?, Edge.restrictTo?, emitFixed,
              firstEquation, secondEquation, resultEquation, tailEquality]
          · have firstOutside := avoids first (by simp [Link.vertices])
            have secondOutside := avoids second (by simp [Link.vertices])
            have resultOutside := avoids result (by simp [Link.vertices])
            have firstEquation : vertices.idxOf? first = none :=
              (List.idxOf?_eq_none_iff).mpr firstOutside
            have secondEquation : vertices.idxOf? second = none :=
              (List.idxOf?_eq_none_iff).mpr secondOutside
            have resultEquation : vertices.idxOf? result = none :=
              (List.idxOf?_eq_none_iff).mpr resultOutside
            simp [Link.restrictTo?, Edge.restrictTo?, emitFixed,
              firstEquation, secondEquation, resultEquation, tailEquality]
      | par first second result =>
          cases firstEquation : vertices.idxOf? first <;>
          cases secondEquation : vertices.idxOf? second <;>
          cases resultEquation : vertices.idxOf? result <;>
            simp [Link.restrictTo?, emitFixed,
              firstEquation, secondEquation, resultEquation, tailEquality]

def formulaComplexityAt (certificate : Certificate) (vertex : Vertex) : Nat :=
  (certificate.formula? vertex).map Formula.complexity |>.getD 0

def linkConclusionComplexity (certificate : Certificate) : Link → Nat
  | .axiom _ _ => 0
  | .tensor _ _ conclusion => certificate.formulaComplexityAt conclusion
  | .par _ _ conclusion => certificate.formulaComplexityAt conclusion

theorem LinkWellFormed.premise_complexity_lt_conclusion
    {certificate : Certificate} {link : Link} {premise : Vertex}
    (wellFormed : certificate.LinkWellFormed link)
    (membership : premise ∈ link.premises) :
    certificate.formulaComplexityAt premise <
      certificate.linkConclusionComplexity link := by
  cases link with
  | «axiom» left right => simp [Link.premises] at membership
  | tensor left right conclusion =>
      rcases wellFormed with ⟨_, _, _, _, _, _, typing⟩
      cases leftEquation : certificate.formula? left with
      | none => simp [leftEquation] at typing
      | some leftFormula =>
          cases rightEquation : certificate.formula? right with
          | none => simp [leftEquation, rightEquation] at typing
          | some rightFormula =>
              cases conclusionEquation : certificate.formula? conclusion with
              | none =>
                  simp [leftEquation, rightEquation, conclusionEquation] at typing
              | some conclusionFormula =>
                  simp [leftEquation, rightEquation, conclusionEquation] at typing
                  subst conclusionFormula
                  simp [Link.premises] at membership
                  rcases membership with rfl | rfl
                  · simpa [formulaComplexityAt, linkConclusionComplexity,
                      leftEquation, conclusionEquation] using
                      Formula.complexity_lt_tensor_left leftFormula rightFormula
                  · simpa [formulaComplexityAt, linkConclusionComplexity,
                      rightEquation, conclusionEquation] using
                      Formula.complexity_lt_tensor_right leftFormula rightFormula
  | par left right conclusion =>
      rcases wellFormed with ⟨_, _, _, _, _, _, typing⟩
      cases leftEquation : certificate.formula? left with
      | none => simp [leftEquation] at typing
      | some leftFormula =>
          cases rightEquation : certificate.formula? right with
          | none => simp [leftEquation, rightEquation] at typing
          | some rightFormula =>
              cases conclusionEquation : certificate.formula? conclusion with
              | none =>
                  simp [leftEquation, rightEquation, conclusionEquation] at typing
              | some conclusionFormula =>
                  simp [leftEquation, rightEquation, conclusionEquation] at typing
                  subst conclusionFormula
                  simp [Link.premises] at membership
                  rcases membership with rfl | rfl
                  · simpa [formulaComplexityAt, linkConclusionComplexity,
                      leftEquation, conclusionEquation] using
                      Formula.complexity_lt_par_left leftFormula rightFormula
                  · simpa [formulaComplexityAt, linkConclusionComplexity,
                      rightEquation, conclusionEquation] using
                      Formula.complexity_lt_par_right leftFormula rightFormula

/-- A par link is terminal when its conclusion occurrence is on the ordered
public boundary. Such a link is the unary inverse-rule case of
sequentialization. -/
def TerminalPar (certificate : Certificate)
    (left right conclusion : Vertex) : Prop :=
  Link.par left right conclusion ∈ certificate.links ∧
    conclusion ∈ certificate.conclusions

/-- A tensor link is terminal when its conclusion occurrence is on the public
boundary. Sequentialization additionally needs the tensor to split the
remaining proof structure into two correct components. -/
def TerminalTensor (certificate : Certificate)
    (left right conclusion : Vertex) : Prop :=
  Link.tensor left right conclusion ∈ certificate.links ∧
    conclusion ∈ certificate.conclusions

/-- A terminal tensor is splitting when deleting its conclusion from the full
occurrence graph separates the two premises. This proposition is independent
of the executable closure algorithm used by the candidate finder. -/
def SplittingTensor (certificate : Certificate)
    (left right conclusion : Vertex) : Prop :=
  certificate.TerminalTensor left right conclusion ∧
    ¬(certificate.fullGraphWithoutVertex conclusion).Walk left right

/-- Representation bridge from generalized-Yeo colored splitting to the
terminal-tensor separation proposition used by recursive sequentialization.
If the two tensor premises remained connected after deleting the conclusion,
an exact lifted path together with the two distinct tensor occurrences would
form a cycle based at the conclusion whose closing colors are different. -/
theorem SplittingVertex.toSplittingTensor
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalTensor left right conclusion)
    (splitting : certificate.SplittingVertex conclusion) :
    certificate.SplittingTensor left right conclusion := by
  classical
  refine ⟨terminal, ?_⟩
  intro connected
  have tensorWellFormed := structural.2.2.2.2.1 _ terminal.1
  have leftNeRight : left ≠ right := tensorWellFormed.1
  have leftNeConclusion : left ≠ conclusion := tensorWellFormed.2.1
  have rightNeConclusion : right ≠ conclusion := tensorWellFormed.2.2.1
  rcases connected.toSimple with ⟨steps, visited, simple⟩
  have avoidsVisited : conclusion ∉ visited :=
    certificate.fullGraphWithoutVertex_simpleWalk_avoids conclusion simple
      leftNeConclusion
  have edgeSubset : ∀ edge ∈
      (certificate.fullGraphWithoutVertex conclusion).edges,
      edge ∈ certificate.fullGraph.edges := by
    intro edge membership
    have fullMembership := (List.mem_filter.mp membership).1
    simpa [fullGraph] using fullMembership
  rcases simple.liftToEdgeSimplePath edgeSubset with
    ⟨path, pathStarts, pathFinishes, pathVertices⟩
  have pathAvoidsConclusion : conclusion ∉ path.vertices := by
    rw [pathVertices]
    exact avoidsVisited
  have pathNonempty : path.traversed ≠ [] := by
    intro empty
    have chain := path.walk.toChain
    rw [empty] at chain
    have startFinish := chain.eq_of_nil
    apply leftNeRight
    exact pathStarts.symm.trans (startFinish.trans pathFinishes)
  rcases certificate.tensor_incidenceColors_exist terminal.1 leftNeRight with
    ⟨leftIncidence, rightIncidence, leftSource, leftTarget, rightSource,
      rightTarget, leftColor, rightColor, indicesDifferent⟩
  let returnPath : certificate.fullGraph.EdgeSimplePath :=
    { start := right
      finish := left
      traversed := [rightIncidence, leftIncidence.reverse]
      walk := by
        have firstStep : certificate.fullGraph.EdgeWalk right
            [rightIncidence] conclusion := by
          simpa using Graph.EdgeWalk.step (.refl right) rightIncidence
            rightSource rightTarget
        have secondStep := Graph.EdgeWalk.step firstStep leftIncidence.reverse
          (by simpa using leftTarget) (by simpa using leftSource)
        simpa using secondStep
      verticesNodup := by
        change (right :: rightIncidence.target ::
          leftIncidence.reverse.target :: []).Nodup
        rw [rightTarget, Graph.DirectedEdge.reverse_target, leftSource]
        simp [rightNeConclusion, leftNeConclusion, leftNeRight, ne_comm] }
  have returnNonempty : returnPath.traversed ≠ [] := by
    simp [returnPath]
  have vertexDisjoint : ∀ vertex, vertex ∈ path.vertices →
      vertex ∈ returnPath.vertices.tail.dropLast → False := by
    intro vertex inPath inReturnInterior
    have atConclusion : vertex = conclusion := by
      simpa [returnPath, Graph.EdgeSimplePath.vertices,
        Graph.EdgeWalk.visitedVertices, rightTarget, leftSource] using
        inReturnInterior
    subst vertex
    exact pathAvoidsConclusion inPath
  have edgeDisjoint : ∀ index,
      index ∈ path.traversed.map Graph.DirectedEdge.index →
      index ∈ returnPath.traversed.map Graph.DirectedEdge.index → False := by
    intro index inPathIndices inReturnIndices
    rcases List.mem_map.mp inPathIndices with
      ⟨directed, directedMembership, directedIndex⟩
    have endpoints := path.walk.endpoints_mem_visitedVertices directedMembership
    change directed.source ∈ path.vertices ∧
      directed.target ∈ path.vertices at endpoints
    have returnIndex : index = rightIncidence.index ∨
        index = leftIncidence.index := by
      simpa [returnPath] using inReturnIndices
    rcases returnIndex with atRight | atLeft
    · have sameIndex : directed.index = rightIncidence.index :=
        directedIndex.trans atRight
      rcases Graph.DirectedEdge.eq_or_eq_reverse_of_index_eq
          directed rightIncidence sameIndex with same | reversed
      · apply pathAvoidsConclusion
        rw [same, rightTarget] at endpoints
        exact endpoints.2
      · apply pathAvoidsConclusion
        rw [reversed, Graph.DirectedEdge.reverse_source, rightTarget] at endpoints
        exact endpoints.1
    · have sameIndex : directed.index = leftIncidence.index :=
        directedIndex.trans atLeft
      rcases Graph.DirectedEdge.eq_or_eq_reverse_of_index_eq
          directed leftIncidence sameIndex with same | reversed
      · apply pathAvoidsConclusion
        rw [same, leftTarget] at endpoints
        exact endpoints.2
      · apply pathAvoidsConclusion
        rw [reversed, Graph.DirectedEdge.reverse_source, leftTarget] at endpoints
        exact endpoints.1
  let closed := Graph.EdgeSimpleCycle.ofTwoPaths path returnPath pathNonempty
    returnNonempty (by simpa [returnPath] using pathFinishes)
      (by simpa [returnPath] using pathStarts.symm) vertexDisjoint edgeDisjoint
  have closedSteps : closed.traversed =
      (path.traversed ++ [rightIncidence]) ++
        leftIncidence.reverse :: [] := by
    simp [closed, returnPath, List.append_assoc]
  rcases closed.rotateAt_exists closedSteps with
    ⟨based, basedStarts, basedSteps⟩
  have basedAtConclusion : based.start = conclusion := by
    exact basedStarts.trans (by simpa using leftTarget)
  have basedHeadOption : based.traversed.head? =
      some leftIncidence.reverse := by
    rw [basedSteps]
    simp
  have basedHead : based.traversed.head based.nonempty =
      leftIncidence.reverse :=
    List.head_of_head?_eq_some basedHeadOption
  have basedLastOption : based.traversed.getLast? =
      some rightIncidence := by
    rw [basedSteps, List.getLast?_append]
    simp
  have basedLast : based.traversed.getLast based.nonempty =
      rightIncidence :=
    List.getLast_of_getLast?_eq_some basedLastOption
  have closingFree : ¬certificate.ClosingCusp based := by
    intro closing
    unfold ClosingCusp at closing
    rw [basedLast, basedHead] at closing
    unfold Cusp at closing
    simp only [Graph.DirectedEdge.reverse_reverse] at closing
    rw [rightColor, leftColor] at closing
    have sameIndex : rightIncidence.index = leftIncidence.index := by
      injection closing
    exact indicesDifferent sameIndex.symm
  exact closingFree (splitting based basedAtConclusion)

/-- Global terminal-rule existence for every declaratively correct
certificate containing a connective.  Parametrized generalized Yeo supplies a
terminal colored-splitting connective target; exact producer inversion then
distinguishes the terminal par case from the terminal tensor case, where the
colored-to-separator bridge supplies `SplittingTensor`. -/
theorem DeclarativelyCorrect.terminalPar_or_splittingTensor_exists
    {certificate : Certificate}
    (correct : certificate.DeclarativelyCorrect)
    (connectiveExists : ∃ link ∈ certificate.links,
      link.isConnective = true) :
    ∃ left right conclusion,
      certificate.TerminalPar left right conclusion ∨
        certificate.SplittingTensor left right conclusion := by
  have acyclic := correct.cuspAcyclic
  rcases acyclic.exists_terminal_splitting_target certificate correct.1
      connectiveExists with
    ⟨maximal, maximalEdge, terminalTarget, splittingTarget⟩
  rcases maximalEdge.2 with ⟨producer, producerMembership, produces⟩
  cases producer with
  | «axiom» left right => simp [Link.produces] at produces
  | tensor left right conclusion =>
      have target : conclusion = maximal.target := by
        simpa [Link.produces] using produces
      have terminal : certificate.TerminalTensor left right conclusion :=
        ⟨producerMembership, by simpa [target] using terminalTarget⟩
      have splitting : certificate.SplittingVertex conclusion := by
        simpa [target] using splittingTarget
      exact ⟨left, right, conclusion, .inr
        (splitting.toSplittingTensor correct.1 terminal)⟩
  | par left right conclusion =>
      have target : conclusion = maximal.target := by
        simpa [Link.produces] using produces
      have terminal : certificate.TerminalPar left right conclusion :=
        ⟨producerMembership, by simpa [target] using terminalTarget⟩
      exact ⟨left, right, conclusion, .inl terminal⟩

theorem terminalPar_or_splittingTensor_exists_of_check
    {certificate : Certificate} (accepted : certificate.check = true)
    (connectiveExists : ∃ link ∈ certificate.links,
      link.isConnective = true) :
    ∃ left right conclusion,
      certificate.TerminalPar left right conclusion ∨
        certificate.SplittingTensor left right conclusion :=
  (certificate.check_sound_declarative accepted).terminalPar_or_splittingTensor_exists
    connectiveExists

/-- Every structurally well-formed certificate containing a multiplicative
link has a terminal multiplicative link. Choose a connective conclusion of
maximal formula complexity; if it had a parent, local typing would give a
strictly more complex connective conclusion, contradicting maximality. -/
theorem terminalConnective_exists
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    (connectiveExists : ∃ link ∈ certificate.links,
      link.isConnective = true) :
    ∃ left right conclusion,
      certificate.TerminalPar left right conclusion ∨
      certificate.TerminalTensor left right conclusion := by
  let connectiveLinks := certificate.links.filter Link.isConnective
  have connectiveNonempty : connectiveLinks ≠ [] := by
    intro empty
    rcases connectiveExists with ⟨link, linkMembership, connective⟩
    have filteredMembership : link ∈ connectiveLinks :=
      List.mem_filter.mpr ⟨linkMembership, connective⟩
    rw [empty] at filteredMembership
    simp at filteredMembership
  cases listEquation : connectiveLinks with
  | nil => exact False.elim (connectiveNonempty listEquation)
  | cons head tail =>
      rcases exists_maximal_measure head tail
          certificate.linkConclusionComplexity with
        ⟨maximal, maximalMembership, maximalBound⟩
      have maximalFiltered : maximal ∈ connectiveLinks := by
        rw [listEquation]
        exact maximalMembership
      have maximalData := List.mem_filter.mp maximalFiltered
      have maximalBoundary : ∀ left right conclusion,
          maximal = .tensor left right conclusion ∨
            maximal = .par left right conclusion →
          conclusion ∈ certificate.conclusions := by
        intro left right conclusion connectiveShape
        have maximalWellFormed := structural.2.2.2.2.1 maximal maximalData.1
        have conclusionInBounds : conclusion < certificate.formulas.size := by
          rcases connectiveShape with tensorShape | parShape
          · subst maximal
            exact maximalWellFormed.2.2.2.2.2.1
          · subst maximal
            exact maximalWellFormed.2.2.2.2.2.1
        by_cases boundary : conclusion ∈ certificate.conclusions
        · exact boundary
        · have notBoundary := boundary
          have conclusionNode :=
            structural.2.2.2.2.2 conclusion conclusionInBounds
          have parentCount : certificate.parentUseCount conclusion = 1 := by
            simpa [Certificate.NodeWellFormed, notBoundary] using conclusionNode.2
          unfold parentUseCount at parentCount
          rcases List.length_eq_one_iff.mp parentCount with
            ⟨parent, parentFilterEquation⟩
          have parentFiltered : parent ∈ certificate.links.filter
              (fun link => link.usesAsPremise conclusion) := by
            rw [parentFilterEquation]
            simp
          rcases List.mem_filter.mp parentFiltered with
            ⟨parentMembership, parentUses⟩
          have premiseMembership : conclusion ∈ parent.premises := by
            simpa [Link.usesAsPremise] using parentUses
          have parentConnective : parent.isConnective = true := by
            cases parent with
            | «axiom» first second => simp [Link.premises] at premiseMembership
            | tensor first second result => rfl
            | par first second result => rfl
          have parentInConnectives : parent ∈ connectiveLinks :=
            List.mem_filter.mpr ⟨parentMembership, parentConnective⟩
          have parentInMaximalList : parent ∈ head :: tail := by
            rw [← listEquation]
            exact parentInConnectives
          have parentUpper := maximalBound parent parentInMaximalList
          have parentWellFormed := structural.2.2.2.2.1 parent parentMembership
          have strictGrowth :=
            parentWellFormed.premise_complexity_lt_conclusion premiseMembership
          rcases connectiveShape with tensorShape | parShape
          · subst maximal
            change certificate.linkConclusionComplexity parent ≤
              certificate.formulaComplexityAt conclusion at parentUpper
            omega
          · subst maximal
            change certificate.linkConclusionComplexity parent ≤
              certificate.formulaComplexityAt conclusion at parentUpper
            omega
      cases maximal with
      | «axiom» first second => simp [Link.isConnective] at maximalData
      | tensor left right conclusion =>
          exact ⟨left, right, conclusion, Or.inr
            ⟨maximalData.1,
              maximalBoundary left right conclusion (Or.inl rfl)⟩⟩
      | par left right conclusion =>
          exact ⟨left, right, conclusion, Or.inl
            ⟨maximalData.1,
              maximalBoundary left right conclusion (Or.inr rfl)⟩⟩

theorem LinkWellFormed.par_conclusionFormula
    {certificate : Certificate} {left right conclusion : Vertex}
    (wellFormed : certificate.LinkWellFormed (.par left right conclusion)) :
    ∃ leftFormula rightFormula,
      certificate.formula? conclusion =
        some (.par leftFormula rightFormula) := by
  rcases wellFormed with ⟨_, _, _, _, _, _, typing⟩
  cases leftEquation : certificate.formula? left with
  | none => simp [leftEquation] at typing
  | some leftFormula =>
      cases rightEquation : certificate.formula? right with
      | none => simp [leftEquation, rightEquation] at typing
      | some rightFormula =>
          cases conclusionEquation : certificate.formula? conclusion with
          | none =>
              simp [leftEquation, rightEquation, conclusionEquation] at typing
          | some conclusionFormula =>
              simp [leftEquation, rightEquation, conclusionEquation] at typing
              subst conclusionFormula
              exact ⟨leftFormula, rightFormula, rfl⟩

/-- Full formula data carried by a well-formed par link, including both premise
occurrences. -/
theorem LinkWellFormed.par_formulaData
    {certificate : Certificate} {left right conclusion : Vertex}
    (wellFormed : certificate.LinkWellFormed (.par left right conclusion)) :
    ∃ leftFormula rightFormula,
      certificate.formula? left = some leftFormula ∧
      certificate.formula? right = some rightFormula ∧
      certificate.formula? conclusion =
        some (.par leftFormula rightFormula) := by
  rcases wellFormed with ⟨_, _, _, _, _, _, typing⟩
  cases leftEquation : certificate.formula? left with
  | none => simp [leftEquation] at typing
  | some leftFormula =>
      cases rightEquation : certificate.formula? right with
      | none => simp [leftEquation, rightEquation] at typing
      | some rightFormula =>
          cases conclusionEquation : certificate.formula? conclusion with
          | none =>
              simp [leftEquation, rightEquation, conclusionEquation] at typing
          | some conclusionFormula =>
              simp [leftEquation, rightEquation, conclusionEquation] at typing
              subst conclusionFormula
              refine ⟨leftFormula, rightFormula, ?_, ?_, ?_⟩
              · simpa using leftEquation
              · simpa using rightEquation
              · simpa using conclusionEquation

theorem LinkWellFormed.tensor_conclusionFormula
    {certificate : Certificate} {left right conclusion : Vertex}
    (wellFormed : certificate.LinkWellFormed (.tensor left right conclusion)) :
    ∃ leftFormula rightFormula,
      certificate.formula? conclusion =
        some (.tensor leftFormula rightFormula) := by
  rcases wellFormed with ⟨_, _, _, _, _, _, typing⟩
  cases leftEquation : certificate.formula? left with
  | none => simp [leftEquation] at typing
  | some leftFormula =>
      cases rightEquation : certificate.formula? right with
      | none => simp [leftEquation, rightEquation] at typing
      | some rightFormula =>
          cases conclusionEquation : certificate.formula? conclusion with
          | none =>
              simp [leftEquation, rightEquation, conclusionEquation] at typing
          | some conclusionFormula =>
              simp [leftEquation, rightEquation, conclusionEquation] at typing
              subst conclusionFormula
              exact ⟨leftFormula, rightFormula, rfl⟩

theorem LinkWellFormed.vertex_in_bounds
    {certificate : Certificate} {link : Link}
    (wellFormed : certificate.LinkWellFormed link)
    {vertex : Vertex} (membership : vertex ∈ link.vertices) :
    vertex < certificate.formulas.size := by
  cases link with
  | «axiom» left right =>
      simp [Link.vertices] at membership
      rcases membership with rfl | rfl
      · exact wellFormed.2.1
      · exact wellFormed.2.2.1
  | tensor left right conclusion =>
      simp [Link.vertices] at membership
      rcases membership with rfl | rfl | rfl
      · exact wellFormed.2.2.2.1
      · exact wellFormed.2.2.2.2.1
      · exact wellFormed.2.2.2.2.2.1
  | par left right conclusion =>
      simp [Link.vertices] at membership
      rcases membership with rfl | rfl | rfl
      · exact wellFormed.2.2.2.1
      · exact wellFormed.2.2.2.2.1
      · exact wellFormed.2.2.2.2.2.1

theorem LinkWellFormed.axiom_endpointFormula
    {certificate : Certificate} {left right vertex : Vertex}
    (wellFormed : certificate.LinkWellFormed (.axiom left right))
    (endpoint : vertex = left ∨ vertex = right) :
    ∃ name positive,
      certificate.formula? vertex = some (.atom name positive) := by
  rcases wellFormed with ⟨_, _, _, typing⟩
  cases leftEquation : certificate.formula? left with
  | none => simp [leftEquation] at typing
  | some leftFormula =>
      cases leftFormula with
      | tensor first second => simp [leftEquation] at typing
      | par first second => simp [leftEquation] at typing
      | atom name positive =>
          cases rightEquation : certificate.formula? right with
          | none => simp [leftEquation, rightEquation] at typing
          | some rightFormula =>
              simp [leftEquation, rightEquation] at typing
              rcases endpoint with rfl | rfl
              · exact ⟨name, positive, by simpa using leftEquation⟩
              · subst rightFormula
                exact ⟨name, !positive, by
                  simpa [Formula.dual] using rightEquation⟩

namespace TerminalPar

theorem ownership {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalPar left right conclusion) :
    certificate.producerCount conclusion = 1 ∧
      certificate.parentUseCount conclusion = 0 ∧
      ∃ leftFormula rightFormula,
        certificate.formula? conclusion =
          some (.par leftFormula rightFormula) := by
  rcases structural with ⟨_, _, conclusionsInBounds, _, linksWellFormed,
    nodesWellFormed⟩
  have terminalWellFormed := linksWellFormed _ terminal.1
  rcases terminalWellFormed.par_conclusionFormula with
    ⟨leftFormula, rightFormula, conclusionFormula⟩
  have node := nodesWellFormed conclusion
    (conclusionsInBounds conclusion terminal.2)
  simp [NodeWellFormed, conclusionFormula, terminal.2] at node
  exact ⟨node.1, node.2, leftFormula, rightFormula, conclusionFormula⟩

theorem premises_not_conclusions
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalPar left right conclusion) :
    left ∉ certificate.conclusions ∧ right ∉ certificate.conclusions := by
  have terminalWellFormed := structural.2.2.2.2.1 _ terminal.1
  rcases terminalWellFormed with
    ⟨_, _, _, leftInBounds, rightInBounds, _, _⟩
  constructor
  · intro leftConclusion
    have node := structural.2.2.2.2.2 left leftInBounds
    have parentZero := node.2
    simp [leftConclusion] at parentZero
    change (certificate.links.filter (·.usesAsPremise left)).length = 0 at parentZero
    exact false_of_mem_filter_length_zero parentZero terminal.1
      (by simp [Link.usesAsPremise, Link.premises])
  · intro rightConclusion
    have node := structural.2.2.2.2.2 right rightInBounds
    have parentZero := node.2
    simp [rightConclusion] at parentZero
    change (certificate.links.filter (·.usesAsPremise right)).length = 0 at parentZero
    exact false_of_mem_filter_length_zero parentZero terminal.1
      (by simp [Link.usesAsPremise, Link.premises])

theorem producer_unique {certificate : Certificate}
    {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalPar left right conclusion)
    {link : Link} (membership : link ∈ certificate.links)
    (produces : link.produces conclusion = true) :
    link = .par left right conclusion := by
  have producerCount := (TerminalPar.ownership structural terminal).1
  change (certificate.links.filter (·.produces conclusion)).length = 1 at producerCount
  apply eq_of_mem_filter_length_one
    (predicate := (·.produces conclusion))
    producerCount
    membership produces terminal.1
  simp [Link.produces]

theorem producer_filter_eq {certificate : Certificate}
    {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalPar left right conclusion) :
    certificate.links.filter (·.produces conclusion) =
      [.par left right conclusion] := by
  have count := (TerminalPar.ownership structural terminal).1
  change (certificate.links.filter (·.produces conclusion)).length = 1 at count
  rcases List.length_eq_one_iff.mp count with ⟨only, equation⟩
  have terminalFiltered : Link.par left right conclusion ∈
      certificate.links.filter (·.produces conclusion) := by
    simp [terminal.1, Link.produces]
  rw [equation] at terminalFiltered
  simp at terminalFiltered
  subst only
  exact equation

theorem no_parentUse {certificate : Certificate}
    {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalPar left right conclusion)
    {link : Link} (membership : link ∈ certificate.links)
    (uses : link.usesAsPremise conclusion = true) : False := by
  have parentCount := (TerminalPar.ownership structural terminal).2.1
  change (certificate.links.filter (·.usesAsPremise conclusion)).length = 0 at parentCount
  exact false_of_mem_filter_length_zero
    (predicate := (·.usesAsPremise conclusion))
    parentCount membership uses

theorem unique_incident {certificate : Certificate}
    {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalPar left right conclusion)
    {link : Link} (membership : link ∈ certificate.links)
    (incident : conclusion ∈ link.vertices) :
    link = .par left right conclusion := by
  have conclusionFormula :=
    (TerminalPar.ownership structural terminal).2.2
  cases link with
  | «axiom» first second =>
      have endpoint : conclusion = first ∨ conclusion = second := by
        simpa [Link.vertices] using incident
      have axiomWellFormed := structural.2.2.2.2.1 _ membership
      rcases axiomWellFormed.axiom_endpointFormula endpoint with
        ⟨name, positive, atomFormula⟩
      rcases conclusionFormula with
        ⟨leftFormula, rightFormula, parFormula⟩
      rw [parFormula] at atomFormula
      cases atomFormula
  | tensor first second result =>
      simp [Link.vertices] at incident
      rcases incident with same | same | same
      · subst first
        exact False.elim (TerminalPar.no_parentUse structural terminal
          membership (by simp [Link.usesAsPremise, Link.premises]))
      · subst second
        exact False.elim (TerminalPar.no_parentUse structural terminal
          membership (by simp [Link.usesAsPremise, Link.premises]))
      · subst result
        exact TerminalPar.producer_unique structural terminal membership
          (by simp [Link.produces])
  | par first second result =>
      simp [Link.vertices] at incident
      rcases incident with same | same | same
      · subst first
        exact False.elim (TerminalPar.no_parentUse structural terminal
          membership (by simp [Link.usesAsPremise, Link.premises]))
      · subst second
        exact False.elim (TerminalPar.no_parentUse structural terminal
          membership (by simp [Link.usesAsPremise, Link.premises]))
      · subst result
        exact TerminalPar.producer_unique structural terminal membership
          (by simp [Link.produces])

theorem deletion_none_iff_eq
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalPar left right conclusion)
    {link : Link} (membership : link ∈ certificate.links) :
    link.deleteVertex? conclusion = none ↔
      link = .par left right conclusion := by
  constructor
  · intro deleted
    exact TerminalPar.unique_incident structural terminal membership
      ((Link.deleteVertex?_eq_none_iff link conclusion).mp deleted)
  · intro same
    subst link
    simp [Link.deleteVertex?, Certificate.deleteVertex?]

theorem terminal_not_mem_remaining
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalPar left right conclusion) :
    Link.par left right conclusion ∉
      certificate.links.erase (.par left right conclusion) := by
  have countOriginal : certificate.links.count (.par left right conclusion) = 1 := by
    rw [← List.count_filter (p := (·.produces conclusion)) (by
      simp [Link.produces])]
    rw [TerminalPar.producer_filter_eq structural terminal]
    simp
  apply List.count_eq_zero.mp
  simp [countOriginal]

end TerminalPar

namespace TerminalTensor

theorem mem_tensorLeftVertices_iff (certificate : Certificate)
    (left conclusion vertex : Vertex) :
    vertex ∈ certificate.tensorLeftVertices left conclusion ↔
      vertex < certificate.formulas.size ∧ vertex ≠ conclusion ∧
        vertex ∈ certificate.tensorLeftReachable left conclusion := by
  simp [tensorLeftVertices]

theorem mem_tensorRightVertices_iff (certificate : Certificate)
    (left conclusion vertex : Vertex) :
    vertex ∈ certificate.tensorRightVertices left conclusion ↔
      vertex < certificate.formulas.size ∧ vertex ≠ conclusion ∧
        vertex ∉ certificate.tensorLeftReachable left conclusion := by
  simp [tensorRightVertices]

theorem tensorLeftVertices_nodup (certificate : Certificate)
    (left conclusion : Vertex) :
    (certificate.tensorLeftVertices left conclusion).Nodup :=
  List.filter_sublist.nodup List.nodup_range

theorem tensorRightVertices_nodup (certificate : Certificate)
    (left conclusion : Vertex) :
    (certificate.tensorRightVertices left conclusion).Nodup :=
  List.filter_sublist.nodup List.nodup_range

theorem conclusion_not_mem_tensorLeftVertices (certificate : Certificate)
    (left conclusion : Vertex) :
    conclusion ∉ certificate.tensorLeftVertices left conclusion := by
  intro membership
  exact (TerminalTensor.mem_tensorLeftVertices_iff certificate
    left conclusion conclusion).mp membership |>.2.1 rfl

theorem conclusion_not_mem_tensorRightVertices (certificate : Certificate)
    (left conclusion : Vertex) :
    conclusion ∉ certificate.tensorRightVertices left conclusion := by
  intro membership
  exact (TerminalTensor.mem_tensorRightVertices_iff certificate
    left conclusion conclusion).mp membership |>.2.1 rfl

theorem vertex_partition (certificate : Certificate)
    (left conclusion vertex : Vertex)
    (vertexInBounds : vertex < certificate.formulas.size)
    (vertexNotConclusion : vertex ≠ conclusion) :
    vertex ∈ certificate.tensorLeftVertices left conclusion ∨
      vertex ∈ certificate.tensorRightVertices left conclusion := by
  by_cases reachable :
      vertex ∈ certificate.tensorLeftReachable left conclusion
  · exact Or.inl ((mem_tensorLeftVertices_iff certificate
      left conclusion vertex).mpr
      ⟨vertexInBounds, vertexNotConclusion, reachable⟩)
  · exact Or.inr ((mem_tensorRightVertices_iff certificate
      left conclusion vertex).mpr
      ⟨vertexInBounds, vertexNotConclusion, reachable⟩)

theorem vertex_partition_disjoint (certificate : Certificate)
    (left conclusion : Vertex) :
    ∀ vertex,
      vertex ∈ certificate.tensorLeftVertices left conclusion →
      vertex ∈ certificate.tensorRightVertices left conclusion → False := by
  intro vertex leftMembership rightMembership
  have reachable := (mem_tensorLeftVertices_iff certificate
    left conclusion vertex).mp leftMembership |>.2.2
  have unreachable := (mem_tensorRightVertices_iff certificate
    left conclusion vertex).mp rightMembership |>.2.2
  exact unreachable reachable

theorem tensorVertices_length_partition
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalTensor left right conclusion) :
    (certificate.tensorLeftVertices left conclusion).length +
        (certificate.tensorRightVertices left conclusion).length + 1 =
      certificate.formulas.size := by
  let reachable := certificate.tensorLeftReachable left conclusion
  have partition := length_filter_three_partition
    (List.range certificate.formulas.size)
    (fun vertex => vertex != conclusion && reachable.contains vertex)
    (fun vertex => vertex != conclusion && !reachable.contains vertex)
    (fun vertex => vertex == conclusion) (by
      intro vertex membership
      by_cases same : vertex = conclusion
      · subst vertex
        simp
      · cases reachableEquation : reachable.contains vertex with
        | false => exact Or.inr (Or.inl (by simp [same]))
        | true => exact Or.inl (by simp [same]))
  have terminalWellFormed := structural.2.2.2.2.1 _ terminal.1
  have conclusionInBounds := terminalWellFormed.2.2.2.2.2.1
  have conclusionCount := length_filter_eq_vertex_of_lt
    certificate.formulas.size conclusion conclusionInBounds
  rw [conclusionCount] at partition
  simpa [tensorLeftVertices, tensorRightVertices, reachable] using partition

theorem reachable_iff_walk
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalTensor left right conclusion) :
    right ∈ (certificate.fullGraphWithoutVertex conclusion).closureN
        certificate.formulas.size [left] ↔
      (certificate.fullGraphWithoutVertex conclusion).Walk left right := by
  have terminalWellFormed := structural.2.2.2.2.1 _ terminal.1
  have bounded := certificate.fullGraphWithoutVertex_bounded structural
    conclusion
  exact Graph.mem_closureN_vertexCount_iff_walk _ bounded
    terminalWellFormed.2.2.2.1 terminalWellFormed.2.2.2.2.1

theorem left_mem_tensorLeftVertices
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalTensor left right conclusion) :
    left ∈ certificate.tensorLeftVertices left conclusion := by
  have terminalWellFormed := structural.2.2.2.2.1 _ terminal.1
  apply (mem_tensorLeftVertices_iff certificate
    left conclusion left).mpr
  refine ⟨terminalWellFormed.2.2.2.1,
    terminalWellFormed.2.1, ?_⟩
  unfold tensorLeftReachable
  apply (Graph.mem_closureN_vertexCount_iff_walk _
    (certificate.fullGraphWithoutVertex_bounded structural conclusion)
    terminalWellFormed.2.2.2.1 terminalWellFormed.2.2.2.1).mpr
  exact .refl left

theorem right_mem_tensorRightVertices
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (splitting : certificate.SplittingTensor left right conclusion) :
    right ∈ certificate.tensorRightVertices left conclusion := by
  have terminalWellFormed := structural.2.2.2.2.1 _ splitting.1.1
  apply (mem_tensorRightVertices_iff certificate
    left conclusion right).mpr
  refine ⟨terminalWellFormed.2.2.2.2.1,
    terminalWellFormed.2.2.1, ?_⟩
  intro reachable
  exact splitting.2
    ((TerminalTensor.reachable_iff_walk structural splitting.1).mp reachable)

theorem tensorLeftVertices_in_bounds (certificate : Certificate)
    (left conclusion : Vertex) :
    ∀ vertex ∈ certificate.tensorLeftVertices left conclusion,
      vertex < certificate.formulas.size := by
  intro vertex membership
  exact (TerminalTensor.mem_tensorLeftVertices_iff certificate
    left conclusion vertex).mp membership |>.1

theorem tensorRightVertices_in_bounds (certificate : Certificate)
    (left conclusion : Vertex) :
    ∀ vertex ∈ certificate.tensorRightVertices left conclusion,
      vertex < certificate.formulas.size := by
  intro vertex membership
  exact (TerminalTensor.mem_tensorRightVertices_iff certificate
    left conclusion vertex).mp membership |>.1

theorem tensorLeftBoundary_contained
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalTensor left right conclusion) :
    ∀ vertex ∈ certificate.tensorLeftBoundary left conclusion,
      vertex ∈ certificate.tensorLeftVertices left conclusion := by
  intro vertex membership
  change vertex ∈
      (certificate.tensorOtherConclusions conclusion).filter
          (certificate.tensorLeftVertices left conclusion).contains ++
        [left] at membership
  rw [List.mem_append] at membership
  rcases membership with filtered | same
  · have contained := (List.mem_filter.mp filtered).2
    simpa using contained
  · simp at same
    subst vertex
    exact TerminalTensor.left_mem_tensorLeftVertices structural terminal

theorem tensorRightBoundary_contained
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (splitting : certificate.SplittingTensor left right conclusion) :
    ∀ vertex ∈ certificate.tensorRightBoundary left right conclusion,
      vertex ∈ certificate.tensorRightVertices left conclusion := by
  intro vertex membership
  change vertex ∈
      (certificate.tensorOtherConclusions conclusion).filter
          (certificate.tensorRightVertices left conclusion).contains ++
        [right] at membership
  rw [List.mem_append] at membership
  rcases membership with filtered | same
  · have contained := (List.mem_filter.mp filtered).2
    simpa using contained
  · simp at same
    subst vertex
    exact TerminalTensor.right_mem_tensorRightVertices structural splitting

theorem mem_tensorLeftBoundary_iff
    {certificate : Certificate} {left conclusion vertex : Vertex}
    (vertexMembership :
      vertex ∈ certificate.tensorLeftVertices left conclusion) :
    vertex ∈ certificate.tensorLeftBoundary left conclusion ↔
      vertex ∈ certificate.conclusions ∨ vertex = left := by
  have vertexNotConclusion :=
    (TerminalTensor.mem_tensorLeftVertices_iff certificate
      left conclusion vertex).mp vertexMembership |>.2.1
  constructor
  · intro membership
    rw [tensorLeftBoundary, List.mem_append] at membership
    rcases membership with filtered | root
    · exact Or.inl (List.mem_of_mem_erase (List.mem_filter.mp filtered).1)
    · exact Or.inr (by simpa using root)
  · intro membership
    rw [tensorLeftBoundary, List.mem_append]
    rcases membership with original | rfl
    · left
      apply List.mem_filter.mpr
      exact ⟨(List.mem_erase_of_ne vertexNotConclusion).mpr original,
        by simpa using vertexMembership⟩
    · simp

theorem mem_tensorRightBoundary_iff
    {certificate : Certificate} {left right conclusion vertex : Vertex}
    (vertexMembership :
      vertex ∈ certificate.tensorRightVertices left conclusion) :
    vertex ∈ certificate.tensorRightBoundary left right conclusion ↔
      vertex ∈ certificate.conclusions ∨ vertex = right := by
  have vertexNotConclusion :=
    (TerminalTensor.mem_tensorRightVertices_iff certificate
      left conclusion vertex).mp vertexMembership |>.2.1
  constructor
  · intro membership
    rw [tensorRightBoundary, List.mem_append] at membership
    rcases membership with filtered | root
    · exact Or.inl (List.mem_of_mem_erase (List.mem_filter.mp filtered).1)
    · exact Or.inr (by simpa using root)
  · intro membership
    rw [tensorRightBoundary, List.mem_append]
    rcases membership with original | rfl
    · left
      apply List.mem_filter.mpr
      exact ⟨(List.mem_erase_of_ne vertexNotConclusion).mpr original,
        by simpa using vertexMembership⟩
    · simp

theorem tensorLeftVertices_length_pos
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalTensor left right conclusion) :
    0 < (certificate.tensorLeftVertices left conclusion).length :=
  List.length_pos_of_mem
    (TerminalTensor.left_mem_tensorLeftVertices structural terminal)

theorem tensorRightVertices_length_pos
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (splitting : certificate.SplittingTensor left right conclusion) :
    0 < (certificate.tensorRightVertices left conclusion).length :=
  List.length_pos_of_mem
    (TerminalTensor.right_mem_tensorRightVertices structural splitting)

theorem tensorLeftBoundary_length_pos (certificate : Certificate)
    (left conclusion : Vertex) :
    0 < (certificate.tensorLeftBoundary left conclusion).length := by
  simp [tensorLeftBoundary]

theorem tensorRightBoundary_length_pos (certificate : Certificate)
    (left right conclusion : Vertex) :
    0 < (certificate.tensorRightBoundary left right conclusion).length := by
  simp [tensorRightBoundary]

theorem splitting_iff_reachability_rejected
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalTensor left right conclusion) :
    certificate.SplittingTensor left right conclusion ↔
      ((certificate.fullGraphWithoutVertex conclusion).closureN
        certificate.formulas.size [left]).contains right = false := by
  have reachability := TerminalTensor.reachable_iff_walk structural terminal
  constructor
  · intro splitting
    have noMembership : right ∉
        (certificate.fullGraphWithoutVertex conclusion).closureN
          certificate.formulas.size [left] := by
      intro membership
      exact splitting.2 (reachability.mp membership)
    simpa using noMembership
  · intro rejected
    refine ⟨terminal, ?_⟩
    intro walk
    have membership := reachability.mpr walk
    have accepted :
        ((certificate.fullGraphWithoutVertex conclusion).closureN
          certificate.formulas.size [left]).contains right = true := by
      simpa using membership
    rw [accepted] at rejected
    cases rejected

theorem ownership {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalTensor left right conclusion) :
    certificate.producerCount conclusion = 1 ∧
      certificate.parentUseCount conclusion = 0 ∧
      ∃ leftFormula rightFormula,
        certificate.formula? conclusion =
          some (.tensor leftFormula rightFormula) := by
  rcases structural with ⟨_, _, conclusionsInBounds, _, linksWellFormed,
    nodesWellFormed⟩
  have terminalWellFormed := linksWellFormed _ terminal.1
  rcases terminalWellFormed.tensor_conclusionFormula with
    ⟨leftFormula, rightFormula, conclusionFormula⟩
  have node := nodesWellFormed conclusion
    (conclusionsInBounds conclusion terminal.2)
  simp [NodeWellFormed, conclusionFormula, terminal.2] at node
  exact ⟨node.1, node.2, leftFormula, rightFormula, conclusionFormula⟩

theorem premises_not_conclusions
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalTensor left right conclusion) :
    left ∉ certificate.conclusions ∧ right ∉ certificate.conclusions := by
  have terminalWellFormed := structural.2.2.2.2.1 _ terminal.1
  rcases terminalWellFormed with
    ⟨_, _, _, leftInBounds, rightInBounds, _, _⟩
  constructor
  · intro leftConclusion
    have node := structural.2.2.2.2.2 left leftInBounds
    have parentZero := node.2
    simp [leftConclusion] at parentZero
    change (certificate.links.filter (·.usesAsPremise left)).length = 0 at parentZero
    exact false_of_mem_filter_length_zero parentZero terminal.1
      (by simp [Link.usesAsPremise, Link.premises])
  · intro rightConclusion
    have node := structural.2.2.2.2.2 right rightInBounds
    have parentZero := node.2
    simp [rightConclusion] at parentZero
    change (certificate.links.filter (·.usesAsPremise right)).length = 0 at parentZero
    exact false_of_mem_filter_length_zero parentZero terminal.1
      (by simp [Link.usesAsPremise, Link.premises])

theorem left_parent_unique
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalTensor left right conclusion)
    {link : Link} (membership : link ∈ certificate.links)
    (uses : link.usesAsPremise left = true) :
    link = .tensor left right conclusion := by
  have terminalWellFormed := structural.2.2.2.2.1 _ terminal.1
  have node := structural.2.2.2.2.2 left terminalWellFormed.2.2.2.1
  have parentCount := node.2
  simp [TerminalTensor.premises_not_conclusions structural terminal |>.1]
    at parentCount
  change (certificate.links.filter (·.usesAsPremise left)).length = 1
    at parentCount
  apply eq_of_mem_filter_length_one parentCount membership uses terminal.1
  simp [Link.usesAsPremise, Link.premises]

theorem right_parent_unique
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalTensor left right conclusion)
    {link : Link} (membership : link ∈ certificate.links)
    (uses : link.usesAsPremise right = true) :
    link = .tensor left right conclusion := by
  have terminalWellFormed := structural.2.2.2.2.1 _ terminal.1
  have node := structural.2.2.2.2.2 right terminalWellFormed.2.2.2.2.1
  have parentCount := node.2
  simp [TerminalTensor.premises_not_conclusions structural terminal |>.2]
    at parentCount
  change (certificate.links.filter (·.usesAsPremise right)).length = 1
    at parentCount
  apply eq_of_mem_filter_length_one parentCount membership uses terminal.1
  simp [Link.usesAsPremise, Link.premises]

theorem tensorLeftBoundary_nodup
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalTensor left right conclusion) :
    (certificate.tensorLeftBoundary left conclusion).Nodup := by
  have originalNodup : certificate.conclusions.Nodup :=
    nodup_of_eraseDups_length_eq structural.2.2.2.1
  have remainingNodup :
      (certificate.tensorOtherConclusions conclusion).Nodup := by
    exact originalNodup.erase conclusion
  have filteredNodup :
      ((certificate.tensorOtherConclusions conclusion).filter
        (certificate.tensorLeftVertices left conclusion).contains).Nodup :=
    List.filter_sublist.nodup remainingNodup
  have leftFresh : left ∉
      (certificate.tensorOtherConclusions conclusion).filter
        (certificate.tensorLeftVertices left conclusion).contains := by
    intro membership
    have remaining := (List.mem_filter.mp membership).1
    have original := List.mem_of_mem_erase remaining
    exact (TerminalTensor.premises_not_conclusions structural terminal).1
      original
  change (((certificate.tensorOtherConclusions conclusion).filter
      (certificate.tensorLeftVertices left conclusion).contains) ++
    [left]).Nodup
  rw [List.nodup_append]
  refine ⟨filteredNodup, by simp, ?_⟩
  intro vertex vertexMembership boundary boundaryMembership
  simp at boundaryMembership
  subst boundary
  intro same
  subst vertex
  exact leftFresh vertexMembership

theorem tensorRightBoundary_nodup
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalTensor left right conclusion) :
    (certificate.tensorRightBoundary left right conclusion).Nodup := by
  have originalNodup : certificate.conclusions.Nodup :=
    nodup_of_eraseDups_length_eq structural.2.2.2.1
  have remainingNodup :
      (certificate.tensorOtherConclusions conclusion).Nodup := by
    exact originalNodup.erase conclusion
  have filteredNodup :
      ((certificate.tensorOtherConclusions conclusion).filter
        (certificate.tensorRightVertices left conclusion).contains).Nodup :=
    List.filter_sublist.nodup remainingNodup
  have rightFresh : right ∉
      (certificate.tensorOtherConclusions conclusion).filter
        (certificate.tensorRightVertices left conclusion).contains := by
    intro membership
    have remaining := (List.mem_filter.mp membership).1
    have original := List.mem_of_mem_erase remaining
    exact (TerminalTensor.premises_not_conclusions structural terminal).2
      original
  change (((certificate.tensorOtherConclusions conclusion).filter
      (certificate.tensorRightVertices left conclusion).contains) ++
    [right]).Nodup
  rw [List.nodup_append]
  refine ⟨filteredNodup, by simp, ?_⟩
  intro vertex vertexMembership boundary boundaryMembership
  simp at boundaryMembership
  subst boundary
  intro same
  subst vertex
  exact rightFresh vertexMembership

theorem producer_unique {certificate : Certificate}
    {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalTensor left right conclusion)
    {link : Link} (membership : link ∈ certificate.links)
    (produces : link.produces conclusion = true) :
    link = .tensor left right conclusion := by
  have producerCount := (TerminalTensor.ownership structural terminal).1
  change (certificate.links.filter (·.produces conclusion)).length = 1 at producerCount
  apply eq_of_mem_filter_length_one
    (predicate := (·.produces conclusion))
    producerCount membership produces terminal.1
  simp [Link.produces]

theorem producer_filter_eq {certificate : Certificate}
    {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalTensor left right conclusion) :
    certificate.links.filter (·.produces conclusion) =
      [.tensor left right conclusion] := by
  have count := (TerminalTensor.ownership structural terminal).1
  change (certificate.links.filter (·.produces conclusion)).length = 1 at count
  rcases List.length_eq_one_iff.mp count with ⟨only, equation⟩
  have terminalFiltered : Link.tensor left right conclusion ∈
      certificate.links.filter (·.produces conclusion) := by
    simp [terminal.1, Link.produces]
  rw [equation] at terminalFiltered
  simp at terminalFiltered
  subst only
  exact equation

theorem no_parentUse {certificate : Certificate}
    {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalTensor left right conclusion)
    {link : Link} (membership : link ∈ certificate.links)
    (uses : link.usesAsPremise conclusion = true) : False := by
  have parentCount := (TerminalTensor.ownership structural terminal).2.1
  change (certificate.links.filter (·.usesAsPremise conclusion)).length = 0 at parentCount
  exact false_of_mem_filter_length_zero
    (predicate := (·.usesAsPremise conclusion))
    parentCount membership uses

theorem unique_incident {certificate : Certificate}
    {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalTensor left right conclusion)
    {link : Link} (membership : link ∈ certificate.links)
    (incident : conclusion ∈ link.vertices) :
    link = .tensor left right conclusion := by
  have conclusionFormula :=
    (TerminalTensor.ownership structural terminal).2.2
  cases link with
  | «axiom» first second =>
      have endpoint : conclusion = first ∨ conclusion = second := by
        simpa [Link.vertices] using incident
      have axiomWellFormed := structural.2.2.2.2.1 _ membership
      rcases axiomWellFormed.axiom_endpointFormula endpoint with
        ⟨name, positive, atomFormula⟩
      rcases conclusionFormula with
        ⟨leftFormula, rightFormula, tensorFormula⟩
      rw [tensorFormula] at atomFormula
      cases atomFormula
  | tensor first second result =>
      simp [Link.vertices] at incident
      rcases incident with same | same | same
      · subst first
        exact False.elim (TerminalTensor.no_parentUse structural terminal
          membership (by simp [Link.usesAsPremise, Link.premises]))
      · subst second
        exact False.elim (TerminalTensor.no_parentUse structural terminal
          membership (by simp [Link.usesAsPremise, Link.premises]))
      · subst result
        exact TerminalTensor.producer_unique structural terminal membership
          (by simp [Link.produces])
  | par first second result =>
      simp [Link.vertices] at incident
      rcases incident with same | same | same
      · subst first
        exact False.elim (TerminalTensor.no_parentUse structural terminal
          membership (by simp [Link.usesAsPremise, Link.premises]))
      · subst second
        exact False.elim (TerminalTensor.no_parentUse structural terminal
          membership (by simp [Link.usesAsPremise, Link.premises]))
      · subst result
        have impossible := TerminalTensor.producer_unique structural terminal
          membership (by simp [Link.produces])
        cases impossible

theorem nonterminal_avoids_conclusion
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalTensor left right conclusion)
    {link : Link} (membership : link ∈ certificate.links)
    (different : link ≠ .tensor left right conclusion) :
    conclusion ∉ link.vertices := by
  intro incident
  exact different (TerminalTensor.unique_incident structural terminal
    membership incident)

theorem link_reachable_iff
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalTensor left right conclusion)
    {link : Link} (linkMembership : link ∈ certificate.links)
    (different : link ≠ .tensor left right conclusion)
    {first second : Vertex}
    (firstMembership : first ∈ link.vertices)
    (secondMembership : second ∈ link.vertices) :
    first ∈ certificate.tensorLeftReachable left conclusion ↔
      second ∈ certificate.tensorLeftReachable left conclusion := by
  have avoids := TerminalTensor.nonterminal_avoids_conclusion structural
    terminal linkMembership different
  have linkWellFormed := structural.2.2.2.2.1 link linkMembership
  have firstInBounds := linkWellFormed.vertex_in_bounds firstMembership
  have secondInBounds := linkWellFormed.vertex_in_bounds secondMembership
  have terminalWellFormed := structural.2.2.2.2.1 _ terminal.1
  have leftInBounds := terminalWellFormed.2.2.2.1
  let graph := certificate.fullGraphWithoutVertex conclusion
  have graphBounded : graph.Bounded :=
    certificate.fullGraphWithoutVertex_bounded structural conclusion
  have firstReachability :
      first ∈ certificate.tensorLeftReachable left conclusion ↔
        graph.Walk left first := by
    unfold tensorLeftReachable
    exact Graph.mem_closureN_vertexCount_iff_walk graph graphBounded
      leftInBounds firstInBounds
  have secondReachability :
      second ∈ certificate.tensorLeftReachable left conclusion ↔
        graph.Walk left second := by
    unfold tensorLeftReachable
    exact Graph.mem_closureN_vertexCount_iff_walk graph graphBounded
      leftInBounds secondInBounds
  have internal : graph.Walk first second :=
    fullGraphWithoutVertex_link_vertices_walk linkMembership avoids
      firstMembership secondMembership
  constructor
  · intro firstReachable
    exact secondReachability.mpr
      ((firstReachability.mp firstReachable).trans internal)
  · intro secondReachable
    exact firstReachability.mpr
      ((secondReachability.mp secondReachable).trans internal.reverse)

theorem link_partition_from_vertex
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalTensor left right conclusion)
    {link : Link} (linkMembership : link ∈ certificate.links)
    (different : link ≠ .tensor left right conclusion)
    {pivot : Vertex} (pivotMembership : pivot ∈ link.vertices) :
    (∀ vertex ∈ link.vertices,
        vertex ∈ certificate.tensorLeftVertices left conclusion) ∨
      (∀ vertex ∈ link.vertices,
        vertex ∈ certificate.tensorRightVertices left conclusion) := by
  have avoids := TerminalTensor.nonterminal_avoids_conclusion structural
    terminal linkMembership different
  have linkWellFormed := structural.2.2.2.2.1 link linkMembership
  have pivotInBounds := linkWellFormed.vertex_in_bounds pivotMembership
  have pivotNotConclusion : pivot ≠ conclusion := by
    intro same
    subst pivot
    exact avoids pivotMembership
  rcases TerminalTensor.vertex_partition certificate left conclusion pivot
      pivotInBounds pivotNotConclusion with pivotLeft | pivotRight
  · left
    intro vertex vertexMembership
    have vertexInBounds := linkWellFormed.vertex_in_bounds vertexMembership
    have vertexNotConclusion : vertex ≠ conclusion := by
      intro same
      subst vertex
      exact avoids vertexMembership
    have pivotReachable :=
      (TerminalTensor.mem_tensorLeftVertices_iff certificate
        left conclusion pivot).mp pivotLeft |>.2.2
    have vertexReachable :=
      (TerminalTensor.link_reachable_iff structural terminal linkMembership
        different pivotMembership vertexMembership).mp pivotReachable
    exact (TerminalTensor.mem_tensorLeftVertices_iff certificate
      left conclusion vertex).mpr
      ⟨vertexInBounds, vertexNotConclusion, vertexReachable⟩
  · right
    intro vertex vertexMembership
    have vertexInBounds := linkWellFormed.vertex_in_bounds vertexMembership
    have vertexNotConclusion : vertex ≠ conclusion := by
      intro same
      subst vertex
      exact avoids vertexMembership
    have pivotUnreachable :=
      (TerminalTensor.mem_tensorRightVertices_iff certificate
        left conclusion pivot).mp pivotRight |>.2.2
    have reachability := TerminalTensor.link_reachable_iff structural terminal
      linkMembership different pivotMembership vertexMembership
    have vertexUnreachable :
        vertex ∉ certificate.tensorLeftReachable left conclusion := by
      intro vertexReachable
      exact pivotUnreachable (reachability.mpr vertexReachable)
    exact (TerminalTensor.mem_tensorRightVertices_iff certificate
      left conclusion vertex).mpr
      ⟨vertexInBounds, vertexNotConclusion, vertexUnreachable⟩

theorem remaining_link_partition
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalTensor left right conclusion)
    {link : Link} (linkMembership : link ∈ certificate.links)
    (different : link ≠ .tensor left right conclusion) :
    (∀ vertex ∈ link.vertices,
        vertex ∈ certificate.tensorLeftVertices left conclusion) ∨
      (∀ vertex ∈ link.vertices,
        vertex ∈ certificate.tensorRightVertices left conclusion) := by
  cases link with
  | «axiom» first second =>
      exact TerminalTensor.link_partition_from_vertex (pivot := first)
        structural terminal
        linkMembership different (by simp [Link.vertices])
  | tensor first second result =>
      exact TerminalTensor.link_partition_from_vertex (pivot := first)
        structural terminal
        linkMembership different (by simp [Link.vertices])
  | par first second result =>
      exact TerminalTensor.link_partition_from_vertex (pivot := first)
        structural terminal
        linkMembership different (by simp [Link.vertices])

theorem terminal_not_mem_remaining
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalTensor left right conclusion) :
    Link.tensor left right conclusion ∉
      certificate.links.erase (.tensor left right conclusion) := by
  have countOriginal : certificate.links.count
      (.tensor left right conclusion) = 1 := by
    rw [← List.count_filter (p := (·.produces conclusion)) (by
      simp [Link.produces])]
    rw [TerminalTensor.producer_filter_eq structural terminal]
    simp
  apply List.count_eq_zero.mp
  simp [countOriginal]

theorem remainingLinks_partitioned
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (splitting : certificate.SplittingTensor left right conclusion) :
    (certificate.links.erase (.tensor left right conclusion)).all fun link =>
      link.vertices.all
          (certificate.tensorLeftVertices left conclusion).contains ||
        link.vertices.all
          (certificate.tensorRightVertices left conclusion).contains := by
  rw [List.all_eq_true]
  intro link remainingMembership
  have linkMembership : link ∈ certificate.links :=
    List.mem_of_mem_erase remainingMembership
  have different : link ≠ .tensor left right conclusion := by
    intro same
    subst link
    exact TerminalTensor.terminal_not_mem_remaining structural splitting.1
      remainingMembership
  rcases TerminalTensor.remaining_link_partition structural splitting.1
      linkMembership different with allLeft | allRight
  · rw [Bool.or_eq_true]
    left
    rw [List.all_eq_true]
    intro vertex vertexMembership
    simpa using allLeft vertex vertexMembership
  · rw [Bool.or_eq_true]
    right
    rw [List.all_eq_true]
    intro vertex vertexMembership
    simpa using allRight vertex vertexMembership

theorem link_terminal_or_left_or_avoids_left
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (splitting : certificate.SplittingTensor left right conclusion)
    {link : Link} (membership : link ∈ certificate.links) :
    link = .tensor left right conclusion ∨
      (∀ vertex ∈ link.vertices,
        vertex ∈ certificate.tensorLeftVertices left conclusion) ∨
      (∀ vertex ∈ link.vertices,
        vertex ∉ certificate.tensorLeftVertices left conclusion) := by
  by_cases terminal : link = .tensor left right conclusion
  · exact Or.inl terminal
  · have remainingMembership : link ∈
        certificate.links.erase (.tensor left right conclusion) :=
      (List.mem_erase_of_ne terminal).mpr membership
    rcases TerminalTensor.remaining_link_partition structural splitting.1
        membership terminal with allLeft | allRight
    · exact Or.inr (Or.inl allLeft)
    · exact Or.inr (Or.inr (by
        intro vertex vertexMembership leftMembership
        exact TerminalTensor.vertex_partition_disjoint certificate left conclusion
          vertex leftMembership (allRight vertex vertexMembership)))

theorem link_terminal_or_right_or_avoids_right
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (splitting : certificate.SplittingTensor left right conclusion)
    {link : Link} (membership : link ∈ certificate.links) :
    link = .tensor left right conclusion ∨
      (∀ vertex ∈ link.vertices,
        vertex ∈ certificate.tensorRightVertices left conclusion) ∨
      (∀ vertex ∈ link.vertices,
        vertex ∉ certificate.tensorRightVertices left conclusion) := by
  by_cases terminal : link = .tensor left right conclusion
  · exact Or.inl terminal
  · have remainingMembership : link ∈
        certificate.links.erase (.tensor left right conclusion) :=
      (List.mem_erase_of_ne terminal).mpr membership
    rcases TerminalTensor.remaining_link_partition structural splitting.1
        membership terminal with allLeft | allRight
    · exact Or.inr (Or.inr (by
        intro vertex vertexMembership rightMembership
        exact TerminalTensor.vertex_partition_disjoint certificate left conclusion
          vertex (allLeft vertex vertexMembership) rightMembership))
    · exact Or.inr (Or.inl allRight)

private theorem restrictTo?_axiomCount_of_tensor_partition
    {certificate restricted : Certificate}
    {vertices boundary : List Vertex}
    {left right conclusion vertex : Vertex}
    (certificateEquation :
      certificate.restrictTo? vertices boundary = some restricted)
    (partition : ∀ link ∈ certificate.links,
      link = .tensor left right conclusion ∨
        (∀ candidate ∈ link.vertices, candidate ∈ vertices) ∨
        (∀ candidate ∈ link.vertices, candidate ∉ vertices))
    (vertexContained : vertex ∈ vertices) :
    restricted.axiomCount (vertices.idxOf vertex) =
      certificate.axiomCount vertex := by
  unfold Certificate.axiomCount
  apply restrictTo?_filter_count_eq_of_partition certificateEquation
    (fun link => link.containsAxiomEndpoint (vertices.idxOf vertex))
    (fun link => link.containsAxiomEndpoint vertex) partition
  · rfl
  · intro link avoids
    apply Link.containsAxiomEndpoint_eq_false_of_not_mem_vertices
    intro incident
    exact (avoids vertex incident) vertexContained
  · intro link transformed linkEquation
    exact Link.restrictTo?_containsAxiomEndpoint linkEquation vertexContained

private theorem restrictTo?_producerCount_of_tensor_partition
    {certificate restricted : Certificate}
    {vertices boundary : List Vertex}
    {left right conclusion vertex : Vertex}
    (certificateEquation :
      certificate.restrictTo? vertices boundary = some restricted)
    (partition : ∀ link ∈ certificate.links,
      link = .tensor left right conclusion ∨
        (∀ candidate ∈ link.vertices, candidate ∈ vertices) ∨
        (∀ candidate ∈ link.vertices, candidate ∉ vertices))
    (vertexContained : vertex ∈ vertices)
    (vertexNotConclusion : vertex ≠ conclusion) :
    restricted.producerCount (vertices.idxOf vertex) =
      certificate.producerCount vertex := by
  unfold Certificate.producerCount
  apply restrictTo?_filter_count_eq_of_partition certificateEquation
    (fun link => link.produces (vertices.idxOf vertex))
    (fun link => link.produces vertex) partition
  · simp [Link.produces, Ne.symm vertexNotConclusion]
  · intro link avoids
    apply Link.produces_eq_false_of_not_mem_vertices
    intro incident
    exact (avoids vertex incident) vertexContained
  · intro link transformed linkEquation
    exact Link.restrictTo?_produces linkEquation vertexContained

private theorem restrictTo?_parentUseCount_of_tensor_partition
    {certificate restricted : Certificate}
    {vertices boundary : List Vertex}
    {left right conclusion vertex : Vertex}
    (certificateEquation :
      certificate.restrictTo? vertices boundary = some restricted)
    (partition : ∀ link ∈ certificate.links,
      link = .tensor left right conclusion ∨
        (∀ candidate ∈ link.vertices, candidate ∈ vertices) ∨
        (∀ candidate ∈ link.vertices, candidate ∉ vertices))
    (vertexContained : vertex ∈ vertices)
    (terminalRejected :
      (Link.tensor left right conclusion).usesAsPremise vertex = false) :
    restricted.parentUseCount (vertices.idxOf vertex) =
      certificate.parentUseCount vertex := by
  unfold Certificate.parentUseCount
  apply restrictTo?_filter_count_eq_of_partition certificateEquation
    (fun link => link.usesAsPremise (vertices.idxOf vertex))
    (fun link => link.usesAsPremise vertex) partition terminalRejected
  · intro link avoids
    apply Link.usesAsPremise_eq_false_of_not_mem_vertices
    intro incident
    exact (avoids vertex incident) vertexContained
  · intro link transformed linkEquation
    exact Link.restrictTo?_usesAsPremise linkEquation vertexContained

theorem restrictTo?_leftRoot_parentUseCount
    {certificate restricted : Certificate}
    {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (splitting : certificate.SplittingTensor left right conclusion)
    (certificateEquation : certificate.restrictTo?
      (certificate.tensorLeftVertices left conclusion)
      (certificate.tensorLeftBoundary left conclusion) = some restricted) :
    restricted.parentUseCount
      ((certificate.tensorLeftVertices left conclusion).idxOf left) = 0 := by
  have leftContained :=
    TerminalTensor.left_mem_tensorLeftVertices structural splitting.1
  unfold Certificate.parentUseCount
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro transformed transformedMembership transformedUses
  rw [certificate.restrictTo?_links certificateEquation] at transformedMembership
  rcases List.mem_filterMap.mp transformedMembership with
    ⟨original, originalMembership, linkEquation⟩
  have originalUses : original.usesAsPremise left = true := by
    rw [← Link.restrictTo?_usesAsPremise linkEquation leftContained]
    exact transformedUses
  have terminal := TerminalTensor.left_parent_unique structural splitting.1
    originalMembership originalUses
  subst original
  have contained := Link.vertices_mem_of_restrictTo?_eq_some linkEquation
  have rightInLeft := contained right (by simp [Link.vertices])
  exact TerminalTensor.vertex_partition_disjoint certificate left conclusion
    right rightInLeft
    (TerminalTensor.right_mem_tensorRightVertices structural splitting)

theorem restrictTo?_rightRoot_parentUseCount
    {certificate restricted : Certificate}
    {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (splitting : certificate.SplittingTensor left right conclusion)
    (certificateEquation : certificate.restrictTo?
      (certificate.tensorRightVertices left conclusion)
      (certificate.tensorRightBoundary left right conclusion) = some restricted) :
    restricted.parentUseCount
      ((certificate.tensorRightVertices left conclusion).idxOf right) = 0 := by
  have rightContained :=
    TerminalTensor.right_mem_tensorRightVertices structural splitting
  unfold Certificate.parentUseCount
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro transformed transformedMembership transformedUses
  rw [certificate.restrictTo?_links certificateEquation] at transformedMembership
  rcases List.mem_filterMap.mp transformedMembership with
    ⟨original, originalMembership, linkEquation⟩
  have originalUses : original.usesAsPremise right = true := by
    rw [← Link.restrictTo?_usesAsPremise linkEquation rightContained]
    exact transformedUses
  have terminal := TerminalTensor.right_parent_unique structural splitting.1
    originalMembership originalUses
  subst original
  have contained := Link.vertices_mem_of_restrictTo?_eq_some linkEquation
  have leftInRight := contained left (by simp [Link.vertices])
  exact TerminalTensor.vertex_partition_disjoint certificate left conclusion
    left (TerminalTensor.left_mem_tensorLeftVertices structural splitting.1)
    leftInRight

theorem restrictTo?_leftNodeWellFormed_idxOf
    {certificate restricted : Certificate}
    {left right conclusion vertex : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (splitting : certificate.SplittingTensor left right conclusion)
    (certificateEquation : certificate.restrictTo?
      (certificate.tensorLeftVertices left conclusion)
      (certificate.tensorLeftBoundary left conclusion) = some restricted)
    (vertexContained :
      vertex ∈ certificate.tensorLeftVertices left conclusion) :
    restricted.NodeWellFormed
      ((certificate.tensorLeftVertices left conclusion).idxOf vertex) := by
  let vertices := certificate.tensorLeftVertices left conclusion
  let boundary := certificate.tensorLeftBoundary left conclusion
  have verticesInBounds :=
    TerminalTensor.tensorLeftVertices_in_bounds certificate left conclusion
  have boundaryContained :=
    TerminalTensor.tensorLeftBoundary_contained structural splitting.1
  have vertexInBounds := verticesInBounds vertex vertexContained
  have vertexNotConclusion :=
    (TerminalTensor.mem_tensorLeftVertices_iff certificate
      left conclusion vertex).mp vertexContained |>.2.1
  have originalNode := structural.2.2.2.2.2 vertex vertexInBounds
  have formulaEquation := certificate.restrictTo?_formula?_idxOf
    verticesInBounds boundaryContained certificateEquation vertexContained
  have partition : ∀ link ∈ certificate.links,
      link = .tensor left right conclusion ∨
        (∀ candidate ∈ link.vertices,
          candidate ∈ certificate.tensorLeftVertices left conclusion) ∨
        (∀ candidate ∈ link.vertices,
          candidate ∉ certificate.tensorLeftVertices left conclusion) := by
    intro link membership
    exact TerminalTensor.link_terminal_or_left_or_avoids_left
      structural splitting membership
  have axiomCountEquation :=
    TerminalTensor.restrictTo?_axiomCount_of_tensor_partition
      certificateEquation partition vertexContained
  have producerCountEquation :=
    TerminalTensor.restrictTo?_producerCount_of_tensor_partition
      certificateEquation partition vertexContained vertexNotConclusion
  unfold Certificate.NodeWellFormed
  constructor
  · rw [formulaEquation]
    cases formula : certificate.formula? vertex with
    | none => simpa [formula] using originalNode.1
    | some value =>
        cases value with
        | atom name positive =>
            simpa [formula, axiomCountEquation] using originalNode.1
        | tensor first second =>
            simpa [formula, producerCountEquation] using originalNode.1
        | par first second =>
            simpa [formula, producerCountEquation] using originalNode.1
  · have localBoundaryIff :
        (certificate.tensorLeftVertices left conclusion).idxOf vertex ∈
            restricted.conclusions ↔
          vertex ∈ certificate.tensorLeftBoundary left conclusion :=
      certificate.restrictTo?_idxOf_mem_conclusions_iff verticesInBounds
        boundaryContained certificateEquation vertexContained
    by_cases isRoot : vertex = left
    · subst vertex
      have rootBoundary : left ∈
          certificate.tensorLeftBoundary left conclusion := by
        simp [tensorLeftBoundary]
      have localBoundary := localBoundaryIff.mpr rootBoundary
      simp [localBoundary,
        TerminalTensor.restrictTo?_leftRoot_parentUseCount
          structural splitting certificateEquation]
    · have notRight : vertex ≠ right := by
        intro same
        subst vertex
        exact TerminalTensor.vertex_partition_disjoint certificate left conclusion
          right vertexContained
          (TerminalTensor.right_mem_tensorRightVertices structural splitting)
      have terminalRejected :
          (Link.tensor left right conclusion).usesAsPremise vertex = false := by
        simp [Link.usesAsPremise, Link.premises, isRoot, notRight]
      have parentCountEquation :=
        TerminalTensor.restrictTo?_parentUseCount_of_tensor_partition
          certificateEquation partition vertexContained terminalRejected
      have boundaryIffOriginal :
          (certificate.tensorLeftVertices left conclusion).idxOf vertex ∈
              restricted.conclusions ↔
            vertex ∈ certificate.conclusions := by
        rw [localBoundaryIff,
          TerminalTensor.mem_tensorLeftBoundary_iff vertexContained]
        simp [isRoot]
      by_cases originalBoundary : vertex ∈ certificate.conclusions
      · have localBoundary := boundaryIffOriginal.mpr originalBoundary
        simp [localBoundary]
        rw [parentCountEquation]
        simpa [originalBoundary] using originalNode.2
      · have localNotBoundary :
            (certificate.tensorLeftVertices left conclusion).idxOf vertex ∉
              restricted.conclusions := by
          intro localBoundary
          exact originalBoundary (boundaryIffOriginal.mp localBoundary)
        simp [localNotBoundary]
        rw [parentCountEquation]
        simpa [originalBoundary] using originalNode.2

theorem restrictTo?_leftNodesWellFormed
    {certificate restricted : Certificate}
    {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (splitting : certificate.SplittingTensor left right conclusion)
    (certificateEquation : certificate.restrictTo?
      (certificate.tensorLeftVertices left conclusion)
      (certificate.tensorLeftBoundary left conclusion) = some restricted) :
    ∀ localVertex, localVertex < restricted.formulas.size →
      restricted.NodeWellFormed localVertex := by
  intro localVertex localInBounds
  have formulasSize := certificate.restrictTo?_formulas_size certificateEquation
  have localInVertices : localVertex <
      (certificate.tensorLeftVertices left conclusion).length := by
    rw [← formulasSize]
    exact localInBounds
  let originalVertex :=
    (certificate.tensorLeftVertices left conclusion)[localVertex]
  have originalMembership : originalVertex ∈
      certificate.tensorLeftVertices left conclusion :=
    List.getElem_mem localInVertices
  have indexEquation :
      (certificate.tensorLeftVertices left conclusion).idxOf originalVertex =
        localVertex :=
    idxOf_getElem_eq_index
      (TerminalTensor.tensorLeftVertices_nodup certificate left conclusion)
      localVertex localInVertices
  rw [← indexEquation]
  exact TerminalTensor.restrictTo?_leftNodeWellFormed_idxOf
    structural splitting certificateEquation originalMembership

theorem restrictTo?_leftStructurallyWellFormed
    {certificate restricted : Certificate}
    {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (splitting : certificate.SplittingTensor left right conclusion)
    (certificateEquation : certificate.restrictTo?
      (certificate.tensorLeftVertices left conclusion)
      (certificate.tensorLeftBoundary left conclusion) = some restricted) :
    restricted.StructurallyWellFormed := by
  have structuralPrefix := certificate.restrictTo?_structuralPrefix
    (TerminalTensor.tensorLeftVertices_in_bounds certificate left conclusion)
    (TerminalTensor.tensorLeftBoundary_contained structural splitting.1)
    (TerminalTensor.tensorLeftVertices_length_pos structural splitting.1)
    (TerminalTensor.tensorLeftBoundary_length_pos certificate left conclusion)
    (TerminalTensor.tensorLeftBoundary_nodup structural splitting.1)
    structural.2.2.2.2.1 certificateEquation
  exact ⟨structuralPrefix.1, structuralPrefix.2.1,
    structuralPrefix.2.2.1, structuralPrefix.2.2.2.1,
    structuralPrefix.2.2.2.2,
    TerminalTensor.restrictTo?_leftNodesWellFormed
      structural splitting certificateEquation⟩

theorem restrictTo?_rightNodeWellFormed_idxOf
    {certificate restricted : Certificate}
    {left right conclusion vertex : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (splitting : certificate.SplittingTensor left right conclusion)
    (certificateEquation : certificate.restrictTo?
      (certificate.tensorRightVertices left conclusion)
      (certificate.tensorRightBoundary left right conclusion) = some restricted)
    (vertexContained :
      vertex ∈ certificate.tensorRightVertices left conclusion) :
    restricted.NodeWellFormed
      ((certificate.tensorRightVertices left conclusion).idxOf vertex) := by
  have verticesInBounds :=
    TerminalTensor.tensorRightVertices_in_bounds certificate left conclusion
  have boundaryContained :=
    TerminalTensor.tensorRightBoundary_contained structural splitting
  have vertexInBounds := verticesInBounds vertex vertexContained
  have vertexNotConclusion :=
    (TerminalTensor.mem_tensorRightVertices_iff certificate
      left conclusion vertex).mp vertexContained |>.2.1
  have originalNode := structural.2.2.2.2.2 vertex vertexInBounds
  have formulaEquation := certificate.restrictTo?_formula?_idxOf
    verticesInBounds boundaryContained certificateEquation vertexContained
  have partition : ∀ link ∈ certificate.links,
      link = .tensor left right conclusion ∨
        (∀ candidate ∈ link.vertices,
          candidate ∈ certificate.tensorRightVertices left conclusion) ∨
        (∀ candidate ∈ link.vertices,
          candidate ∉ certificate.tensorRightVertices left conclusion) := by
    intro link membership
    exact TerminalTensor.link_terminal_or_right_or_avoids_right
      structural splitting membership
  have axiomCountEquation :=
    TerminalTensor.restrictTo?_axiomCount_of_tensor_partition
      certificateEquation partition vertexContained
  have producerCountEquation :=
    TerminalTensor.restrictTo?_producerCount_of_tensor_partition
      certificateEquation partition vertexContained vertexNotConclusion
  unfold Certificate.NodeWellFormed
  constructor
  · rw [formulaEquation]
    cases formula : certificate.formula? vertex with
    | none => simpa [formula] using originalNode.1
    | some value =>
        cases value with
        | atom name positive =>
            simpa [formula, axiomCountEquation] using originalNode.1
        | tensor first second =>
            simpa [formula, producerCountEquation] using originalNode.1
        | par first second =>
            simpa [formula, producerCountEquation] using originalNode.1
  · have localBoundaryIff :
        (certificate.tensorRightVertices left conclusion).idxOf vertex ∈
            restricted.conclusions ↔
          vertex ∈ certificate.tensorRightBoundary left right conclusion :=
      certificate.restrictTo?_idxOf_mem_conclusions_iff verticesInBounds
        boundaryContained certificateEquation vertexContained
    by_cases isRoot : vertex = right
    · subst vertex
      have rootBoundary : right ∈
          certificate.tensorRightBoundary left right conclusion := by
        simp [tensorRightBoundary]
      have localBoundary := localBoundaryIff.mpr rootBoundary
      simp [localBoundary,
        TerminalTensor.restrictTo?_rightRoot_parentUseCount
          structural splitting certificateEquation]
    · have notLeft : vertex ≠ left := by
        intro same
        subst vertex
        exact TerminalTensor.vertex_partition_disjoint certificate left conclusion
          left (TerminalTensor.left_mem_tensorLeftVertices structural splitting.1)
          vertexContained
      have terminalRejected :
          (Link.tensor left right conclusion).usesAsPremise vertex = false := by
        simp [Link.usesAsPremise, Link.premises, notLeft, isRoot]
      have parentCountEquation :=
        TerminalTensor.restrictTo?_parentUseCount_of_tensor_partition
          certificateEquation partition vertexContained terminalRejected
      have boundaryIffOriginal :
          (certificate.tensorRightVertices left conclusion).idxOf vertex ∈
              restricted.conclusions ↔
            vertex ∈ certificate.conclusions := by
        rw [localBoundaryIff,
          TerminalTensor.mem_tensorRightBoundary_iff vertexContained]
        simp [isRoot]
      by_cases originalBoundary : vertex ∈ certificate.conclusions
      · have localBoundary := boundaryIffOriginal.mpr originalBoundary
        simp [localBoundary]
        rw [parentCountEquation]
        simpa [originalBoundary] using originalNode.2
      · have localNotBoundary :
            (certificate.tensorRightVertices left conclusion).idxOf vertex ∉
              restricted.conclusions := by
          intro localBoundary
          exact originalBoundary (boundaryIffOriginal.mp localBoundary)
        simp [localNotBoundary]
        rw [parentCountEquation]
        simpa [originalBoundary] using originalNode.2

theorem restrictTo?_rightNodesWellFormed
    {certificate restricted : Certificate}
    {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (splitting : certificate.SplittingTensor left right conclusion)
    (certificateEquation : certificate.restrictTo?
      (certificate.tensorRightVertices left conclusion)
      (certificate.tensorRightBoundary left right conclusion) = some restricted) :
    ∀ localVertex, localVertex < restricted.formulas.size →
      restricted.NodeWellFormed localVertex := by
  intro localVertex localInBounds
  have formulasSize := certificate.restrictTo?_formulas_size certificateEquation
  have localInVertices : localVertex <
      (certificate.tensorRightVertices left conclusion).length := by
    rw [← formulasSize]
    exact localInBounds
  let originalVertex :=
    (certificate.tensorRightVertices left conclusion)[localVertex]
  have originalMembership : originalVertex ∈
      certificate.tensorRightVertices left conclusion :=
    List.getElem_mem localInVertices
  have indexEquation :
      (certificate.tensorRightVertices left conclusion).idxOf originalVertex =
        localVertex :=
    idxOf_getElem_eq_index
      (TerminalTensor.tensorRightVertices_nodup certificate left conclusion)
      localVertex localInVertices
  rw [← indexEquation]
  exact TerminalTensor.restrictTo?_rightNodeWellFormed_idxOf
    structural splitting certificateEquation originalMembership

theorem restrictTo?_rightStructurallyWellFormed
    {certificate restricted : Certificate}
    {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (splitting : certificate.SplittingTensor left right conclusion)
    (certificateEquation : certificate.restrictTo?
      (certificate.tensorRightVertices left conclusion)
      (certificate.tensorRightBoundary left right conclusion) = some restricted) :
    restricted.StructurallyWellFormed := by
  have structuralPrefix := certificate.restrictTo?_structuralPrefix
    (TerminalTensor.tensorRightVertices_in_bounds certificate left conclusion)
    (TerminalTensor.tensorRightBoundary_contained structural splitting)
    (TerminalTensor.tensorRightVertices_length_pos structural splitting)
    (TerminalTensor.tensorRightBoundary_length_pos certificate left right conclusion)
    (TerminalTensor.tensorRightBoundary_nodup structural splitting.1)
    structural.2.2.2.2.1 certificateEquation
  exact ⟨structuralPrefix.1, structuralPrefix.2.1,
    structuralPrefix.2.2.1, structuralPrefix.2.2.2.1,
    structuralPrefix.2.2.2.2,
    TerminalTensor.restrictTo?_rightNodesWellFormed
      structural splitting certificateEquation⟩

end TerminalTensor

theorem ChoiceSelection.filter_length_eq_of_pair_agreement
    {choices : List (Edge × Edge)} {selected : List Edge}
    (selection : ChoiceSelection choices selected)
    (predicate : Edge → Bool)
    (pairAgreement : ∀ choice ∈ choices,
      predicate choice.1 = predicate choice.2) :
    (selected.filter predicate).length =
      (choices.filter fun choice => predicate choice.1).length := by
  induction selection with
  | nil => rfl
  | @left left right rest selected prior ih =>
      have restAgreement : ∀ choice ∈ rest,
          predicate choice.1 = predicate choice.2 := by
        intro choice membership
        exact pairAgreement choice (by simp [membership])
      by_cases accepted : predicate left = true <;>
        simp [accepted, ih restAgreement]
  | @right left right rest selected prior ih =>
      have headAgreement : predicate left = predicate right :=
        pairAgreement (left, right) (by simp)
      have restAgreement : ∀ choice ∈ rest,
          predicate choice.1 = predicate choice.2 := by
        intro choice membership
        exact pairAgreement choice (by simp [membership])
      by_cases accepted : predicate left = true <;>
        simp [accepted, ← headAgreement, ih restAgreement]

theorem ChoiceSelection.liftDelete
    {removed : Vertex} {choices : List (Edge × Edge)} {selected : List Edge}
    (selection : ChoiceSelection
      (choices.filterMap (ParChoice.deleteVertex? removed)) selected)
    (agreement : ∀ choice ∈ choices,
      (choice.1.deleteVertex? removed).isSome =
        (choice.2.deleteVertex? removed).isSome) :
    ∃ lifted,
      ChoiceSelection choices lifted ∧
      selected = lifted.filterMap (Edge.deleteVertex? removed) := by
  induction choices generalizing selected with
  | nil =>
      cases selection
      exact ⟨[], .nil, rfl⟩
  | cons choice rest ih =>
      have headAgreement := agreement choice (by simp)
      have restAgreement : ∀ candidate ∈ rest,
          (candidate.1.deleteVertex? removed).isSome =
            (candidate.2.deleteVertex? removed).isSome := by
        intro candidate membership
        exact agreement candidate (by simp [membership])
      cases firstEquation : choice.1.deleteVertex? removed with
      | none =>
          have secondNone : choice.2.deleteVertex? removed = none := by
            cases secondEquation : choice.2.deleteVertex? removed with
            | none => rfl
            | some second =>
                simp [firstEquation, secondEquation] at headAgreement
          have restSelection : ChoiceSelection
              (rest.filterMap (ParChoice.deleteVertex? removed)) selected := by
            simpa [ParChoice.deleteVertex?, firstEquation, secondNone]
              using selection
          rcases ih restSelection restAgreement with
            ⟨lifted, liftedSelection, selectedEquation⟩
          exact ⟨choice.1 :: lifted, .left liftedSelection, by
            simp [firstEquation, selectedEquation]⟩
      | some first =>
          have secondSome : ∃ second,
              choice.2.deleteVertex? removed = some second := by
            cases secondEquation : choice.2.deleteVertex? removed with
            | none => simp [firstEquation, secondEquation] at headAgreement
            | some second => exact ⟨second, rfl⟩
          rcases secondSome with ⟨second, secondEquation⟩
          have expandedSelection : ChoiceSelection
              ((first, second) ::
                rest.filterMap (ParChoice.deleteVertex? removed)) selected := by
            simpa [ParChoice.deleteVertex?, firstEquation, secondEquation]
              using selection
          cases expandedSelection with
          | left prior =>
              rcases ih prior restAgreement with
                ⟨lifted, liftedSelection, selectedEquation⟩
              exact ⟨choice.1 :: lifted, .left liftedSelection, by
                simp [firstEquation, selectedEquation]⟩
          | right prior =>
              rcases ih prior restAgreement with
                ⟨lifted, liftedSelection, selectedEquation⟩
              exact ⟨choice.2 :: lifted, .right liftedSelection, by
                simp [secondEquation, selectedEquation]⟩

theorem ChoiceSelection.liftRestrict
    {vertices : List Vertex} {choices : List (Edge × Edge)}
    {selected : List Edge}
    (selection : ChoiceSelection
      (choices.filterMap (ParChoice.restrictTo? vertices)) selected) :
    ∃ lifted,
      ChoiceSelection choices lifted ∧
      selected = lifted.filterMap (Edge.restrictTo? vertices) := by
  induction choices generalizing selected with
  | nil =>
      cases selection
      exact ⟨[], .nil, rfl⟩
  | cons choice rest ih =>
      cases firstEquation : choice.1.restrictTo? vertices with
      | none =>
          have restSelection : ChoiceSelection
              (rest.filterMap (ParChoice.restrictTo? vertices)) selected := by
            simpa [ParChoice.restrictTo?, firstEquation] using selection
          rcases ih restSelection with
            ⟨lifted, liftedSelection, selectedEquation⟩
          exact ⟨choice.1 :: lifted, .left liftedSelection, by
            simp [firstEquation, selectedEquation]⟩
      | some first =>
          cases secondEquation : choice.2.restrictTo? vertices with
          | none =>
              have restSelection : ChoiceSelection
                  (rest.filterMap (ParChoice.restrictTo? vertices)) selected := by
                simpa [ParChoice.restrictTo?, firstEquation, secondEquation]
                  using selection
              rcases ih restSelection with
                ⟨lifted, liftedSelection, selectedEquation⟩
              exact ⟨choice.2 :: lifted, .right liftedSelection, by
                simp [secondEquation, selectedEquation]⟩
          | some second =>
              have expandedSelection : ChoiceSelection
                  ((first, second) ::
                    rest.filterMap (ParChoice.restrictTo? vertices)) selected := by
                simpa [ParChoice.restrictTo?, firstEquation, secondEquation]
                  using selection
              cases expandedSelection with
              | left prior =>
                  rcases ih prior with
                    ⟨lifted, liftedSelection, selectedEquation⟩
                  exact ⟨choice.1 :: lifted, .left liftedSelection, by
                    simp [firstEquation, selectedEquation]⟩
              | right prior =>
                  rcases ih prior with
                    ⟨lifted, liftedSelection, selectedEquation⟩
                  exact ⟨choice.2 :: lifted, .right liftedSelection, by
                    simp [secondEquation, selectedEquation]⟩

/-- Every switching of a closed restricted component is the edge restriction
of a switching of the input certificate. -/
theorem restrictTo?_switchingLift_of_tensor_partition
    {certificate restricted : Certificate} {vertices boundary : List Vertex}
    {left right conclusion : Vertex}
    (certificateEquation :
      certificate.restrictTo? vertices boundary = some restricted)
    (conclusionOutside : conclusion ∉ vertices)
    (partition : ∀ link ∈ certificate.links,
      link = .tensor left right conclusion ∨
        (∀ vertex ∈ link.vertices, vertex ∈ vertices) ∨
        (∀ vertex ∈ link.vertices, vertex ∉ vertices))
    {restrictedGraph : Graph}
    (restrictedSwitching : restricted.SwitchingGraph restrictedGraph) :
    ∃ inputGraph,
      certificate.SwitchingGraph inputGraph ∧
      restrictedGraph = inputGraph.restrictTo vertices := by
  rcases restrictedSwitching with ⟨selected, selection, rfl⟩
  have transformedSelection : ChoiceSelection
      (certificate.parChoices.filterMap (ParChoice.restrictTo? vertices))
      selected := by
    rw [← certificate.restrictTo?_parChoices certificateEquation]
    exact selection
  rcases transformedSelection.liftRestrict with
    ⟨lifted, liftedSelection, selectedEquation⟩
  let inputGraph := certificate.graphForSelection lifted
  refine ⟨inputGraph, ⟨lifted, liftedSelection, rfl⟩, ?_⟩
  have formulasSize :=
    certificate.restrictTo?_formulas_size certificateEquation
  have edgesEquation : restricted.fixedEdges ++ selected =
      (certificate.fixedEdges ++ lifted).filterMap
        (Edge.restrictTo? vertices) := by
    rw [certificate.restrictTo?_fixedEdges_of_tensor_partition
      certificateEquation conclusionOutside partition,
      selectedEquation, List.filterMap_append]
  simp [inputGraph, Certificate.graphForSelection, Graph.restrictTo,
    formulasSize, edgesEquation]

namespace TerminalTensor

theorem restrictTo?_leftSwitchingLift
    {certificate restricted : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (splitting : certificate.SplittingTensor left right conclusion)
    (certificateEquation : certificate.restrictTo?
      (certificate.tensorLeftVertices left conclusion)
      (certificate.tensorLeftBoundary left conclusion) = some restricted)
    {restrictedGraph : Graph}
    (restrictedSwitching : restricted.SwitchingGraph restrictedGraph) :
    ∃ inputGraph,
      certificate.SwitchingGraph inputGraph ∧
      restrictedGraph = inputGraph.restrictTo
        (certificate.tensorLeftVertices left conclusion) := by
  apply certificate.restrictTo?_switchingLift_of_tensor_partition
    certificateEquation
    (TerminalTensor.conclusion_not_mem_tensorLeftVertices
      certificate left conclusion)
  · intro link membership
    exact TerminalTensor.link_terminal_or_left_or_avoids_left
      structural splitting membership
  · exact restrictedSwitching

theorem restrictTo?_rightSwitchingLift
    {certificate restricted : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (splitting : certificate.SplittingTensor left right conclusion)
    (certificateEquation : certificate.restrictTo?
      (certificate.tensorRightVertices left conclusion)
      (certificate.tensorRightBoundary left right conclusion) = some restricted)
    {restrictedGraph : Graph}
    (restrictedSwitching : restricted.SwitchingGraph restrictedGraph) :
    ∃ inputGraph,
      certificate.SwitchingGraph inputGraph ∧
      restrictedGraph = inputGraph.restrictTo
        (certificate.tensorRightVertices left conclusion) := by
  apply certificate.restrictTo?_switchingLift_of_tensor_partition
    certificateEquation
    (TerminalTensor.conclusion_not_mem_tensorRightVertices
      certificate left conclusion)
  · intro link membership
    exact TerminalTensor.link_terminal_or_right_or_avoids_right
      structural splitting membership
  · exact restrictedSwitching

end TerminalTensor

theorem TerminalPar.parChoice_incident_agreement
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalPar left right conclusion)
    {choice : Edge × Edge} (membership : choice ∈ certificate.parChoices) :
    choice.1.incident conclusion = choice.2.incident conclusion := by
  simp only [parChoices, List.mem_filterMap] at membership
  rcases membership with ⟨link, linkMembership, emitted⟩
  cases link with
  | «axiom» first second => simp at emitted
  | tensor first second result => simp at emitted
  | par first second result =>
      simp at emitted
      subst choice
      have firstNotConclusion : first ≠ conclusion := by
        intro same
        subst first
        exact TerminalPar.no_parentUse structural terminal linkMembership
          (by simp [Link.usesAsPremise, Link.premises])
      have secondNotConclusion : second ≠ conclusion := by
        intro same
        subst second
        exact TerminalPar.no_parentUse structural terminal linkMembership
          (by simp [Link.usesAsPremise, Link.premises])
      have firstBoolean : (first == conclusion) = false :=
        beq_eq_false_iff_ne.mpr firstNotConclusion
      have secondBoolean : (second == conclusion) = false :=
        beq_eq_false_iff_ne.mpr secondNotConclusion
      simp [Edge.incident, firstBoolean, secondBoolean]

theorem TerminalPar.parChoice_deletion_agreement
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalPar left right conclusion)
    {choice : Edge × Edge} (membership : choice ∈ certificate.parChoices) :
    (choice.1.deleteVertex? conclusion).isSome =
      (choice.2.deleteVertex? conclusion).isSome := by
  rw [Edge.deleteVertex?_isSome, Edge.deleteVertex?_isSome,
    TerminalPar.parChoice_incident_agreement structural terminal membership]

theorem TerminalTensor.parChoice_not_incident
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalTensor left right conclusion)
    {choice : Edge × Edge} (membership : choice ∈ certificate.parChoices) :
    choice.1.incident conclusion = false ∧
      choice.2.incident conclusion = false := by
  simp only [parChoices, List.mem_filterMap] at membership
  rcases membership with ⟨link, linkMembership, emitted⟩
  cases link with
  | «axiom» first second => simp at emitted
  | tensor first second result => simp at emitted
  | par first second result =>
      simp at emitted
      subst choice
      have avoids : conclusion ∉ (Link.par first second result).vertices := by
        intro incident
        have impossible := TerminalTensor.unique_incident structural terminal
          linkMembership incident
        cases impossible
      simp [Link.vertices] at avoids
      have firstNotConclusion : first ≠ conclusion := Ne.symm avoids.1
      have secondNotConclusion : second ≠ conclusion := Ne.symm avoids.2.1
      have resultNotConclusion : result ≠ conclusion := Ne.symm avoids.2.2
      simp [Edge.incident, firstNotConclusion, secondNotConclusion,
        resultNotConclusion]

theorem TerminalTensor.selected_incidentCount
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalTensor left right conclusion)
    {selected : List Edge}
    (selection : ChoiceSelection certificate.parChoices selected) :
    (selected.filter (·.incident conclusion)).length = 0 := by
  rw [selection.filter_length_eq_of_pair_agreement
    (·.incident conclusion) (by
      intro choice membership
      have avoids := TerminalTensor.parChoice_not_incident structural terminal
        membership
      rw [avoids.1, avoids.2])]
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro choice membership
  have avoids := TerminalTensor.parChoice_not_incident structural terminal
    membership
  simp [avoids.1]

theorem TerminalTensor.fixedEdges_incident
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalTensor left right conclusion) :
    certificate.fixedEdges.filter (·.incident conclusion) =
      [{ first := left, second := conclusion },
       { first := right, second := conclusion }] := by
  let emitFixed : Link → List Edge := fun
    | .axiom first second => [{ first, second }]
    | .tensor first second result =>
        [{ first := first, second := result },
         { first := second, second := result }]
    | .par _ _ _ => []
  change (certificate.links.flatMap emitFixed).filter
      (·.incident conclusion) = _
  have general : ∀ links : List Link,
      (∀ link ∈ links, link ∈ certificate.links) →
      (links.flatMap emitFixed).filter (·.incident conclusion) =
        (links.filter (·.produces conclusion)).flatMap emitFixed := by
    intro links subset
    induction links with
    | nil => rfl
    | cons head tail ih =>
        have headMembership : head ∈ certificate.links :=
          subset head (by simp)
        have tailSubset : ∀ link ∈ tail, link ∈ certificate.links := by
          intro link membership
          exact subset link (by simp [membership])
        have tailEquality := ih tailSubset
        by_cases produced : head.produces conclusion = true
        · have same := TerminalTensor.producer_unique structural terminal
            headMembership produced
          subst head
          simpa [emitFixed, Link.produces, Edge.incident]
            using tailEquality
        · have avoids : conclusion ∉ head.vertices := by
            intro incident
            have same := TerminalTensor.unique_incident structural terminal
              headMembership incident
            subst head
            simp [Link.produces] at produced
          cases head with
          | «axiom» first second =>
              simp [Link.vertices] at avoids
              have firstNotConclusion : first ≠ conclusion := Ne.symm avoids.1
              have secondNotConclusion : second ≠ conclusion :=
                Ne.symm avoids.2
              simpa [emitFixed, produced, Edge.incident,
                firstNotConclusion, secondNotConclusion] using tailEquality
          | tensor first second result =>
              simp [Link.vertices] at avoids
              have firstNotConclusion : first ≠ conclusion := Ne.symm avoids.1
              have secondNotConclusion : second ≠ conclusion :=
                Ne.symm avoids.2.1
              have resultNotConclusion : result ≠ conclusion :=
                Ne.symm avoids.2.2
              simpa [emitFixed, produced, Edge.incident,
                firstNotConclusion, secondNotConclusion,
                resultNotConclusion] using tailEquality
          | par first second result =>
              simpa [emitFixed, produced] using tailEquality
  rw [general certificate.links (by simp),
    TerminalTensor.producer_filter_eq structural terminal]
  rfl

theorem TerminalTensor.graphForSelection_incidentCount
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalTensor left right conclusion)
    {selected : List Edge}
    (selection : ChoiceSelection certificate.parChoices selected) :
    (certificate.graphForSelection selected).incidentCount conclusion = 2 := by
  unfold Graph.incidentCount
  change ((certificate.fixedEdges ++ selected).filter
    (·.incident conclusion)).length = 2
  rw [List.filter_append, List.length_append,
    TerminalTensor.fixedEdges_incident structural terminal,
    TerminalTensor.selected_incidentCount structural terminal selection]
  rfl

theorem TerminalTensor.graphForSelection_incidentEdges
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalTensor left right conclusion)
    {selected : List Edge}
    (selection : ChoiceSelection certificate.parChoices selected) :
    (certificate.graphForSelection selected).edges.filter
        (·.incident conclusion) =
      [{ first := left, second := conclusion },
       { first := right, second := conclusion }] := by
  have selectedLength :=
    TerminalTensor.selected_incidentCount structural terminal selection
  have selectedNone : selected.filter (·.incident conclusion) = [] :=
    List.eq_nil_of_length_eq_zero selectedLength
  change (certificate.fixedEdges ++ selected).filter
      (·.incident conclusion) = _
  rw [List.filter_append,
    TerminalTensor.fixedEdges_incident structural terminal, selectedNone]
  rfl

theorem TerminalTensor.graphForSelection_adjacent_conclusion_iff
    {certificate : Certificate} {left right conclusion vertex : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalTensor left right conclusion)
    {selected : List Edge}
    (selection : ChoiceSelection certificate.parChoices selected) :
    (certificate.graphForSelection selected).Adjacent vertex conclusion ↔
      vertex = left ∨ vertex = right := by
  have incidentEdges :=
    TerminalTensor.graphForSelection_incidentEdges structural terminal selection
  have terminalWellFormed := structural.2.2.2.2.1 _ terminal.1
  have leftNotConclusion := terminalWellFormed.2.1
  have rightNotConclusion := terminalWellFormed.2.2.1
  constructor
  · rintro ⟨edge, edgeMembership, direction⟩
    have incident : edge.incident conclusion = true := by
      rcases direction with forward | backward
      · simp [Edge.incident, forward]
      · simp [Edge.incident, backward]
    have filtered : edge ∈
        (certificate.graphForSelection selected).edges.filter
          (·.incident conclusion) := by
      simp [edgeMembership, incident]
    rw [incidentEdges] at filtered
    simp at filtered
    rcases filtered with same | same
    · rw [same] at direction
      rcases direction with forward | backward
      · exact Or.inl forward.1.symm
      · exact False.elim (leftNotConclusion backward.1)
    · rw [same] at direction
      rcases direction with forward | backward
      · exact Or.inr forward.1.symm
      · exact False.elim (rightNotConclusion backward.1)
  · intro endpoint
    rcases endpoint with endpoint | endpoint
    · have filtered : ({ first := left, second := conclusion } : Edge) ∈
          (certificate.graphForSelection selected).edges.filter
            (·.incident conclusion) := by
        rw [incidentEdges]
        simp
      have adjacency : (certificate.graphForSelection selected).Adjacent
          left conclusion :=
        ⟨_, (List.mem_filter.mp filtered).1, .inl ⟨rfl, rfl⟩⟩
      simpa [endpoint] using adjacency
    · have filtered : ({ first := right, second := conclusion } : Edge) ∈
          (certificate.graphForSelection selected).edges.filter
            (·.incident conclusion) := by
        rw [incidentEdges]
        simp
      have adjacency : (certificate.graphForSelection selected).Adjacent
          right conclusion :=
        ⟨_, (List.mem_filter.mp filtered).1, .inl ⟨rfl, rfl⟩⟩
      simpa [endpoint] using adjacency

namespace TerminalTensor

theorem graphForSelection_adjacent_preserves_left
    {certificate : Certificate} {left right conclusion first second : Vertex}
    {selected : List Edge}
    (structural : certificate.StructurallyWellFormed)
    (splitting : certificate.SplittingTensor left right conclusion)
    (selection : ChoiceSelection certificate.parChoices selected)
    (firstMembership :
      first ∈ certificate.tensorLeftVertices left conclusion)
    (secondNotConclusion : second ≠ conclusion)
    (adjacency : (certificate.graphForSelection selected).Adjacent
      first second) :
    second ∈ certificate.tensorLeftVertices left conclusion := by
  have firstData := (TerminalTensor.mem_tensorLeftVertices_iff certificate
    left conclusion first).mp firstMembership
  have fullAdjacency :=
    certificate.graphForSelection_adjacent_fullGraphWithout selection
      firstData.2.1 secondNotConclusion adjacency
  have fullBounded :=
    certificate.fullGraphWithoutVertex_bounded structural conclusion
  have secondInBounds :=
    (certificate.fullGraphWithoutVertex conclusion).adjacent_right_in_bounds
      fullBounded fullAdjacency
  have terminalWellFormed := structural.2.2.2.2.1 _ splitting.1.1
  have leftInBounds := terminalWellFormed.2.2.2.1
  have firstWalk :=
    (Graph.mem_closureN_vertexCount_iff_walk _ fullBounded
      leftInBounds firstData.1).mp firstData.2.2
  have secondReachable : second ∈
      certificate.tensorLeftReachable left conclusion := by
    unfold tensorLeftReachable
    exact (Graph.mem_closureN_vertexCount_iff_walk _ fullBounded
      leftInBounds secondInBounds).mpr (.step firstWalk fullAdjacency)
  exact (TerminalTensor.mem_tensorLeftVertices_iff certificate
    left conclusion second).mpr
    ⟨secondInBounds, secondNotConclusion, secondReachable⟩

theorem graphForSelection_adjacent_preserves_right
    {certificate : Certificate} {left right conclusion first second : Vertex}
    {selected : List Edge}
    (structural : certificate.StructurallyWellFormed)
    (splitting : certificate.SplittingTensor left right conclusion)
    (selection : ChoiceSelection certificate.parChoices selected)
    (firstMembership :
      first ∈ certificate.tensorRightVertices left conclusion)
    (secondNotConclusion : second ≠ conclusion)
    (adjacency : (certificate.graphForSelection selected).Adjacent
      first second) :
    second ∈ certificate.tensorRightVertices left conclusion := by
  have firstData := (TerminalTensor.mem_tensorRightVertices_iff certificate
    left conclusion first).mp firstMembership
  have fullAdjacency :=
    certificate.graphForSelection_adjacent_fullGraphWithout selection
      firstData.2.1 secondNotConclusion adjacency
  have fullBounded :=
    certificate.fullGraphWithoutVertex_bounded structural conclusion
  have secondInBounds :=
    (certificate.fullGraphWithoutVertex conclusion).adjacent_right_in_bounds
      fullBounded fullAdjacency
  have terminalWellFormed := structural.2.2.2.2.1 _ splitting.1.1
  have leftInBounds := terminalWellFormed.2.2.2.1
  have secondUnreachable : second ∉
      certificate.tensorLeftReachable left conclusion := by
    intro secondReachable
    have secondWalk :=
      (Graph.mem_closureN_vertexCount_iff_walk _ fullBounded
        leftInBounds secondInBounds).mp secondReachable
    have firstWalk := secondWalk.trans
      (.step (.refl second) fullAdjacency.symm)
    exact firstData.2.2
      ((Graph.mem_closureN_vertexCount_iff_walk _ fullBounded
        leftInBounds firstData.1).mpr firstWalk)
  exact (TerminalTensor.mem_tensorRightVertices_iff certificate
    left conclusion second).mpr
    ⟨secondInBounds, secondNotConclusion, secondUnreachable⟩

theorem simpleWalk_avoiding_conclusion_stays_left
    {certificate : Certificate} {left right conclusion start finish : Vertex}
    {selected : List Edge} {steps : Nat} {visited : List Vertex}
    (structural : certificate.StructurallyWellFormed)
    (splitting : certificate.SplittingTensor left right conclusion)
    (selection : ChoiceSelection certificate.parChoices selected)
    (tree : (certificate.graphForSelection selected).IsTree)
    (walk : (certificate.graphForSelection selected).SimpleWalk
      start steps visited finish)
    (startMembership :
      start ∈ certificate.tensorLeftVertices left conclusion)
    (avoidsConclusion : conclusion ∉ visited) :
    ∀ vertex ∈ visited,
      vertex ∈ certificate.tensorLeftVertices left conclusion := by
  induction walk with
  | refl =>
      intro vertex membership
      simp at membership
      subst vertex
      exact startMembership
  | @step priorSteps priorVisited middle current prior adjacency fresh ih =>
      have priorAvoids : conclusion ∉ priorVisited := by
        intro membership
        exact avoidsConclusion (by simp [membership])
      have priorContained := ih priorAvoids
      intro vertex membership
      simp at membership
      rcases membership with priorMembership | same
      · exact priorContained vertex priorMembership
      · subst vertex
        have middleMembership := priorContained middle prior.finish_mem
        have middleNotConclusion :=
          (TerminalTensor.mem_tensorLeftVertices_iff certificate
            left conclusion middle).mp middleMembership |>.2.1
        have currentNotConclusion : current ≠ conclusion := by
          intro same
          subst current
          exact avoidsConclusion (by simp)
        have currentInBounds :=
          (certificate.graphForSelection selected).adjacent_right_in_bounds
            tree.1 adjacency
        have fullAdjacency :=
          certificate.graphForSelection_adjacent_fullGraphWithout selection
            middleNotConclusion currentNotConclusion adjacency
        have terminalWellFormed := structural.2.2.2.2.1 _ splitting.1.1
        have leftInBounds := terminalWellFormed.2.2.2.1
        have middleInBounds :=
          (TerminalTensor.mem_tensorLeftVertices_iff certificate
            left conclusion middle).mp middleMembership |>.1
        have middleReachable :=
          (TerminalTensor.mem_tensorLeftVertices_iff certificate
            left conclusion middle).mp middleMembership |>.2.2
        have fullBounded :=
          certificate.fullGraphWithoutVertex_bounded structural conclusion
        have middleWalk :=
          (Graph.mem_closureN_vertexCount_iff_walk _ fullBounded
            leftInBounds middleInBounds).mp middleReachable
        have currentReachable : current ∈
            certificate.tensorLeftReachable left conclusion := by
          unfold tensorLeftReachable
          exact (Graph.mem_closureN_vertexCount_iff_walk _ fullBounded
            leftInBounds currentInBounds).mpr
            (.step middleWalk fullAdjacency)
        exact (TerminalTensor.mem_tensorLeftVertices_iff certificate
          left conclusion current).mpr
          ⟨currentInBounds, currentNotConclusion, currentReachable⟩

theorem simpleWalk_avoiding_conclusion_stays_right
    {certificate : Certificate} {left right conclusion start finish : Vertex}
    {selected : List Edge} {steps : Nat} {visited : List Vertex}
    (structural : certificate.StructurallyWellFormed)
    (splitting : certificate.SplittingTensor left right conclusion)
    (selection : ChoiceSelection certificate.parChoices selected)
    (tree : (certificate.graphForSelection selected).IsTree)
    (walk : (certificate.graphForSelection selected).SimpleWalk
      start steps visited finish)
    (startMembership :
      start ∈ certificate.tensorRightVertices left conclusion)
    (avoidsConclusion : conclusion ∉ visited) :
    ∀ vertex ∈ visited,
      vertex ∈ certificate.tensorRightVertices left conclusion := by
  induction walk with
  | refl =>
      intro vertex membership
      simp at membership
      subst vertex
      exact startMembership
  | @step priorSteps priorVisited middle current prior adjacency fresh ih =>
      have priorAvoids : conclusion ∉ priorVisited := by
        intro membership
        exact avoidsConclusion (by simp [membership])
      have priorContained := ih priorAvoids
      intro vertex membership
      simp at membership
      rcases membership with priorMembership | same
      · exact priorContained vertex priorMembership
      · subst vertex
        have middleMembership := priorContained middle prior.finish_mem
        have middleNotConclusion :=
          (TerminalTensor.mem_tensorRightVertices_iff certificate
            left conclusion middle).mp middleMembership |>.2.1
        have currentNotConclusion : current ≠ conclusion := by
          intro same
          subst current
          exact avoidsConclusion (by simp)
        have currentInBounds :=
          (certificate.graphForSelection selected).adjacent_right_in_bounds
            tree.1 adjacency
        have fullAdjacency :=
          certificate.graphForSelection_adjacent_fullGraphWithout selection
            middleNotConclusion currentNotConclusion adjacency
        have terminalWellFormed := structural.2.2.2.2.1 _ splitting.1.1
        have leftInBounds := terminalWellFormed.2.2.2.1
        have middleInBounds :=
          (TerminalTensor.mem_tensorRightVertices_iff certificate
            left conclusion middle).mp middleMembership |>.1
        have middleUnreachable :=
          (TerminalTensor.mem_tensorRightVertices_iff certificate
            left conclusion middle).mp middleMembership |>.2.2
        have fullBounded :=
          certificate.fullGraphWithoutVertex_bounded structural conclusion
        have currentUnreachable : current ∉
            certificate.tensorLeftReachable left conclusion := by
          intro currentReachable
          have currentWalk :=
            (Graph.mem_closureN_vertexCount_iff_walk _ fullBounded
              leftInBounds currentInBounds).mp currentReachable
          have reverseAdjacency :
              (certificate.fullGraphWithoutVertex conclusion).Adjacent
                current middle := by
            rcases fullAdjacency with ⟨edge, edgeMembership, direction⟩
            refine ⟨edge, edgeMembership, ?_⟩
            rcases direction with forward | backward
            · exact .inr forward
            · exact .inl backward
          have middleWalk := currentWalk.trans
            (.step (.refl current) reverseAdjacency)
          exact middleUnreachable
            ((Graph.mem_closureN_vertexCount_iff_walk _ fullBounded
              leftInBounds middleInBounds).mpr middleWalk)
        exact (TerminalTensor.mem_tensorRightVertices_iff certificate
          left conclusion current).mpr
          ⟨currentInBounds, currentNotConclusion, currentUnreachable⟩

theorem simpleWalk_left_endpoints_avoids_conclusion
    {certificate : Certificate} {left right conclusion start finish : Vertex}
    {selected : List Edge} {steps : Nat} {visited : List Vertex}
    (structural : certificate.StructurallyWellFormed)
    (splitting : certificate.SplittingTensor left right conclusion)
    (selection : ChoiceSelection certificate.parChoices selected)
    (tree : (certificate.graphForSelection selected).IsTree)
    (walk : (certificate.graphForSelection selected).SimpleWalk
      start steps visited finish)
    (startMembership :
      start ∈ certificate.tensorLeftVertices left conclusion)
    (finishMembership :
      finish ∈ certificate.tensorLeftVertices left conclusion) :
    conclusion ∉ visited := by
  induction walk with
  | refl =>
      have startNotConclusion :=
        (TerminalTensor.mem_tensorLeftVertices_iff certificate
          left conclusion start).mp startMembership |>.2.1
      simpa [eq_comm] using startNotConclusion
  | @step priorSteps priorVisited middle current prior adjacency fresh ih =>
      have currentNotConclusion :=
        (TerminalTensor.mem_tensorLeftVertices_iff certificate
          left conclusion current).mp finishMembership |>.2.1
      intro conclusionMembership
      simp at conclusionMembership
      rcases conclusionMembership with priorContains | currentIsConclusion
      · by_cases middleIsConclusion : middle = conclusion
        · subst middle
          have currentEndpoint :=
            (TerminalTensor.graphForSelection_adjacent_conclusion_iff
              structural splitting.1 selection).mp adjacency.symm
          have currentIsLeft : current = left := by
            rcases currentEndpoint with currentIsLeft | currentIsRight
            · exact currentIsLeft
            · subst current
              exact False.elim
                (TerminalTensor.vertex_partition_disjoint certificate
                  left conclusion right finishMembership
                  (TerminalTensor.right_mem_tensorRightVertices
                    structural splitting))
          cases prior with
          | refl =>
              have startNotConclusion :=
                (TerminalTensor.mem_tensorLeftVertices_iff certificate
                  left conclusion conclusion).mp startMembership |>.2.1
              exact startNotConclusion rfl
          | @step earlierSteps earlierVisited previous _ earlier enter
              conclusionFresh =>
              have previousEndpoint :=
                (TerminalTensor.graphForSelection_adjacent_conclusion_iff
                  structural splitting.1 selection).mp enter
              rcases previousEndpoint with previousIsLeft | previousIsRight
              · subst previous
                subst current
                exact fresh (List.mem_append.mpr (Or.inl earlier.finish_mem))
              · have earlierContained :=
                  TerminalTensor.simpleWalk_avoiding_conclusion_stays_left
                    structural splitting selection tree earlier startMembership
                    conclusionFresh
                have previousLeft :=
                  earlierContained previous earlier.finish_mem
                subst previous
                exact TerminalTensor.vertex_partition_disjoint certificate
                  left conclusion right previousLeft
                  (TerminalTensor.right_mem_tensorRightVertices
                    structural splitting)
        · have middleLeft :=
            TerminalTensor.graphForSelection_adjacent_preserves_left
              structural splitting selection finishMembership
              middleIsConclusion adjacency.symm
          exact (ih middleLeft) priorContains
      · exact currentNotConclusion currentIsConclusion.symm

theorem simpleWalk_right_endpoints_avoids_conclusion
    {certificate : Certificate} {left right conclusion start finish : Vertex}
    {selected : List Edge} {steps : Nat} {visited : List Vertex}
    (structural : certificate.StructurallyWellFormed)
    (splitting : certificate.SplittingTensor left right conclusion)
    (selection : ChoiceSelection certificate.parChoices selected)
    (tree : (certificate.graphForSelection selected).IsTree)
    (walk : (certificate.graphForSelection selected).SimpleWalk
      start steps visited finish)
    (startMembership :
      start ∈ certificate.tensorRightVertices left conclusion)
    (finishMembership :
      finish ∈ certificate.tensorRightVertices left conclusion) :
    conclusion ∉ visited := by
  induction walk with
  | refl =>
      have startNotConclusion :=
        (TerminalTensor.mem_tensorRightVertices_iff certificate
          left conclusion start).mp startMembership |>.2.1
      simpa [eq_comm] using startNotConclusion
  | @step priorSteps priorVisited middle current prior adjacency fresh ih =>
      have currentNotConclusion :=
        (TerminalTensor.mem_tensorRightVertices_iff certificate
          left conclusion current).mp finishMembership |>.2.1
      intro conclusionMembership
      simp at conclusionMembership
      rcases conclusionMembership with priorContains | currentIsConclusion
      · by_cases middleIsConclusion : middle = conclusion
        · subst middle
          have currentEndpoint :=
            (TerminalTensor.graphForSelection_adjacent_conclusion_iff
              structural splitting.1 selection).mp adjacency.symm
          have currentIsRight : current = right := by
            rcases currentEndpoint with currentIsLeft | currentIsRight
            · subst current
              exact False.elim
                (TerminalTensor.vertex_partition_disjoint certificate
                  left conclusion left
                  (TerminalTensor.left_mem_tensorLeftVertices
                    structural splitting.1) finishMembership)
            · exact currentIsRight
          cases prior with
          | refl =>
              have startNotConclusion :=
                (TerminalTensor.mem_tensorRightVertices_iff certificate
                  left conclusion conclusion).mp startMembership |>.2.1
              exact startNotConclusion rfl
          | @step earlierSteps earlierVisited previous _ earlier enter
              conclusionFresh =>
              have previousEndpoint :=
                (TerminalTensor.graphForSelection_adjacent_conclusion_iff
                  structural splitting.1 selection).mp enter
              rcases previousEndpoint with previousIsLeft | previousIsRight
              · have earlierContained :=
                  TerminalTensor.simpleWalk_avoiding_conclusion_stays_right
                    structural splitting selection tree earlier startMembership
                    conclusionFresh
                have previousRight :=
                  earlierContained previous earlier.finish_mem
                subst previous
                exact TerminalTensor.vertex_partition_disjoint certificate
                  left conclusion left
                  (TerminalTensor.left_mem_tensorLeftVertices
                    structural splitting.1) previousRight
              · subst previous
                subst current
                exact fresh (List.mem_append.mpr (Or.inl earlier.finish_mem))
        · have middleRight :=
            TerminalTensor.graphForSelection_adjacent_preserves_right
              structural splitting selection finishMembership
              middleIsConclusion adjacency.symm
          exact (ih middleRight) priorContains
      · exact currentNotConclusion currentIsConclusion.symm

theorem graph_restrictTo_left_connected
    {certificate : Certificate} {left right conclusion : Vertex}
    {selected : List Edge}
    (structural : certificate.StructurallyWellFormed)
    (splitting : certificate.SplittingTensor left right conclusion)
    (selection : ChoiceSelection certificate.parChoices selected)
    (tree : (certificate.graphForSelection selected).IsTree) :
    ((certificate.graphForSelection selected).restrictTo
      (certificate.tensorLeftVertices left conclusion)).Connected := by
  let vertices := certificate.tensorLeftVertices left conclusion
  have verticesPositive :=
    TerminalTensor.tensorLeftVertices_length_pos structural splitting.1
  refine ⟨by simpa [Graph.restrictTo, vertices] using verticesPositive, ?_⟩
  intro localVertex localInBounds
  have zeroInBounds : 0 < vertices.length := verticesPositive
  let oldStart := vertices[0]
  let oldFinish := vertices[localVertex]
  have oldStartMembership : oldStart ∈ vertices :=
    List.getElem_mem zeroInBounds
  have oldFinishMembership : oldFinish ∈ vertices :=
    List.getElem_mem localInBounds
  have oldStartInBounds :=
    (TerminalTensor.mem_tensorLeftVertices_iff certificate
      left conclusion oldStart).mp oldStartMembership |>.1
  have oldFinishInBounds :=
    (TerminalTensor.mem_tensorLeftVertices_iff certificate
      left conclusion oldFinish).mp oldFinishMembership |>.1
  have between : (certificate.graphForSelection selected).Walk
      oldStart oldFinish :=
    (tree.2.1.2 oldStart oldStartInBounds).reverse.trans
      (tree.2.1.2 oldFinish oldFinishInBounds)
  rcases between.toSimple with ⟨steps, visited, simple⟩
  have avoids :=
    TerminalTensor.simpleWalk_left_endpoints_avoids_conclusion
      structural splitting selection tree simple oldStartMembership
      oldFinishMembership
  have contained :=
    TerminalTensor.simpleWalk_avoiding_conclusion_stays_left
      structural splitting selection tree simple oldStartMembership avoids
  have restrictedWalk := simple.restrictTo contained
  have startIndex : vertices.idxOf oldStart = 0 :=
    idxOf_getElem_eq_index
      (TerminalTensor.tensorLeftVertices_nodup certificate left conclusion)
      0 zeroInBounds
  have finishIndex : vertices.idxOf oldFinish = localVertex :=
    idxOf_getElem_eq_index
      (TerminalTensor.tensorLeftVertices_nodup certificate left conclusion)
      localVertex localInBounds
  rw [startIndex, finishIndex] at restrictedWalk
  exact restrictedWalk

theorem graph_restrictTo_right_connected
    {certificate : Certificate} {left right conclusion : Vertex}
    {selected : List Edge}
    (structural : certificate.StructurallyWellFormed)
    (splitting : certificate.SplittingTensor left right conclusion)
    (selection : ChoiceSelection certificate.parChoices selected)
    (tree : (certificate.graphForSelection selected).IsTree) :
    ((certificate.graphForSelection selected).restrictTo
      (certificate.tensorRightVertices left conclusion)).Connected := by
  let vertices := certificate.tensorRightVertices left conclusion
  have verticesPositive :=
    TerminalTensor.tensorRightVertices_length_pos structural splitting
  refine ⟨by simpa [Graph.restrictTo, vertices] using verticesPositive, ?_⟩
  intro localVertex localInBounds
  have zeroInBounds : 0 < vertices.length := verticesPositive
  let oldStart := vertices[0]
  let oldFinish := vertices[localVertex]
  have oldStartMembership : oldStart ∈ vertices :=
    List.getElem_mem zeroInBounds
  have oldFinishMembership : oldFinish ∈ vertices :=
    List.getElem_mem localInBounds
  have oldStartInBounds :=
    (TerminalTensor.mem_tensorRightVertices_iff certificate
      left conclusion oldStart).mp oldStartMembership |>.1
  have oldFinishInBounds :=
    (TerminalTensor.mem_tensorRightVertices_iff certificate
      left conclusion oldFinish).mp oldFinishMembership |>.1
  have between : (certificate.graphForSelection selected).Walk
      oldStart oldFinish :=
    (tree.2.1.2 oldStart oldStartInBounds).reverse.trans
      (tree.2.1.2 oldFinish oldFinishInBounds)
  rcases between.toSimple with ⟨steps, visited, simple⟩
  have avoids :=
    TerminalTensor.simpleWalk_right_endpoints_avoids_conclusion
      structural splitting selection tree simple oldStartMembership
      oldFinishMembership
  have contained :=
    TerminalTensor.simpleWalk_avoiding_conclusion_stays_right
      structural splitting selection tree simple oldStartMembership avoids
  have restrictedWalk := simple.restrictTo contained
  have startIndex : vertices.idxOf oldStart = 0 :=
    idxOf_getElem_eq_index
      (TerminalTensor.tensorRightVertices_nodup certificate left conclusion)
      0 zeroInBounds
  have finishIndex : vertices.idxOf oldFinish = localVertex :=
    idxOf_getElem_eq_index
      (TerminalTensor.tensorRightVertices_nodup certificate left conclusion)
      localVertex localInBounds
  rw [startIndex, finishIndex] at restrictedWalk
  exact restrictedWalk

theorem graph_restrictTo_edges_length_partition
    {certificate : Certificate} {left right conclusion : Vertex}
    {selected : List Edge}
    (structural : certificate.StructurallyWellFormed)
    (splitting : certificate.SplittingTensor left right conclusion)
    (selection : ChoiceSelection certificate.parChoices selected)
    (tree : (certificate.graphForSelection selected).IsTree) :
    ((certificate.graphForSelection selected).restrictTo
          (certificate.tensorLeftVertices left conclusion)).edges.length +
        ((certificate.graphForSelection selected).restrictTo
          (certificate.tensorRightVertices left conclusion)).edges.length + 2 =
      (certificate.graphForSelection selected).edges.length := by
  let graph := certificate.graphForSelection selected
  let leftVertices := certificate.tensorLeftVertices left conclusion
  let rightVertices := certificate.tensorRightVertices left conclusion
  let leftContained : Edge → Bool := fun edge =>
    leftVertices.contains edge.first && leftVertices.contains edge.second
  let rightContained : Edge → Bool := fun edge =>
    rightVertices.contains edge.first && rightVertices.contains edge.second
  have classified : ∀ edge ∈ graph.edges,
      (leftContained edge = true ∧ rightContained edge = false ∧
        edge.incident conclusion = false) ∨
      (leftContained edge = false ∧ rightContained edge = true ∧
        edge.incident conclusion = false) ∨
      (leftContained edge = false ∧ rightContained edge = false ∧
        edge.incident conclusion = true) := by
    intro edge edgeMembership
    have edgeBounded := tree.1 edge edgeMembership
    have adjacency : graph.Adjacent edge.first edge.second :=
      ⟨edge, edgeMembership, .inl ⟨rfl, rfl⟩⟩
    by_cases incident : edge.incident conclusion = true
    · have incidentEndpoint :
          edge.first = conclusion ∨ edge.second = conclusion := by
        simpa [Edge.incident] using incident
      have conclusionNotLeft : conclusion ∉ leftVertices := by
        exact TerminalTensor.conclusion_not_mem_tensorLeftVertices
          certificate left conclusion
      have conclusionNotRight : conclusion ∉ rightVertices := by
        exact TerminalTensor.conclusion_not_mem_tensorRightVertices
          certificate left conclusion
      have leftRejected : leftContained edge = false := by
        rcases incidentEndpoint with firstConclusion | secondConclusion
        · simp [leftContained, firstConclusion, conclusionNotLeft]
        · simp [leftContained, secondConclusion, conclusionNotLeft]
      have rightRejected : rightContained edge = false := by
        rcases incidentEndpoint with firstConclusion | secondConclusion
        · simp [rightContained, firstConclusion, conclusionNotRight]
        · simp [rightContained, secondConclusion, conclusionNotRight]
      exact Or.inr (Or.inr ⟨leftRejected, rightRejected, incident⟩)
    · have endpointAvoidance :
          edge.first ≠ conclusion ∧ edge.second ≠ conclusion := by
        have incidentFalse : edge.incident conclusion = false := by
          cases incidentEquation : edge.incident conclusion with
          | false => rfl
          | true => exact False.elim (incident incidentEquation)
        simpa [Edge.incident] using incidentFalse
      have incidentFalse : edge.incident conclusion = false := by
        cases incidentEquation : edge.incident conclusion with
        | false => rfl
        | true => exact False.elim (incident incidentEquation)
      rcases TerminalTensor.vertex_partition certificate left conclusion
          edge.first edgeBounded.1 endpointAvoidance.1 with
        firstLeft | firstRight
      · have secondLeft :=
          TerminalTensor.graphForSelection_adjacent_preserves_left
            structural splitting selection firstLeft endpointAvoidance.2
            adjacency
        have firstNotRight : edge.first ∉ rightVertices := by
          intro firstRight
          exact TerminalTensor.vertex_partition_disjoint certificate
            left conclusion edge.first firstLeft firstRight
        exact Or.inl ⟨by
          simp [leftContained, leftVertices, firstLeft, secondLeft], by
          simp [rightContained, rightVertices, firstNotRight], incidentFalse⟩
      · have secondRight :=
          TerminalTensor.graphForSelection_adjacent_preserves_right
            structural splitting selection firstRight endpointAvoidance.2
            adjacency
        have firstNotLeft : edge.first ∉ leftVertices := by
          intro firstLeft
          exact TerminalTensor.vertex_partition_disjoint certificate
            left conclusion edge.first firstLeft firstRight
        exact Or.inr (Or.inl ⟨by
          simp [leftContained, leftVertices, firstNotLeft], by
          simp [rightContained, rightVertices, firstRight, secondRight],
          incidentFalse⟩)
  have edgePartition := length_filter_three_partition graph.edges
    leftContained rightContained (fun edge => edge.incident conclusion)
    classified
  have incidentCount :=
    TerminalTensor.graphForSelection_incidentCount structural splitting.1
      selection
  unfold Graph.incidentCount at incidentCount
  change (graph.edges.filter (fun edge => edge.incident conclusion)).length =
    2 at incidentCount
  rw [Graph.restrictTo_edges_length, Graph.restrictTo_edges_length]
  change (graph.edges.filter leftContained).length +
      (graph.edges.filter rightContained).length + 2 = graph.edges.length
  omega

theorem graph_restrictTo_trees
    {certificate : Certificate} {left right conclusion : Vertex}
    {selected : List Edge}
    (structural : certificate.StructurallyWellFormed)
    (splitting : certificate.SplittingTensor left right conclusion)
    (selection : ChoiceSelection certificate.parChoices selected)
    (tree : (certificate.graphForSelection selected).IsTree) :
    ((certificate.graphForSelection selected).restrictTo
        (certificate.tensorLeftVertices left conclusion)).IsTree ∧
      ((certificate.graphForSelection selected).restrictTo
        (certificate.tensorRightVertices left conclusion)).IsTree := by
  let inputGraph := certificate.graphForSelection selected
  let leftGraph := inputGraph.restrictTo
    (certificate.tensorLeftVertices left conclusion)
  let rightGraph := inputGraph.restrictTo
    (certificate.tensorRightVertices left conclusion)
  have leftBounded : leftGraph.Bounded := by
    simpa [leftGraph, inputGraph] using tree.1.restrictTo
      (certificate.tensorLeftVertices left conclusion)
  have rightBounded : rightGraph.Bounded := by
    simpa [rightGraph, inputGraph] using tree.1.restrictTo
      (certificate.tensorRightVertices left conclusion)
  have leftConnected : leftGraph.Connected := by
    simpa [leftGraph, inputGraph] using
      TerminalTensor.graph_restrictTo_left_connected structural splitting
        selection tree
  have rightConnected : rightGraph.Connected := by
    simpa [rightGraph, inputGraph] using
      TerminalTensor.graph_restrictTo_right_connected structural splitting
        selection tree
  have leftLower := leftConnected.vertexCount_le_edges_add_one
  have rightLower := rightConnected.vertexCount_le_edges_add_one
  change leftGraph.vertexCount ≤ leftGraph.edges.length + 1 at leftLower
  change rightGraph.vertexCount ≤ rightGraph.edges.length + 1 at rightLower
  have edgePartition :=
    TerminalTensor.graph_restrictTo_edges_length_partition structural
      splitting selection tree
  change leftGraph.edges.length + rightGraph.edges.length + 2 =
    inputGraph.edges.length at edgePartition
  have vertexPartition :=
    TerminalTensor.tensorVertices_length_partition structural splitting.1
  change leftGraph.vertexCount + rightGraph.vertexCount + 1 =
    inputGraph.vertexCount at vertexPartition
  have inputCount := tree.2.2
  change inputGraph.edges.length + 1 = inputGraph.vertexCount at inputCount
  have leftCount : leftGraph.edges.length + 1 = leftGraph.vertexCount := by
    omega
  have rightCount : rightGraph.edges.length + 1 = rightGraph.vertexCount := by
    omega
  constructor
  · exact ⟨leftBounded, leftConnected, leftCount⟩
  · exact ⟨rightBounded, rightConnected, rightCount⟩

end TerminalTensor

theorem TerminalPar.parChoices_incidentCount
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalPar left right conclusion) :
    (certificate.parChoices.filter fun choice =>
      choice.1.incident conclusion).length =
        certificate.producerCount conclusion := by
  let emitChoice : Link → Option (Edge × Edge) := fun
    | .par first second result =>
        some ({ first := first, second := result },
          { first := second, second := result })
    | _ => none
  change
    ((certificate.links.filterMap emitChoice).filter fun choice =>
      choice.1.incident conclusion).length =
        (certificate.links.filter (·.produces conclusion)).length
  suffices general : ∀ links : List Link,
      (∀ link ∈ links, link ∈ certificate.links) →
      ((links.filterMap emitChoice).filter fun choice =>
        choice.1.incident conclusion).length =
        (links.filter (·.produces conclusion)).length by
    exact general certificate.links (by simp)
  intro links subset
  induction links with
  | nil => rfl
  | cons head tail ih =>
      have headMembership : head ∈ certificate.links :=
        subset head (by simp)
      have tailSubset : ∀ link ∈ tail, link ∈ certificate.links := by
        intro link membership
        exact subset link (by simp [membership])
      have tailEquality := ih tailSubset
      cases head with
      | «axiom» first second => simpa [emitChoice, Link.produces] using tailEquality
      | tensor first second result =>
          have resultNotConclusion : result ≠ conclusion := by
            intro same
            subst result
            have impossible := TerminalPar.producer_unique structural terminal
              headMembership (by simp [Link.produces])
            cases impossible
          simpa [emitChoice, Link.produces, resultNotConclusion] using tailEquality
      | par first second result =>
          simp only [emitChoice, Edge.incident, Link.produces] at tailEquality
          have firstNotConclusion : first ≠ conclusion := by
            intro same
            subst first
            exact TerminalPar.no_parentUse structural terminal headMembership
              (by simp [Link.usesAsPremise, Link.premises])
          have firstBoolean : (first == conclusion) = false :=
            beq_eq_false_iff_ne.mpr firstNotConclusion
          cases resultBoolean : (result == conclusion) <;>
            simp [emitChoice, Link.produces, Edge.incident,
              firstBoolean, resultBoolean, tailEquality]

theorem TerminalPar.selected_incidentCount
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalPar left right conclusion)
    {selected : List Edge}
    (selection : ChoiceSelection certificate.parChoices selected) :
    (selected.filter (·.incident conclusion)).length = 1 := by
  rw [selection.filter_length_eq_of_pair_agreement
    (·.incident conclusion) (by
      intro choice membership
      exact TerminalPar.parChoice_incident_agreement structural terminal
        membership)]
  rw [TerminalPar.parChoices_incidentCount structural terminal]
  exact (TerminalPar.ownership structural terminal).1

theorem TerminalPar.fixedEdges_incidentCount
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalPar left right conclusion) :
    (certificate.fixedEdges.filter (·.incident conclusion)).length = 0 := by
  let emitFixed : Link → List Edge := fun
    | .axiom first second => [{ first, second }]
    | .tensor first second result =>
        [{ first := first, second := result },
         { first := second, second := result }]
    | .par _ _ _ => []
  change
    ((certificate.links.flatMap emitFixed).filter
      (·.incident conclusion)).length = 0
  suffices general : ∀ links : List Link,
      (∀ link ∈ links, link ∈ certificate.links) →
      ((links.flatMap emitFixed).filter
        (·.incident conclusion)).length = 0 by
    exact general certificate.links (by simp)
  intro links subset
  induction links with
  | nil => rfl
  | cons head tail ih =>
      have headMembership : head ∈ certificate.links :=
        subset head (by simp)
      have tailSubset : ∀ link ∈ tail, link ∈ certificate.links := by
        intro link membership
        exact subset link (by simp [membership])
      have tailEquality := ih tailSubset
      cases head with
      | «axiom» first second =>
          have firstNotConclusion : first ≠ conclusion := by
            intro same
            subst first
            have impossible := TerminalPar.unique_incident structural terminal
              headMembership (by simp [Link.vertices])
            cases impossible
          have secondNotConclusion : second ≠ conclusion := by
            intro same
            subst second
            have impossible := TerminalPar.unique_incident structural terminal
              headMembership (by simp [Link.vertices])
            cases impossible
          have firstBoolean : (first == conclusion) = false :=
            beq_eq_false_iff_ne.mpr firstNotConclusion
          have secondBoolean : (second == conclusion) = false :=
            beq_eq_false_iff_ne.mpr secondNotConclusion
          simpa [emitFixed, Edge.incident, firstBoolean, secondBoolean]
            using tailEquality
      | tensor first second result =>
          have firstNotConclusion : first ≠ conclusion := by
            intro same
            subst first
            exact TerminalPar.no_parentUse structural terminal headMembership
              (by simp [Link.usesAsPremise, Link.premises])
          have secondNotConclusion : second ≠ conclusion := by
            intro same
            subst second
            exact TerminalPar.no_parentUse structural terminal headMembership
              (by simp [Link.usesAsPremise, Link.premises])
          have resultNotConclusion : result ≠ conclusion := by
            intro same
            subst result
            have impossible := TerminalPar.producer_unique structural terminal
              headMembership (by simp [Link.produces])
            cases impossible
          have firstBoolean : (first == conclusion) = false :=
            beq_eq_false_iff_ne.mpr firstNotConclusion
          have secondBoolean : (second == conclusion) = false :=
            beq_eq_false_iff_ne.mpr secondNotConclusion
          have resultBoolean : (result == conclusion) = false :=
            beq_eq_false_iff_ne.mpr resultNotConclusion
          simpa [emitFixed, Edge.incident, firstBoolean, secondBoolean,
            resultBoolean] using tailEquality
      | par first second result => simpa [emitFixed] using tailEquality

theorem TerminalPar.graphForSelection_leaf
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalPar left right conclusion)
    {selected : List Edge}
    (selection : ChoiceSelection certificate.parChoices selected) :
    (certificate.graphForSelection selected).Leaf conclusion := by
  constructor
  · exact structural.2.2.1 conclusion terminal.2
  · unfold Graph.incidentCount
    change ((certificate.fixedEdges ++ selected).filter
      (·.incident conclusion)).length = 1
    rw [List.filter_append, List.length_append,
      TerminalPar.fixedEdges_incidentCount structural terminal,
      TerminalPar.selected_incidentCount structural terminal selection]

/-- Executable list of terminal par links. It is only a candidate finder; the
subnet construction and preservation theorem remain proof obligations. -/
def terminalPars (certificate : Certificate) :
    List (Vertex × Vertex × Vertex) :=
  certificate.links.filterMap fun
    | .par left right conclusion =>
        if conclusion ∈ certificate.conclusions then
          some (left, right, conclusion)
        else
          none
    | _ => none

def terminalTensors (certificate : Certificate) :
    List (Vertex × Vertex × Vertex) :=
  certificate.links.filterMap fun
    | .tensor left right conclusion =>
        if conclusion ∈ certificate.conclusions then
          some (left, right, conclusion)
        else
          none
    | _ => none

/-- Candidate inverse of a terminal par rule. The produced premise removes the
par conclusion occurrence and its incident link, compacts all vertex names,
and puts the two premises at the tail of the ordered boundary. This function
does not itself assert preservation; `peelTerminalParChecked?` supplies the
safe executable boundary and the general preservation theorem is the next
formal obligation. -/
def peelTerminalParCandidate? (certificate : Certificate)
    (left right conclusion : Vertex) : Option Certificate := do
  if !certificate.links.contains (.par left right conclusion) then none
  if !certificate.conclusions.contains conclusion then none
  let left' ← deleteVertex? conclusion left
  let right' ← deleteVertex? conclusion right
  let context ← (certificate.conclusions.filter (· != conclusion)).mapM
    (deleteVertex? conclusion)
  pure {
    formulas := certificate.formulas.eraseIdxIfInBounds conclusion
    links := certificate.links.filterMap (Link.deleteVertex? conclusion)
    conclusions := context ++ [left', right'] }

/-- Proposition-friendly form of terminal-par peeling. It agrees with the
optional candidate on every structurally well-formed terminal par. -/
def peelTerminalPar (certificate : Certificate)
    (left right conclusion : Vertex) : Certificate where
  formulas := certificate.formulas.eraseIdxIfInBounds conclusion
  links := certificate.links.filterMap (Link.deleteVertex? conclusion)
  conclusions :=
    (certificate.conclusions.filter (· != conclusion)).map
      (compactVertex conclusion) ++
    [compactVertex conclusion left, compactVertex conclusion right]

theorem mapM_deleteVertex?_eq_of_avoids (removed : Vertex)
    (values : List Vertex)
    (avoids : ∀ vertex ∈ values, vertex ≠ removed) :
    values.mapM (deleteVertex? removed) =
      some (values.map (compactVertex removed)) := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
      have headNotRemoved := avoids head (by simp)
      have tailAvoids : ∀ vertex ∈ tail, vertex ≠ removed := by
        intro vertex membership
        exact avoids vertex (by simp [membership])
      simp [deleteVertex?_eq_some_of_ne headNotRemoved, ih tailAvoids]

theorem peelTerminalParCandidate?_eq_some
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalPar left right conclusion) :
    certificate.peelTerminalParCandidate? left right conclusion =
      some (certificate.peelTerminalPar left right conclusion) := by
  have terminalWellFormed := structural.2.2.2.2.1 _ terminal.1
  rcases terminalWellFormed with
    ⟨_, leftNotConclusion, rightNotConclusion, _, _, _, _⟩
  have filteredAvoids : ∀ vertex ∈
      certificate.conclusions.filter (· != conclusion),
      vertex ≠ conclusion := by
    intro vertex membership
    simp only [List.mem_filter] at membership
    simpa using membership.2
  have contextMap := mapM_deleteVertex?_eq_of_avoids conclusion
    (certificate.conclusions.filter (· != conclusion)) filteredAvoids
  simp [peelTerminalParCandidate?, peelTerminalPar, terminal.1, terminal.2,
    deleteVertex?_eq_some_of_ne leftNotConclusion,
    deleteVertex?_eq_some_of_ne rightNotConclusion,
    contextMap]

theorem peelTerminalPar_formula?_compact
    {certificate : Certificate} {left right conclusion vertex : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalPar left right conclusion)
    (vertexNotConclusion : vertex ≠ conclusion) :
    (certificate.peelTerminalPar left right conclusion).formula?
      (compactVertex conclusion vertex) = certificate.formula? vertex := by
  have conclusionInBounds := structural.2.2.1 conclusion terminal.2
  by_cases before : vertex < conclusion
  · simp [peelTerminalPar, formula?, Array.eraseIdxIfInBounds,
      conclusionInBounds, compactVertex, before, Array.getElem?_eraseIdx]
  · have conclusionLeVertex : conclusion ≤ vertex := Nat.le_of_not_gt before
    have conclusionNotVertex : conclusion ≠ vertex := Ne.symm vertexNotConclusion
    have after : conclusion < vertex :=
      Nat.lt_of_le_of_ne conclusionLeVertex conclusionNotVertex
    have compactAtOrAfter : conclusion ≤ vertex - 1 :=
      Nat.le_sub_one_of_lt after
    have compactNotBefore : ¬vertex - 1 < conclusion :=
      Nat.not_lt.mpr compactAtOrAfter
    have vertexPositive : 1 ≤ vertex :=
      Nat.succ_le_of_lt (Nat.zero_lt_of_lt after)
    have restore : vertex - 1 + 1 = vertex :=
      Nat.sub_add_cancel vertexPositive
    simp [peelTerminalPar, formula?, Array.eraseIdxIfInBounds,
      conclusionInBounds, compactVertex, before, Array.getElem?_eraseIdx,
      compactNotBefore, restore]

/-- Exact logical boundary interface for a terminal-par inverse step.  The
peeled premise ends in the two premise formulas, while rebuilding their par is
a permutation of the original ordered boundary. -/
theorem TerminalPar.logicalBoundaryData
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalPar left right conclusion) :
    ∃ context leftFormula rightFormula inputSequent,
      (certificate.peelTerminalPar left right conclusion).conclusionFormulas? =
        some (context ++ [leftFormula, rightFormula]) ∧
      certificate.conclusionFormulas? = some inputSequent ∧
      (context ++ [Formula.par leftFormula rightFormula]).Perm
        inputSequent := by
  let fallback : Formula := .atom "" false
  have linkWellFormed := structural.2.2.2.2.1 _ terminal.1
  rcases linkWellFormed with
    ⟨_leftRightDifferent, leftNotConclusion, rightNotConclusion,
      leftInBounds, rightInBounds, conclusionInBounds, typing⟩
  cases leftEquation : certificate.formula? left with
  | none => simp [leftEquation] at typing
  | some leftFormula =>
      cases rightEquation : certificate.formula? right with
      | none => simp [leftEquation, rightEquation] at typing
      | some rightFormula =>
          cases conclusionEquation : certificate.formula? conclusion with
          | none =>
              simp [leftEquation, rightEquation, conclusionEquation] at typing
          | some conclusionFormula =>
              have conclusionFormulaEquation :
                  conclusionFormula = Formula.par leftFormula rightFormula := by
                simpa [leftEquation, rightEquation, conclusionEquation]
                  using typing
              subst conclusionFormula
              let contextVertices := certificate.conclusions.erase conclusion
              let context := contextVertices.map fun vertex =>
                certificate.formulas.getD vertex fallback
              let inputSequent := certificate.conclusions.map fun vertex =>
                certificate.formulas.getD vertex fallback
              have originalNodup : certificate.conclusions.Nodup :=
                nodup_of_eraseDups_length_eq structural.2.2.2.1
              have filteredEquation :
                  certificate.conclusions.filter (· != conclusion) =
                    contextVertices := by
                exact (List.Nodup.erase_eq_filter originalNodup conclusion).symm
              have contextLabels :
                  ((certificate.conclusions.filter (· != conclusion)).map
                    (compactVertex conclusion)).mapM
                      (certificate.peelTerminalPar left right conclusion).formula? =
                    some context := by
                rw [filteredEquation]
                rw [List.mapM_map]
                apply list_mapM_eq_some_map_of_forall
                intro vertex membership
                change
                  (certificate.peelTerminalPar left right conclusion).formula?
                      (compactVertex conclusion vertex) = _
                have originalMembership : vertex ∈ certificate.conclusions :=
                  List.mem_of_mem_erase membership
                have vertexNotConclusion : vertex ≠ conclusion := by
                  exact (originalNodup.mem_erase_iff.mp membership).1
                rw [peelTerminalPar_formula?_compact structural terminal
                  vertexNotConclusion]
                have vertexInBounds := structural.2.2.1 vertex originalMembership
                simp [formula?, vertexInBounds]
              have leftPremiseLabel :
                  (certificate.peelTerminalPar left right conclusion).formula?
                      (compactVertex conclusion left) = some leftFormula := by
                rw [peelTerminalPar_formula?_compact structural terminal
                  leftNotConclusion, leftEquation]
              have rightPremiseLabel :
                  (certificate.peelTerminalPar left right conclusion).formula?
                      (compactVertex conclusion right) = some rightFormula := by
                rw [peelTerminalPar_formula?_compact structural terminal
                  rightNotConclusion, rightEquation]
              have premiseLabels :
                  Certificate.conclusionFormulas?
                      (certificate.peelTerminalPar left right conclusion) =
                    some (context ++ [leftFormula, rightFormula]) := by
                unfold conclusionFormulas?
                change
                  (((certificate.conclusions.filter (· != conclusion)).map
                      (compactVertex conclusion) ++
                    [compactVertex conclusion left,
                      compactVertex conclusion right]).mapM
                      (Certificate.formula?
                        (certificate.peelTerminalPar left right conclusion))) = _
                rw [List.mapM_append, contextLabels]
                simp [leftPremiseLabel, rightPremiseLabel]
              have inputLabels : certificate.conclusionFormulas? =
                  some inputSequent := by
                exact structural.conclusionFormulas?_eq_getD fallback
              have vertexPermutation :
                  (contextVertices ++ [conclusion]).Perm
                    certificate.conclusions := by
                exact List.perm_append_comm.trans
                  (List.perm_cons_erase terminal.2).symm
              have labelPermutation := vertexPermutation.map fun vertex =>
                certificate.formulas.getD vertex fallback
              have conclusionLabel :
                  certificate.formulas.getD conclusion fallback =
                    Formula.par leftFormula rightFormula := by
                simpa [formula?, conclusionInBounds] using conclusionEquation
              refine ⟨context, leftFormula, rightFormula, inputSequent,
                premiseLabels, inputLabels, ?_⟩
              have normalizedLabelPermutation :
                  (context ++ [certificate.formulas.getD conclusion fallback]).Perm
                    inputSequent := by
                simpa only [List.map_append, List.map_singleton] using
                  labelPermutation
              rw [conclusionLabel] at normalizedLabelPermutation
              exact normalizedLabelPermutation

/-- Occurrence-level boundary reconstruction for a terminal par inverse.
After peeling, applying par to the two final premise roots yields the old
boundary with the par conclusion rotated to the end. Pulling the original
boundary back through the insertion renaming is therefore an executable
exchange target, even when boundary formulas are syntactically equal. -/
theorem TerminalPar.occurrenceBoundaryReconstruction
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalPar left right conclusion) :
    let premise := certificate.peelTerminalPar left right conclusion
    let sourceBoundary :=
      (certificate.conclusions.filter (· != conclusion)).map
          (Certificate.compactVertex conclusion) ++
        [premise.formulas.size]
    ∃ placement : VertexRenaming (premise.formulas.size + 1),
      sourceBoundary.map placement.forward =
          certificate.conclusions.erase conclusion ++ [conclusion] ∧
        sourceBoundary.Perm
          (certificate.conclusions.map placement.inverse) := by
  dsimp only
  have conclusionInBounds := structural.2.2.1 conclusion terminal.2
  have sizeEquation :
      (certificate.peelTerminalPar left right conclusion).formulas.size + 1 =
        certificate.formulas.size := by
    have peelSize :
        (certificate.peelTerminalPar left right conclusion).formulas.size =
          certificate.formulas.size - 1 := by
      simp [peelTerminalPar, Array.eraseIdxIfInBounds, conclusionInBounds]
    rw [peelSize]
    exact Nat.sub_add_cancel structural.1
  have placementInBounds : conclusion <
      (certificate.peelTerminalPar left right conclusion).formulas.size + 1 := by
    simpa [sizeEquation] using conclusionInBounds
  let placement := VertexRenaming.insertLastAt
    (certificate.peelTerminalPar left right conclusion).formulas.size
    conclusion placementInBounds
  let context := certificate.conclusions.filter (· != conclusion)
  have contextMapped :
      (context.map (Certificate.compactVertex conclusion)).map
          placement.forward = context := by
    rw [List.map_map]
    calc
      List.map (placement.forward ∘ Certificate.compactVertex conclusion) context =
          List.map id context := by
        apply List.map_congr_left
        intro vertex membership
        have filtered := List.mem_filter.mp membership
        have vertexMembership : vertex ∈ certificate.conclusions := filtered.1
        have vertexNotConclusion : vertex ≠ conclusion := by
          simpa using filtered.2
        have vertexInBounds := structural.2.2.1 vertex vertexMembership
        have compactInBounds : Certificate.compactVertex conclusion vertex <
            (certificate.peelTerminalPar left right conclusion).formulas.size := by
          have compactBound := Certificate.compactVertex_lt conclusionInBounds
            vertexInBounds vertexNotConclusion
          have peelSize :
              (certificate.peelTerminalPar left right conclusion).formulas.size =
                certificate.formulas.size - 1 := by
            simp [peelTerminalPar, Array.eraseIdxIfInBounds, conclusionInBounds]
          simpa [peelSize] using compactBound
        simp only [Function.comp_apply, id_eq, placement]
        rw [VertexRenaming.insertLastAt_forward_old _ _ placementInBounds
          compactInBounds]
        change Certificate.expandVertex conclusion
          (Certificate.compactVertex conclusion vertex) = vertex
        exact Certificate.expandVertex_compactVertex_of_ne vertexNotConclusion
      _ = context := by simpa using (List.map_id context)
  have originalNodup : certificate.conclusions.Nodup :=
    nodup_of_eraseDups_length_eq structural.2.2.2.1
  have contextEquation : context = certificate.conclusions.erase conclusion := by
    simpa [context] using
      (List.Nodup.erase_eq_filter originalNodup conclusion).symm
  let sourceBoundary :=
    context.map (Certificate.compactVertex conclusion) ++
      [(certificate.peelTerminalPar left right conclusion).formulas.size]
  have sourceMapped : sourceBoundary.map placement.forward =
      certificate.conclusions.erase conclusion ++ [conclusion] := by
    calc
      sourceBoundary.map placement.forward = context ++ [conclusion] := by
        simp only [sourceBoundary, List.map_append, List.map_singleton]
        rw [contextMapped]
        simp [placement]
      _ = certificate.conclusions.erase conclusion ++ [conclusion] := by
        rw [contextEquation]
  have erasedPermutation :
      (certificate.conclusions.erase conclusion ++ [conclusion]).Perm
        certificate.conclusions := by
    have rotation :
        (certificate.conclusions.erase conclusion ++ [conclusion]).Perm
          ([conclusion] ++ certificate.conclusions.erase conclusion) :=
      List.perm_append_comm
    exact rotation.trans (by
      simpa using (List.perm_cons_erase terminal.2).symm)
  have targetMapped :
      (certificate.conclusions.map placement.inverse).map placement.forward =
        certificate.conclusions := by
    simp [List.map_map, Function.comp_def, placement.forward_inverse]
  have mappedPermutation :
      (sourceBoundary.map placement.forward).Perm
        ((certificate.conclusions.map placement.inverse).map
          placement.forward) := by
    rw [sourceMapped, targetMapped]
    exact erasedPermutation
  have pulled := mappedPermutation.map placement.inverse
  refine ⟨placement, sourceMapped, ?_⟩
  simpa [List.map_map, Function.comp_def, placement.inverse_forward] using pulled

/-- The old links surviving a terminal-par peel are restored pointwise by the
insertion renaming. Appending the unique terminal link then recovers the input
link multiset, independently of its storage position. -/
theorem TerminalPar.peelLinks_reindex_append_perm
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalPar left right conclusion)
    (placementInBounds : conclusion <
      (certificate.peelTerminalPar left right conclusion).formulas.size + 1) :
    let placement := VertexRenaming.insertLastAt
      (certificate.peelTerminalPar left right conclusion).formulas.size
      conclusion placementInBounds
    ((certificate.peelTerminalPar left right conclusion).links.map
        (Link.reindex placement) ++ [Link.par left right conclusion]).Perm
      certificate.links := by
  dsimp only
  let premise := certificate.peelTerminalPar left right conclusion
  let terminalLink : Link := .par left right conclusion
  let placement := VertexRenaming.insertLastAt premise.formulas.size
    conclusion placementInBounds
  have conclusionInBounds := structural.2.2.1 conclusion terminal.2
  have sizeEquation : premise.formulas.size + 1 = certificate.formulas.size := by
    have peelSize : premise.formulas.size = certificate.formulas.size - 1 := by
      simp [premise, peelTerminalPar, Array.eraseIdxIfInBounds,
        conclusionInBounds]
    rw [peelSize]
    exact Nat.sub_add_cancel structural.1
  have restoreSegment : ∀ segment : List Link,
      (∀ link ∈ segment, link ∈ certificate.links) →
      terminalLink ∉ segment →
      (segment.filterMap (Link.deleteVertex? conclusion)).map
          (Link.reindex placement) = segment := by
    intro segment subset avoidsTerminal
    induction segment with
    | nil => rfl
    | cons head tail ih =>
        have headMembership : head ∈ certificate.links :=
          subset head (by simp)
        have tailSubset : ∀ link ∈ tail, link ∈ certificate.links := by
          intro link membership
          exact subset link (by simp [membership])
        have headDifferent : head ≠ terminalLink := by
          intro same
          subst head
          exact avoidsTerminal (by simp)
        have tailAvoids : terminalLink ∉ tail := by
          intro membership
          exact avoidsTerminal (by simp [membership])
        have tailIH := ih tailSubset tailAvoids
        cases deleted : head.deleteVertex? conclusion with
        | none =>
            have same := (TerminalPar.deletion_none_iff_eq structural terminal
              headMembership).mp deleted
            exact False.elim (headDifferent same)
        | some compacted =>
            rcases (Link.deleteVertex?_eq_some_iff head compacted conclusion).mp
                deleted with ⟨headAvoids, rfl⟩
            have headWellFormed := structural.2.2.2.2.1 head headMembership
            have headInBounds : ∀ vertex ∈ head.vertices,
                vertex < premise.formulas.size + 1 := by
              intro vertex membership
              have originalBound := headWellFormed.vertex_in_bounds membership
              simpa [sizeEquation] using originalBound
            have restored := Link.reindex_insertLastAt_compactVertices
              placementInBounds head headInBounds headAvoids
            have restoredAtPlacement :
                (head.compactVertices conclusion).reindex placement = head := by
              simpa [premise, placement] using restored
            simp [deleted, restoredAtPlacement, tailIH]
  have countOriginal : certificate.links.count terminalLink = 1 := by
    change certificate.links.count (.par left right conclusion) = 1
    rw [← List.count_filter (p := (·.produces conclusion)) (by
      simp [Link.produces])]
    rw [TerminalPar.producer_filter_eq structural terminal]
    simp
  rcases List.mem_iff_append.mp terminal.1 with
    ⟨before, after, linksEquation⟩
  have beforeSubset : ∀ link ∈ before, link ∈ certificate.links := by
    intro link membership
    rw [linksEquation]
    simp [membership]
  have afterSubset : ∀ link ∈ after, link ∈ certificate.links := by
    intro link membership
    rw [linksEquation]
    simp [membership]
  have countDecomposition := congrArg (List.count terminalLink) linksEquation
  rw [countOriginal] at countDecomposition
  have countSplit : before.count terminalLink + after.count terminalLink = 0 := by
    simp [terminalLink, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] at countDecomposition
    rcases countDecomposition with ⟨beforeZero, afterZero⟩
    simp [terminalLink, beforeZero, afterZero]
  have beforeAvoids : terminalLink ∉ before := by
    apply List.count_eq_zero.mp
    omega
  have afterAvoids : terminalLink ∉ after := by
    apply List.count_eq_zero.mp
    omega
  have beforeRestored := restoreSegment before beforeSubset beforeAvoids
  have afterRestored := restoreSegment after afterSubset afterAvoids
  have restoredRemaining :
      (premise.links.map (Link.reindex placement)) =
        certificate.links.erase terminalLink := by
    change ((certificate.links.filterMap
      (Link.deleteVertex? conclusion)).map (Link.reindex placement)) = _
    rw [linksEquation, List.filterMap_append, List.map_append]
    simp only [List.filterMap_cons]
    have terminalDeleted : terminalLink.deleteVertex? conclusion = none := by
      simp [terminalLink, Link.deleteVertex?, Certificate.deleteVertex?]
    rw [terminalDeleted]
    simp only [List.filterMap_nil, List.nil_append, List.map_append,
      List.map_nil, List.append_nil]
    rw [beforeRestored, afterRestored]
    symm
    simp only [terminalLink] at beforeAvoids ⊢
    rw [List.erase_append_right _ beforeAvoids, List.erase_cons_head]
  rw [restoredRemaining]
  exact List.perm_append_comm.trans (by
    simpa [terminalLink] using (List.perm_cons_erase terminal.1).symm)

/-- Restoring the deleted position and appending the typed par formula recovers
the input formula-occurrence array exactly. -/
theorem TerminalPar.peelFormulas_reindex_append_eq
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalPar left right conclusion)
    (boundary : List Vertex)
    (placementInBounds : conclusion <
      (certificate.peelTerminalPar left right conclusion).formulas.size + 1) :
    ∃ leftFormula rightFormula,
      let premise := certificate.peelTerminalPar left right conclusion
      let rebuilt := premise.appendParOccurrence leftFormula rightFormula
        (Certificate.compactVertex conclusion left)
        (Certificate.compactVertex conclusion right) boundary
      let placement := premise.appendParPlacement leftFormula rightFormula
        (Certificate.compactVertex conclusion left)
        (Certificate.compactVertex conclusion right) boundary conclusion
        placementInBounds
      (rebuilt.reindex placement).formulas = certificate.formulas := by
  let premise := certificate.peelTerminalPar left right conclusion
  have terminalWellFormed := structural.2.2.2.2.1 _ terminal.1
  rcases terminalWellFormed.par_formulaData with
    ⟨leftFormula, rightFormula, leftEquation, rightEquation,
      conclusionEquation⟩
  refine ⟨leftFormula, rightFormula, ?_⟩
  dsimp only
  let rebuilt := premise.appendParOccurrence leftFormula rightFormula
    (Certificate.compactVertex conclusion left)
    (Certificate.compactVertex conclusion right) boundary
  let placement := premise.appendParPlacement leftFormula rightFormula
    (Certificate.compactVertex conclusion left)
    (Certificate.compactVertex conclusion right) boundary conclusion
    placementInBounds
  have conclusionInBounds := structural.2.2.1 conclusion terminal.2
  have sizeEquation : premise.formulas.size + 1 = certificate.formulas.size := by
    have peelSize : premise.formulas.size = certificate.formulas.size - 1 := by
      simp [premise, peelTerminalPar, Array.eraseIdxIfInBounds,
        conclusionInBounds]
    rw [peelSize]
    exact Nat.sub_add_cancel structural.1
  apply Array.ext_getElem?
  intro index
  change (rebuilt.reindex placement).formula? index =
    certificate.formula? index
  by_cases indexInBounds : index < certificate.formulas.size
  · by_cases atConclusion : index = conclusion
    · subst index
      have lastForward : placement.forward premise.formulas.size = conclusion := by
        simp [placement, Certificate.appendParPlacement]
      have lookup := rebuilt.reindex_formula?_forward placement
        premise.formulas.size
      rw [lastForward] at lookup
      have rebuiltLast : rebuilt.formula? premise.formulas.size =
          some (.par leftFormula rightFormula) := by
        simp [rebuilt, Certificate.appendParOccurrence, Certificate.formula?]
      exact lookup.trans (rebuiltLast.trans conclusionEquation.symm)
    · have compactInBounds : Certificate.compactVertex conclusion index <
          premise.formulas.size := by
        have compactBound := Certificate.compactVertex_lt conclusionInBounds
          indexInBounds atConclusion
        have peelSize : premise.formulas.size = certificate.formulas.size - 1 := by
          simp [premise, peelTerminalPar, Array.eraseIdxIfInBounds,
            conclusionInBounds]
        simpa [peelSize] using compactBound
      have oldForward : placement.forward
          (Certificate.compactVertex conclusion index) = index := by
        simp only [placement, Certificate.appendParPlacement_forward]
        rw [VertexRenaming.insertLastAt_forward_old _ _ placementInBounds
          compactInBounds]
        change Certificate.expandVertex conclusion
          (Certificate.compactVertex conclusion index) = index
        exact Certificate.expandVertex_compactVertex_of_ne atConclusion
      have lookup := rebuilt.reindex_formula?_forward placement
        (Certificate.compactVertex conclusion index)
      rw [oldForward] at lookup
      have rebuiltOld : rebuilt.formula?
          (Certificate.compactVertex conclusion index) =
          premise.formula? (Certificate.compactVertex conclusion index) := by
        have compactNotLast : Certificate.compactVertex conclusion index ≠
            premise.formulas.size := Nat.ne_of_lt compactInBounds
        simp [rebuilt, Certificate.appendParOccurrence, Certificate.formula?,
          Array.getElem?_push, compactInBounds, compactNotLast]
      exact lookup.trans (rebuiltOld.trans
        (certificate.peelTerminalPar_formula?_compact structural terminal
          atConclusion))
  · have inputOutside : certificate.formulas.size ≤ index :=
      Nat.le_of_not_gt indexInBounds
    have rebuiltSize : (rebuilt.reindex placement).formulas.size =
        certificate.formulas.size := by
      simp [rebuilt, premise, sizeEquation]
    have rebuiltOutside : (rebuilt.reindex placement).formulas.size ≤ index := by
      rw [rebuiltSize]
      exact inputOutside
    simp [Certificate.formula?, Array.getElem?_eq_none_iff.mpr inputOutside,
      Array.getElem?_eq_none_iff.mpr rebuiltOutside]

/-- A peeled terminal par can be rebuilt, exchanged into the pullback of the
original boundary, and related to the input by one bounded renaming followed by
one link permutation. -/
theorem TerminalPar.rebuild_directProofNetEquivalent
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalPar left right conclusion) :
    ∃ (leftFormula rightFormula : Formula)
        (placementInBounds : conclusion <
          (certificate.peelTerminalPar left right conclusion).formulas.size + 1),
      let premise := certificate.peelTerminalPar left right conclusion
      let placement := VertexRenaming.insertLastAt premise.formulas.size
        conclusion placementInBounds
      let targetBoundary := certificate.conclusions.map placement.inverse
      Certificate.DirectProofNetEquivalent
        (premise.appendParOccurrence leftFormula rightFormula
          (Certificate.compactVertex conclusion left)
          (Certificate.compactVertex conclusion right) targetBoundary)
        certificate := by
  let premise := certificate.peelTerminalPar left right conclusion
  have conclusionInBounds := structural.2.2.1 conclusion terminal.2
  have sizeEquation : premise.formulas.size + 1 = certificate.formulas.size := by
    have peelSize : premise.formulas.size = certificate.formulas.size - 1 := by
      simp [premise, peelTerminalPar, Array.eraseIdxIfInBounds,
        conclusionInBounds]
    rw [peelSize]
    exact Nat.sub_add_cancel structural.1
  have placementInBounds : conclusion < premise.formulas.size + 1 := by
    simpa [sizeEquation] using conclusionInBounds
  let rawPlacement := VertexRenaming.insertLastAt premise.formulas.size
    conclusion placementInBounds
  let targetBoundary := certificate.conclusions.map rawPlacement.inverse
  rcases TerminalPar.peelFormulas_reindex_append_eq structural terminal
      targetBoundary placementInBounds with
    ⟨leftFormula, rightFormula, formulaEquality⟩
  refine ⟨leftFormula, rightFormula, placementInBounds, ?_⟩
  dsimp only
  let rebuilt := premise.appendParOccurrence leftFormula rightFormula
    (Certificate.compactVertex conclusion left)
    (Certificate.compactVertex conclusion right) targetBoundary
  let placement := premise.appendParPlacement leftFormula rightFormula
    (Certificate.compactVertex conclusion left)
    (Certificate.compactVertex conclusion right) targetBoundary conclusion
    placementInBounds
  refine ⟨placement, {
    formulas := ?_
    links := ?_
    conclusions := ?_ }⟩
  · simpa [rebuilt, placement, premise, targetBoundary, rawPlacement] using
      formulaEquality
  · have linkPermutation := TerminalPar.peelLinks_reindex_append_perm
      structural terminal placementInBounds
    have terminalWellFormed := structural.2.2.2.2.1 _ terminal.1
    have leftInBounds := terminalWellFormed.vertex_in_bounds
      (vertex := left) (by simp [Link.vertices])
    have rightInBounds := terminalWellFormed.vertex_in_bounds
      (vertex := right) (by simp [Link.vertices])
    have leftNotConclusion : left ≠ conclusion := terminalWellFormed.2.1
    have rightNotConclusion : right ≠ conclusion := terminalWellFormed.2.2.1
    have compactLeftInBounds : Certificate.compactVertex conclusion left <
        premise.formulas.size := by
      have bound := Certificate.compactVertex_lt conclusionInBounds
        leftInBounds leftNotConclusion
      have peelSize : premise.formulas.size = certificate.formulas.size - 1 := by
        simp [premise, peelTerminalPar, Array.eraseIdxIfInBounds,
          conclusionInBounds]
      simpa [peelSize] using bound
    have compactRightInBounds : Certificate.compactVertex conclusion right <
        premise.formulas.size := by
      have bound := Certificate.compactVertex_lt conclusionInBounds
        rightInBounds rightNotConclusion
      have peelSize : premise.formulas.size = certificate.formulas.size - 1 := by
        simp [premise, peelTerminalPar, Array.eraseIdxIfInBounds,
          conclusionInBounds]
      simpa [peelSize] using bound
    have leftRestored : rawPlacement.forward
        (Certificate.compactVertex conclusion left) = left := by
      rw [VertexRenaming.insertLastAt_forward_old _ _ placementInBounds
        compactLeftInBounds]
      exact Certificate.expandVertex_compactVertex_of_ne leftNotConclusion
    have rightRestored : rawPlacement.forward
        (Certificate.compactVertex conclusion right) = right := by
      rw [VertexRenaming.insertLastAt_forward_old _ _ placementInBounds
        compactRightInBounds]
      exact Certificate.expandVertex_compactVertex_of_ne rightNotConclusion
    have oldLinks : premise.links.map (Link.reindex placement) =
        premise.links.map (Link.reindex rawPlacement) := by
      apply List.map_congr_left
      intro link _membership
      cases link <;>
        simp [Link.reindex, placement, Certificate.appendParPlacement,
          rawPlacement]
    have newLink : Link.reindex placement
        (.par (Certificate.compactVertex conclusion left)
          (Certificate.compactVertex conclusion right) premise.formulas.size) =
        .par left right conclusion := by
      simp [Link.reindex, placement, Certificate.appendParPlacement,
        rawPlacement, leftRestored, rightRestored]
    change ((premise.links ++ [
      Link.par (Certificate.compactVertex conclusion left)
        (Certificate.compactVertex conclusion right)
        premise.formulas.size]).map (Link.reindex placement)).Perm
      certificate.links
    rw [List.map_append, List.map_singleton, oldLinks, newLink]
    simpa [premise, rawPlacement] using linkPermutation
  · change targetBoundary.map placement.forward = certificate.conclusions
    have placementForward : placement.forward = rawPlacement.forward := by
      simp [placement, rawPlacement]
    rw [placementForward]
    simp [targetBoundary, List.map_map, Function.comp_def,
      rawPlacement.forward_inverse]

theorem peelTerminalPar_conclusions_nodup
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalPar left right conclusion) :
    (certificate.peelTerminalPar left right conclusion).conclusions.Nodup := by
  let remaining := certificate.conclusions.filter (· != conclusion)
  let context := remaining.map (compactVertex conclusion)
  have originalNodup : certificate.conclusions.Nodup :=
    nodup_of_eraseDups_length_eq structural.2.2.2.1
  have remainingNodup : remaining.Nodup :=
    List.filter_sublist.nodup originalNodup
  have contextNodup : context.Nodup := by
    apply nodup_map_of_injective_on remainingNodup
    intro first firstMembership second secondMembership same
    have firstNotConclusion : first ≠ conclusion := by
      have filtered := List.mem_filter.mp firstMembership
      simpa using filtered.2
    have secondNotConclusion : second ≠ conclusion := by
      have filtered := List.mem_filter.mp secondMembership
      simpa using filtered.2
    exact compactVertex_injective_of_ne firstNotConclusion
      secondNotConclusion same
  have terminalWellFormed := structural.2.2.2.2.1 _ terminal.1
  rcases terminalWellFormed with
    ⟨leftNotRight, leftNotConclusion, rightNotConclusion, _, _, _, _⟩
  have premiseBoundaries := TerminalPar.premises_not_conclusions
    structural terminal
  have compactLeftFresh : compactVertex conclusion left ∉ context := by
    intro membership
    rcases List.mem_map.mp membership with
      ⟨vertex, vertexMembership, same⟩
    have filtered := List.mem_filter.mp vertexMembership
    have vertexNotConclusion : vertex ≠ conclusion := by
      simpa using filtered.2
    have oldSame := compactVertex_injective_of_ne vertexNotConclusion
      leftNotConclusion same
    subst vertex
    exact premiseBoundaries.1 filtered.1
  have compactRightFresh : compactVertex conclusion right ∉ context := by
    intro membership
    rcases List.mem_map.mp membership with
      ⟨vertex, vertexMembership, same⟩
    have filtered := List.mem_filter.mp vertexMembership
    have vertexNotConclusion : vertex ≠ conclusion := by
      simpa using filtered.2
    have oldSame := compactVertex_injective_of_ne vertexNotConclusion
      rightNotConclusion same
    subst vertex
    exact premiseBoundaries.2 filtered.1
  have compactDistinct :
      compactVertex conclusion left ≠ compactVertex conclusion right := by
    intro same
    exact leftNotRight (compactVertex_injective_of_ne leftNotConclusion
      rightNotConclusion same)
  change (context ++ [compactVertex conclusion left,
    compactVertex conclusion right]).Nodup
  rw [List.nodup_append]
  refine ⟨contextNodup, by simp [compactDistinct], ?_⟩
  intro vertex vertexMembership boundary boundaryMembership
  simp at boundaryMembership
  rcases boundaryMembership with rfl | rfl
  · intro same
    subst vertex
    exact compactLeftFresh vertexMembership
  · intro same
    subst vertex
    exact compactRightFresh vertexMembership

theorem peelTerminalPar_conclusions_eraseDups_length
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalPar left right conclusion) :
    (certificate.peelTerminalPar left right conclusion).conclusions.eraseDups.length =
      (certificate.peelTerminalPar left right conclusion).conclusions.length := by
  rw [eraseDups_eq_self_of_nodup
    (peelTerminalPar_conclusions_nodup structural terminal)]

theorem LinkWellFormed.deleteVertex
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalPar left right conclusion)
    {link compacted : Link}
    (wellFormed : certificate.LinkWellFormed link)
    (deleted : link.deleteVertex? conclusion = some compacted) :
    (certificate.peelTerminalPar left right conclusion).LinkWellFormed
      compacted := by
  have conclusionInBounds := structural.2.2.1 conclusion terminal.2
  have formulaSize :
      (certificate.peelTerminalPar left right conclusion).formulas.size =
        certificate.formulas.size - 1 := by
    simp [peelTerminalPar, Array.eraseIdxIfInBounds, conclusionInBounds]
  cases link with
  | «axiom» first second =>
      by_cases firstDeleted : first = conclusion
      · subst first
        simp [Link.deleteVertex?, Certificate.deleteVertex?] at deleted
      · by_cases secondDeleted : second = conclusion
        · subst second
          simp [Link.deleteVertex?, Certificate.deleteVertex?] at deleted
        · simp [Link.deleteVertex?, Certificate.deleteVertex?, firstDeleted,
            secondDeleted] at deleted
          subst compacted
          rcases wellFormed with
            ⟨different, firstInBounds, secondInBounds, typing⟩
          refine ⟨?_, ?_, ?_, ?_⟩
          · exact fun same => different
              (compactVertex_injective_of_ne firstDeleted secondDeleted same)
          · rw [formulaSize]
            exact compactVertex_lt conclusionInBounds firstInBounds firstDeleted
          · rw [formulaSize]
            exact compactVertex_lt conclusionInBounds secondInBounds secondDeleted
          · rw [peelTerminalPar_formula?_compact structural terminal firstDeleted,
              peelTerminalPar_formula?_compact structural terminal secondDeleted]
            exact typing
  | tensor first second result =>
      by_cases firstDeleted : first = conclusion
      · subst first
        simp [Link.deleteVertex?, Certificate.deleteVertex?] at deleted
      · by_cases secondDeleted : second = conclusion
        · subst second
          simp [Link.deleteVertex?, Certificate.deleteVertex?, firstDeleted] at deleted
        · by_cases resultDeleted : result = conclusion
          · subst result
            simp [Link.deleteVertex?, Certificate.deleteVertex?, firstDeleted,
              secondDeleted] at deleted
          · simp [Link.deleteVertex?, Certificate.deleteVertex?, firstDeleted,
              secondDeleted, resultDeleted] at deleted
            subst compacted
            rcases wellFormed with
              ⟨firstSecond, firstResult, secondResult, firstInBounds,
                secondInBounds, resultInBounds, typing⟩
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · exact fun same => firstSecond
                (compactVertex_injective_of_ne firstDeleted secondDeleted same)
            · exact fun same => firstResult
                (compactVertex_injective_of_ne firstDeleted resultDeleted same)
            · exact fun same => secondResult
                (compactVertex_injective_of_ne secondDeleted resultDeleted same)
            · rw [formulaSize]
              exact compactVertex_lt conclusionInBounds firstInBounds firstDeleted
            · rw [formulaSize]
              exact compactVertex_lt conclusionInBounds secondInBounds secondDeleted
            · rw [formulaSize]
              exact compactVertex_lt conclusionInBounds resultInBounds resultDeleted
            · rw [peelTerminalPar_formula?_compact structural terminal firstDeleted,
                peelTerminalPar_formula?_compact structural terminal secondDeleted,
                peelTerminalPar_formula?_compact structural terminal resultDeleted]
              exact typing
  | par first second result =>
      by_cases firstDeleted : first = conclusion
      · subst first
        simp [Link.deleteVertex?, Certificate.deleteVertex?] at deleted
      · by_cases secondDeleted : second = conclusion
        · subst second
          simp [Link.deleteVertex?, Certificate.deleteVertex?, firstDeleted] at deleted
        · by_cases resultDeleted : result = conclusion
          · subst result
            simp [Link.deleteVertex?, Certificate.deleteVertex?, firstDeleted,
              secondDeleted] at deleted
          · simp [Link.deleteVertex?, Certificate.deleteVertex?, firstDeleted,
              secondDeleted, resultDeleted] at deleted
            subst compacted
            rcases wellFormed with
              ⟨firstSecond, firstResult, secondResult, firstInBounds,
                secondInBounds, resultInBounds, typing⟩
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · exact fun same => firstSecond
                (compactVertex_injective_of_ne firstDeleted secondDeleted same)
            · exact fun same => firstResult
                (compactVertex_injective_of_ne firstDeleted resultDeleted same)
            · exact fun same => secondResult
                (compactVertex_injective_of_ne secondDeleted resultDeleted same)
            · rw [formulaSize]
              exact compactVertex_lt conclusionInBounds firstInBounds firstDeleted
            · rw [formulaSize]
              exact compactVertex_lt conclusionInBounds secondInBounds secondDeleted
            · rw [formulaSize]
              exact compactVertex_lt conclusionInBounds resultInBounds resultDeleted
            · rw [peelTerminalPar_formula?_compact structural terminal firstDeleted,
                peelTerminalPar_formula?_compact structural terminal secondDeleted,
                peelTerminalPar_formula?_compact structural terminal resultDeleted]
              exact typing

theorem peelTerminalPar_links_wellFormed
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalPar left right conclusion) :
    ∀ link ∈ (certificate.peelTerminalPar left right conclusion).links,
      (certificate.peelTerminalPar left right conclusion).LinkWellFormed link := by
  intro link membership
  change link ∈ certificate.links.filterMap
    (Link.deleteVertex? conclusion) at membership
  simp only [List.mem_filterMap] at membership
  rcases membership with ⟨original, originalMembership, deleted⟩
  exact LinkWellFormed.deleteVertex structural terminal
    (structural.2.2.2.2.1 original originalMembership) deleted

/-- Every structural obligation for terminal-par peeling except global node
ownership. The omitted final field is isolated explicitly so that this result
cannot be mistaken for full structural preservation. -/
theorem peelTerminalPar_structural_prefix
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalPar left right conclusion) :
    0 < (certificate.peelTerminalPar left right conclusion).formulas.size ∧
    0 < (certificate.peelTerminalPar left right conclusion).conclusions.length ∧
    (∀ vertex ∈
      (certificate.peelTerminalPar left right conclusion).conclusions,
      vertex <
        (certificate.peelTerminalPar left right conclusion).formulas.size) ∧
    (certificate.peelTerminalPar left right conclusion).conclusions.eraseDups.length =
      (certificate.peelTerminalPar left right conclusion).conclusions.length ∧
    (∀ link ∈ (certificate.peelTerminalPar left right conclusion).links,
      (certificate.peelTerminalPar left right conclusion).LinkWellFormed link) := by
  have terminalWellFormed := structural.2.2.2.2.1 _ terminal.1
  rcases terminalWellFormed with
    ⟨_, leftNotConclusion, rightNotConclusion, leftInBounds,
      rightInBounds, conclusionInBounds, _⟩
  have formulaSize :
      (certificate.peelTerminalPar left right conclusion).formulas.size =
        certificate.formulas.size - 1 := by
    simp [peelTerminalPar, Array.eraseIdxIfInBounds, conclusionInBounds]
  refine ⟨?_, ?_, ?_,
    peelTerminalPar_conclusions_eraseDups_length structural terminal,
    peelTerminalPar_links_wellFormed structural terminal⟩
  · rw [formulaSize]
    have onePremisePositive : 0 < left ∨ 0 < conclusion := by
      by_cases leftZero : left = 0
      · right
        exact Nat.pos_of_ne_zero fun conclusionZero =>
          leftNotConclusion (leftZero.trans conclusionZero.symm)
      · exact Or.inl (Nat.pos_of_ne_zero leftZero)
    have oneLtSize : 1 < certificate.formulas.size := by
      rcases onePremisePositive with leftPositive | conclusionPositive
      · exact Nat.lt_of_le_of_lt leftPositive leftInBounds
      · exact Nat.lt_of_le_of_lt conclusionPositive conclusionInBounds
    exact Nat.sub_pos_of_lt oneLtSize
  · simp [peelTerminalPar]
  · intro vertex membership
    change vertex ∈
      (certificate.conclusions.filter (· != conclusion)).map
          (compactVertex conclusion) ++
        [compactVertex conclusion left,
          compactVertex conclusion right] at membership
    rw [List.mem_append] at membership
    rcases membership with contextMembership | premiseMembership
    · rcases List.mem_map.mp contextMembership with
        ⟨original, originalMembership, rfl⟩
      have filtered := List.mem_filter.mp originalMembership
      have originalNotConclusion : original ≠ conclusion := by
        simpa using filtered.2
      rw [formulaSize]
      exact compactVertex_lt conclusionInBounds
        (structural.2.2.1 original filtered.1) originalNotConclusion
    · simp at premiseMembership
      rcases premiseMembership with rfl | rfl
      · rw [formulaSize]
        exact compactVertex_lt conclusionInBounds leftInBounds
          leftNotConclusion
      · rw [formulaSize]
        exact compactVertex_lt conclusionInBounds rightInBounds
          rightNotConclusion

theorem peelTerminalPar_axiomCount_compact
    {certificate : Certificate} {left right conclusion vertex : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalPar left right conclusion)
    (vertexNotConclusion : vertex ≠ conclusion) :
    (certificate.peelTerminalPar left right conclusion).axiomCount
        (compactVertex conclusion vertex) =
      certificate.axiomCount vertex := by
  unfold axiomCount
  change ((certificate.links.filterMap
      (Link.deleteVertex? conclusion)).filter
        (·.containsAxiomEndpoint (compactVertex conclusion vertex))).length =
    (certificate.links.filter (·.containsAxiomEndpoint vertex)).length
  apply length_filter_filterMap_eq
  intro link membership
  cases deleted : link.deleteVertex? conclusion with
  | none =>
      have same := (TerminalPar.deletion_none_iff_eq structural terminal
        membership).mp deleted
      subst link
      rfl
  | some compacted =>
      exact Link.containsAxiomEndpoint_deleteVertex?_eq_some
        vertexNotConclusion deleted

theorem peelTerminalPar_producerCount_compact
    {certificate : Certificate} {left right conclusion vertex : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalPar left right conclusion)
    (vertexNotConclusion : vertex ≠ conclusion) :
    (certificate.peelTerminalPar left right conclusion).producerCount
        (compactVertex conclusion vertex) =
      certificate.producerCount vertex := by
  unfold producerCount
  change ((certificate.links.filterMap
      (Link.deleteVertex? conclusion)).filter
        (·.produces (compactVertex conclusion vertex))).length =
    (certificate.links.filter (·.produces vertex)).length
  apply length_filter_filterMap_eq
  intro link membership
  cases deleted : link.deleteVertex? conclusion with
  | none =>
      have same := (TerminalPar.deletion_none_iff_eq structural terminal
        membership).mp deleted
      subst link
      simp [Link.produces, Ne.symm vertexNotConclusion]
  | some compacted =>
      exact Link.produces_deleteVertex?_eq_some vertexNotConclusion deleted

theorem peelTerminalPar_parentUseCount_compact
    {certificate : Certificate} {left right conclusion vertex : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalPar left right conclusion)
    (vertexNotConclusion : vertex ≠ conclusion)
    (vertexNotLeft : vertex ≠ left) (vertexNotRight : vertex ≠ right) :
    (certificate.peelTerminalPar left right conclusion).parentUseCount
        (compactVertex conclusion vertex) =
      certificate.parentUseCount vertex := by
  unfold parentUseCount
  change ((certificate.links.filterMap
      (Link.deleteVertex? conclusion)).filter
        (·.usesAsPremise (compactVertex conclusion vertex))).length =
    (certificate.links.filter (·.usesAsPremise vertex)).length
  apply length_filter_filterMap_eq
  intro link membership
  cases deleted : link.deleteVertex? conclusion with
  | none =>
      have same := (TerminalPar.deletion_none_iff_eq structural terminal
        membership).mp deleted
      subst link
      simp [Link.usesAsPremise, Link.premises, vertexNotLeft,
        vertexNotRight]
  | some compacted =>
      exact Link.usesAsPremise_deleteVertex?_eq_some
        vertexNotConclusion deleted

theorem peelTerminalPar_parentUseCount_premise_zero
    {certificate : Certificate} {left right conclusion premise : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalPar left right conclusion)
    (isPremise : premise = left ∨ premise = right) :
    (certificate.peelTerminalPar left right conclusion).parentUseCount
        (compactVertex conclusion premise) = 0 := by
  have terminalWellFormed := structural.2.2.2.2.1 _ terminal.1
  rcases terminalWellFormed with
    ⟨_, leftNotConclusion, rightNotConclusion, leftInBounds,
      rightInBounds, _, _⟩
  have premiseNotConclusion : premise ≠ conclusion := by
    rcases isPremise with rfl | rfl
    · exact leftNotConclusion
    · exact rightNotConclusion
  have premiseInBounds : premise < certificate.formulas.size := by
    rcases isPremise with rfl | rfl
    · exact leftInBounds
    · exact rightInBounds
  have premiseNotBoundary : premise ∉ certificate.conclusions := by
    have boundaries := TerminalPar.premises_not_conclusions structural terminal
    rcases isPremise with rfl | rfl
    · exact boundaries.1
    · exact boundaries.2
  have originalNode := structural.2.2.2.2.2 premise premiseInBounds
  have originalCount : certificate.parentUseCount premise = 1 := by
    simpa [Certificate.NodeWellFormed, premiseNotBoundary] using originalNode.2
  have terminalUses :
      (Link.par left right conclusion).usesAsPremise premise = true := by
    rcases isPremise with rfl | rfl <;>
      simp [Link.usesAsPremise, Link.premises]
  unfold parentUseCount
  change ((certificate.links.filterMap
      (Link.deleteVertex? conclusion)).filter
        (·.usesAsPremise (compactVertex conclusion premise))).length = 0
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro compacted compactedMembership
  cases compactedUses :
      compacted.usesAsPremise (compactVertex conclusion premise) with
  | false => simp
  | true =>
      simp only [List.mem_filterMap] at compactedMembership
      rcases compactedMembership with
        ⟨original, originalMembership, deleted⟩
      have originalUses := Link.usesAsPremise_deleteVertex?_eq_some
        premiseNotConclusion deleted
      rw [compactedUses] at originalUses
      have originalUsesTrue : original.usesAsPremise premise = true := by
        simpa using originalUses.symm
      have unique := eq_of_mem_filter_length_one
        (show (certificate.links.filter
          (·.usesAsPremise premise)).length = 1 from originalCount)
        originalMembership originalUsesTrue terminal.1 terminalUses
      subst original
      simp [Link.deleteVertex?, Certificate.deleteVertex?] at deleted

theorem peelTerminalPar_compact_mem_conclusions_iff
    {certificate : Certificate} {left right conclusion vertex : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalPar left right conclusion)
    (vertexNotConclusion : vertex ≠ conclusion) :
    compactVertex conclusion vertex ∈
        (certificate.peelTerminalPar left right conclusion).conclusions ↔
      vertex ∈ certificate.conclusions ∨ vertex = left ∨ vertex = right := by
  have terminalWellFormed := structural.2.2.2.2.1 _ terminal.1
  have leftNotConclusion := terminalWellFormed.2.1
  have rightNotConclusion := terminalWellFormed.2.2.1
  change compactVertex conclusion vertex ∈
      (certificate.conclusions.filter (· != conclusion)).map
          (compactVertex conclusion) ++
        [compactVertex conclusion left,
          compactVertex conclusion right] ↔ _
  constructor
  · intro membership
    rw [List.mem_append] at membership
    rcases membership with contextMembership | premiseMembership
    · rcases List.mem_map.mp contextMembership with
        ⟨original, originalMembership, same⟩
      have filtered := List.mem_filter.mp originalMembership
      have originalNotConclusion : original ≠ conclusion := by
        simpa using filtered.2
      have originalSame := compactVertex_injective_of_ne
        originalNotConclusion vertexNotConclusion same
      subst original
      exact Or.inl filtered.1
    · simp at premiseMembership
      rcases premiseMembership with same | same
      · exact Or.inr (Or.inl (compactVertex_injective_of_ne
          vertexNotConclusion leftNotConclusion same))
      · exact Or.inr (Or.inr (compactVertex_injective_of_ne
          vertexNotConclusion rightNotConclusion same))
  · intro membership
    rw [List.mem_append]
    rcases membership with oldBoundary | same
    · left
      apply List.mem_map.mpr
      exact ⟨vertex, List.mem_filter.mpr
        ⟨oldBoundary, by simpa using vertexNotConclusion⟩, rfl⟩
    · rcases same with rfl | rfl
      · right
        simp
      · right
        simp

theorem peelTerminalPar_nodeWellFormed_compact
    {certificate : Certificate} {left right conclusion vertex : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalPar left right conclusion)
    (vertexInBounds : vertex < certificate.formulas.size)
    (vertexNotConclusion : vertex ≠ conclusion) :
    (certificate.peelTerminalPar left right conclusion).NodeWellFormed
      (compactVertex conclusion vertex) := by
  have originalNode := structural.2.2.2.2.2 vertex vertexInBounds
  unfold NodeWellFormed at originalNode ⊢
  rw [peelTerminalPar_formula?_compact structural terminal
    vertexNotConclusion]
  constructor
  · cases formula : certificate.formula? vertex with
    | none => simp [formula] at originalNode
    | some value =>
        cases value with
        | atom name positive =>
            simp only [formula] at originalNode ⊢
            rw [peelTerminalPar_axiomCount_compact structural terminal
              vertexNotConclusion]
            exact originalNode.1
        | tensor first second =>
            simp only [formula] at originalNode ⊢
            rw [peelTerminalPar_producerCount_compact structural terminal
              vertexNotConclusion]
            exact originalNode.1
        | par first second =>
            simp only [formula] at originalNode ⊢
            rw [peelTerminalPar_producerCount_compact structural terminal
              vertexNotConclusion]
            exact originalNode.1
  · by_cases isLeft : vertex = left
    · subst vertex
      have newBoundary : compactVertex conclusion left ∈
          (certificate.peelTerminalPar left right conclusion).conclusions :=
        (peelTerminalPar_compact_mem_conclusions_iff structural terminal
          (structural.2.2.2.2.1 _ terminal.1).2.1).mpr
          (Or.inr (Or.inl rfl))
      rw [if_pos newBoundary]
      exact peelTerminalPar_parentUseCount_premise_zero structural terminal
        (Or.inl rfl)
    · by_cases isRight : vertex = right
      · subst vertex
        have newBoundary : compactVertex conclusion right ∈
            (certificate.peelTerminalPar left right conclusion).conclusions :=
          (peelTerminalPar_compact_mem_conclusions_iff structural terminal
            (structural.2.2.2.2.1 _ terminal.1).2.2.1).mpr
            (Or.inr (Or.inr rfl))
        rw [if_pos newBoundary]
        exact peelTerminalPar_parentUseCount_premise_zero structural terminal
          (Or.inr rfl)
      · have boundaryIff : compactVertex conclusion vertex ∈
            (certificate.peelTerminalPar left right conclusion).conclusions ↔
            vertex ∈ certificate.conclusions := by
          rw [peelTerminalPar_compact_mem_conclusions_iff structural terminal
            vertexNotConclusion]
          simp [isLeft, isRight]
        by_cases oldBoundary : vertex ∈ certificate.conclusions
        · have newBoundary := boundaryIff.mpr oldBoundary
          rw [if_pos newBoundary,
            peelTerminalPar_parentUseCount_compact structural terminal
              vertexNotConclusion isLeft isRight]
          simpa [oldBoundary] using originalNode.2
        · have newBoundary : compactVertex conclusion vertex ∉
              (certificate.peelTerminalPar left right conclusion).conclusions :=
            fun membership => oldBoundary (boundaryIff.mp membership)
          rw [if_neg newBoundary,
            peelTerminalPar_parentUseCount_compact structural terminal
              vertexNotConclusion isLeft isRight]
          simpa [oldBoundary] using originalNode.2

theorem peelTerminalPar_nodes_wellFormed
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalPar left right conclusion) :
    ∀ vertex,
      vertex <
        (certificate.peelTerminalPar left right conclusion).formulas.size →
      (certificate.peelTerminalPar left right conclusion).NodeWellFormed
        vertex := by
  intro vertex vertexInBounds
  have conclusionInBounds := structural.2.2.1 conclusion terminal.2
  have formulaSize :
      (certificate.peelTerminalPar left right conclusion).formulas.size =
        certificate.formulas.size - 1 := by
    simp [peelTerminalPar, Array.eraseIdxIfInBounds, conclusionInBounds]
  have compactedInBounds : vertex < certificate.formulas.size - 1 := by
    simpa [formulaSize] using vertexInBounds
  let original := expandVertex conclusion vertex
  have originalInBounds : original < certificate.formulas.size :=
    expandVertex_lt conclusionInBounds compactedInBounds
  have originalNotConclusion : original ≠ conclusion :=
    expandVertex_ne conclusion vertex
  have node := peelTerminalPar_nodeWellFormed_compact structural terminal
    originalInBounds originalNotConclusion
  simpa [original, compactVertex_expandVertex] using node

/-- Removing a terminal par link and exposing its two premises preserves the
complete Boolean-free structural specification. -/
theorem peelTerminalPar_structurallyWellFormed
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalPar left right conclusion) :
    (certificate.peelTerminalPar left right conclusion).StructurallyWellFormed := by
  rcases peelTerminalPar_structural_prefix structural terminal with
    ⟨formulasPositive, conclusionsPositive, conclusionsInBounds,
      conclusionsUnique, linksWellFormed⟩
  exact ⟨formulasPositive, conclusionsPositive, conclusionsInBounds,
    conclusionsUnique, linksWellFormed,
    peelTerminalPar_nodes_wellFormed structural terminal⟩

theorem peelTerminalPar_wellFormed
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalPar left right conclusion) :
    (certificate.peelTerminalPar left right conclusion).wellFormed = true :=
  (Certificate.wellFormed_iff_structurallyWellFormed
    (certificate.peelTerminalPar left right conclusion)).mpr
    (peelTerminalPar_structurallyWellFormed structural terminal)

theorem peelTerminalPar_parChoices
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalPar left right conclusion) :
    (certificate.peelTerminalPar left right conclusion).parChoices =
      certificate.parChoices.filterMap
        (ParChoice.deleteVertex? conclusion) := by
  let emitChoice : Link → Option (Edge × Edge) := fun
    | .par first second result =>
        some ({ first := first, second := result },
          { first := second, second := result })
    | _ => none
  change
    ((certificate.links.filterMap (Link.deleteVertex? conclusion)).filterMap
      emitChoice) =
    (certificate.links.filterMap emitChoice).filterMap
      (ParChoice.deleteVertex? conclusion)
  suffices general : ∀ links : List Link,
      (∀ link ∈ links, link ∈ certificate.links) →
      ((links.filterMap (Link.deleteVertex? conclusion)).filterMap
        emitChoice) =
      (links.filterMap emitChoice).filterMap
        (ParChoice.deleteVertex? conclusion) by
    exact general certificate.links (by simp)
  intro links subset
  induction links with
  | nil => rfl
  | cons head tail ih =>
      have headMembership : head ∈ certificate.links :=
        subset head (by simp)
      have tailSubset : ∀ link ∈ tail, link ∈ certificate.links := by
        intro link membership
        exact subset link (by simp [membership])
      have tailEquality := ih tailSubset
      cases deleted : head.deleteVertex? conclusion with
      | none =>
          have same := (TerminalPar.deletion_none_iff_eq structural terminal
            headMembership).mp deleted
          subst head
          simpa [emitChoice, deleted, Link.deleteVertex?,
            ParChoice.deleteVertex?, Edge.deleteVertex?,
            Certificate.deleteVertex?] using tailEquality
      | some compacted =>
          rcases (Link.deleteVertex?_eq_some_iff head compacted conclusion).mp
            deleted with ⟨avoids, rfl⟩
          cases head with
          | «axiom» first second =>
              simpa [emitChoice, deleted, Link.compactVertices] using tailEquality
          | tensor first second result =>
              simpa [emitChoice, deleted, Link.compactVertices] using tailEquality
          | par first second result =>
              simp [Link.vertices] at avoids
              have firstNotConclusion : first ≠ conclusion := Ne.symm avoids.1
              have secondNotConclusion : second ≠ conclusion :=
                Ne.symm avoids.2.1
              have resultNotConclusion : result ≠ conclusion :=
                Ne.symm avoids.2.2
              simpa [emitChoice, deleted, Link.compactVertices,
                ParChoice.deleteVertex?, Edge.deleteVertex?,
                Certificate.deleteVertex?, firstNotConclusion,
                secondNotConclusion, resultNotConclusion] using tailEquality

theorem peelTerminalPar_fixedEdges
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalPar left right conclusion) :
    (certificate.peelTerminalPar left right conclusion).fixedEdges =
      certificate.fixedEdges.filterMap (Edge.deleteVertex? conclusion) := by
  let emitFixed : Link → List Edge := fun
    | .axiom first second => [{ first, second }]
    | .tensor first second result =>
        [{ first := first, second := result },
         { first := second, second := result }]
    | .par _ _ _ => []
  change
    (certificate.links.filterMap
      (Link.deleteVertex? conclusion)).flatMap emitFixed =
    (certificate.links.flatMap emitFixed).filterMap
      (Edge.deleteVertex? conclusion)
  suffices general : ∀ links : List Link,
      (∀ link ∈ links, link ∈ certificate.links) →
      (links.filterMap (Link.deleteVertex? conclusion)).flatMap emitFixed =
      (links.flatMap emitFixed).filterMap (Edge.deleteVertex? conclusion) by
    exact general certificate.links (by simp)
  intro links subset
  induction links with
  | nil => rfl
  | cons head tail ih =>
      have headMembership : head ∈ certificate.links :=
        subset head (by simp)
      have tailSubset : ∀ link ∈ tail, link ∈ certificate.links := by
        intro link membership
        exact subset link (by simp [membership])
      have tailEquality := ih tailSubset
      cases deleted : head.deleteVertex? conclusion with
      | none =>
          have same := (TerminalPar.deletion_none_iff_eq structural terminal
            headMembership).mp deleted
          subst head
          simpa [emitFixed, deleted, Link.deleteVertex?,
            Certificate.deleteVertex?] using tailEquality
      | some compacted =>
          rcases (Link.deleteVertex?_eq_some_iff head compacted conclusion).mp
            deleted with ⟨avoids, rfl⟩
          cases head with
          | «axiom» first second =>
              simp [Link.vertices] at avoids
              have firstNotConclusion : first ≠ conclusion := Ne.symm avoids.1
              have secondNotConclusion : second ≠ conclusion :=
                Ne.symm avoids.2
              simpa [emitFixed, deleted, Link.compactVertices,
                Edge.deleteVertex?, Certificate.deleteVertex?,
                firstNotConclusion, secondNotConclusion] using tailEquality
          | tensor first second result =>
              simp [Link.vertices] at avoids
              have firstNotConclusion : first ≠ conclusion := Ne.symm avoids.1
              have secondNotConclusion : second ≠ conclusion :=
                Ne.symm avoids.2.1
              have resultNotConclusion : result ≠ conclusion :=
                Ne.symm avoids.2.2
              simpa [emitFixed, deleted, Link.compactVertices,
                Edge.deleteVertex?, Certificate.deleteVertex?,
                firstNotConclusion, secondNotConclusion,
                resultNotConclusion] using tailEquality
          | par first second result =>
              simpa [emitFixed, deleted, Link.compactVertices]
                using tailEquality

/-- Checker-gated terminal-par premise. Even before the general preservation
theorem is complete, callers cannot accidentally treat a malformed candidate
as a proof net. -/
def peelTerminalParChecked? (certificate : Certificate)
    (left right conclusion : Vertex) :
    Option CutFreeDerivation.CheckedCertificate := do
  let premise ← certificate.peelTerminalParCandidate? left right conclusion
  if accepted : premise.check = true then
    some ⟨premise, accepted⟩
  else
    none

/-- Two checker-accepted premises produced by a terminal splitting tensor
candidate. -/
structure CheckedTensorPremises where
  leftPremise : CutFreeDerivation.CheckedCertificate
  rightPremise : CutFreeDerivation.CheckedCertificate

/-- Executable candidate for the inverse tensor rule. Reachability is computed
in the full occurrence graph after deleting the terminal tensor conclusion.
The candidate is returned only when the two vertex sets cover every remaining
link without crossings. Mathematical completeness of this criterion is a
separate splitting theorem. -/
def splitTerminalTensorCandidate? (certificate : Certificate)
    (left right conclusion : Vertex) : Option (Certificate × Certificate) := do
  let terminalLink := Link.tensor left right conclusion
  if !certificate.links.contains terminalLink then none
  if !certificate.conclusions.contains conclusion then none
  let leftReachable := certificate.tensorLeftReachable left conclusion
  if leftReachable.contains right then none
  let leftVertices := certificate.tensorLeftVertices left conclusion
  let rightVertices := certificate.tensorRightVertices left conclusion
  let remainingLinks := certificate.links.erase terminalLink
  let partitioned := remainingLinks.all fun link =>
    link.vertices.all leftVertices.contains ||
      link.vertices.all rightVertices.contains
  if !partitioned then none
  let leftBoundary := certificate.tensorLeftBoundary left conclusion
  let rightBoundary := certificate.tensorRightBoundary left right conclusion
  let leftCertificate ← certificate.restrictTo? leftVertices leftBoundary
  let rightCertificate ← certificate.restrictTo? rightVertices rightBoundary
  pure (leftCertificate, rightCertificate)

theorem splitTerminalTensorCandidate?_eq_some_exists
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (splitting : certificate.SplittingTensor left right conclusion) :
    ∃ leftCertificate rightCertificate,
      certificate.splitTerminalTensorCandidate? left right conclusion =
        some (leftCertificate, rightCertificate) := by
  have reachabilityRejected :
      (certificate.tensorLeftReachable left conclusion).contains right = false := by
    simpa [tensorLeftReachable] using
      (TerminalTensor.splitting_iff_reachability_rejected structural
        splitting.1).mp splitting
  have rightUnreachable :
      right ∉ certificate.tensorLeftReachable left conclusion := by
    simpa using reachabilityRejected
  have partitioned :
      (certificate.links.erase (.tensor left right conclusion)).all fun link =>
        link.vertices.all
            (certificate.tensorLeftVertices left conclusion).contains ||
          link.vertices.all
            (certificate.tensorRightVertices left conclusion).contains :=
    TerminalTensor.remainingLinks_partitioned structural splitting
  rcases certificate.restrictTo?_eq_some_exists
      (certificate.tensorLeftVertices left conclusion)
      (certificate.tensorLeftBoundary left conclusion)
      (TerminalTensor.tensorLeftVertices_in_bounds certificate left conclusion)
      (TerminalTensor.tensorLeftBoundary_contained structural splitting.1) with
    ⟨leftCertificate, leftEquation⟩
  rcases certificate.restrictTo?_eq_some_exists
      (certificate.tensorRightVertices left conclusion)
      (certificate.tensorRightBoundary left right conclusion)
      (TerminalTensor.tensorRightVertices_in_bounds certificate left conclusion)
      (TerminalTensor.tensorRightBoundary_contained structural splitting) with
    ⟨rightCertificate, rightEquation⟩
  exact ⟨leftCertificate, rightCertificate, by
    simp [splitTerminalTensorCandidate?, splitting.1.1, splitting.1.2,
      rightUnreachable, partitioned, leftEquation, rightEquation]⟩

/-- A mathematical splitting tensor produces two structurally well-formed
premises.  This is stronger than executable candidate totality: it establishes
all local typing, boundary, and occurrence-ownership obligations for both
components. -/
theorem splitTerminalTensorCandidate?_structural_exists
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (splitting : certificate.SplittingTensor left right conclusion) :
    ∃ leftCertificate rightCertificate,
      certificate.splitTerminalTensorCandidate? left right conclusion =
        some (leftCertificate, rightCertificate) ∧
      leftCertificate.StructurallyWellFormed ∧
      rightCertificate.StructurallyWellFormed := by
  have reachabilityRejected :
      (certificate.tensorLeftReachable left conclusion).contains right = false := by
    simpa [tensorLeftReachable] using
      (TerminalTensor.splitting_iff_reachability_rejected structural
        splitting.1).mp splitting
  have rightUnreachable :
      right ∉ certificate.tensorLeftReachable left conclusion := by
    simpa using reachabilityRejected
  have partitioned :
      (certificate.links.erase (.tensor left right conclusion)).all fun link =>
        link.vertices.all
            (certificate.tensorLeftVertices left conclusion).contains ||
          link.vertices.all
            (certificate.tensorRightVertices left conclusion).contains :=
    TerminalTensor.remainingLinks_partitioned structural splitting
  rcases certificate.restrictTo?_eq_some_exists
      (certificate.tensorLeftVertices left conclusion)
      (certificate.tensorLeftBoundary left conclusion)
      (TerminalTensor.tensorLeftVertices_in_bounds certificate left conclusion)
      (TerminalTensor.tensorLeftBoundary_contained structural splitting.1) with
    ⟨leftCertificate, leftEquation⟩
  rcases certificate.restrictTo?_eq_some_exists
      (certificate.tensorRightVertices left conclusion)
      (certificate.tensorRightBoundary left right conclusion)
      (TerminalTensor.tensorRightVertices_in_bounds certificate left conclusion)
      (TerminalTensor.tensorRightBoundary_contained structural splitting) with
    ⟨rightCertificate, rightEquation⟩
  refine ⟨leftCertificate, rightCertificate, ?_,
    TerminalTensor.restrictTo?_leftStructurallyWellFormed
      structural splitting leftEquation,
    TerminalTensor.restrictTo?_rightStructurallyWellFormed
      structural splitting rightEquation⟩
  simp [splitTerminalTensorCandidate?, splitting.1.1, splitting.1.2,
    rightUnreachable, partitioned, leftEquation, rightEquation]

theorem splitTerminalTensorCandidate?_structurallyWellFormed
    {certificate leftCertificate rightCertificate : Certificate}
    {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (splitting : certificate.SplittingTensor left right conclusion)
    (equation : certificate.splitTerminalTensorCandidate?
      left right conclusion = some (leftCertificate, rightCertificate)) :
    leftCertificate.StructurallyWellFormed ∧
      rightCertificate.StructurallyWellFormed := by
  rcases certificate.splitTerminalTensorCandidate?_structural_exists
      structural splitting with
    ⟨expectedLeft, expectedRight, expectedEquation,
      leftStructural, rightStructural⟩
  rw [expectedEquation] at equation
  cases equation
  exact ⟨leftStructural, rightStructural⟩

theorem splitTerminalTensorCandidate?_restriction_equations
    {certificate leftCertificate rightCertificate : Certificate}
    {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (splitting : certificate.SplittingTensor left right conclusion)
    (equation : certificate.splitTerminalTensorCandidate?
      left right conclusion = some (leftCertificate, rightCertificate)) :
    certificate.restrictTo?
        (certificate.tensorLeftVertices left conclusion)
        (certificate.tensorLeftBoundary left conclusion) =
          some leftCertificate ∧
      certificate.restrictTo?
        (certificate.tensorRightVertices left conclusion)
        (certificate.tensorRightBoundary left right conclusion) =
          some rightCertificate := by
  have reachabilityRejected :
      (certificate.tensorLeftReachable left conclusion).contains right = false := by
    simpa [tensorLeftReachable] using
      (TerminalTensor.splitting_iff_reachability_rejected structural
        splitting.1).mp splitting
  have rightUnreachable :
      right ∉ certificate.tensorLeftReachable left conclusion := by
    simpa using reachabilityRejected
  have partitioned :
      (certificate.links.erase (.tensor left right conclusion)).all fun link =>
        link.vertices.all
            (certificate.tensorLeftVertices left conclusion).contains ||
          link.vertices.all
            (certificate.tensorRightVertices left conclusion).contains :=
    TerminalTensor.remainingLinks_partitioned structural splitting
  cases leftEquation : certificate.restrictTo?
      (certificate.tensorLeftVertices left conclusion)
      (certificate.tensorLeftBoundary left conclusion) with
  | none =>
      simp [splitTerminalTensorCandidate?, splitting.1.1, splitting.1.2,
        rightUnreachable, partitioned, leftEquation] at equation
  | some expectedLeft =>
      cases rightEquation : certificate.restrictTo?
          (certificate.tensorRightVertices left conclusion)
          (certificate.tensorRightBoundary left right conclusion) with
      | none =>
          simp [splitTerminalTensorCandidate?, splitting.1.1, splitting.1.2,
            rightUnreachable, partitioned, leftEquation, rightEquation]
            at equation
      | some expectedRight =>
          simp [splitTerminalTensorCandidate?, splitting.1.1, splitting.1.2,
            rightUnreachable, partitioned, leftEquation, rightEquation]
            at equation
          rcases equation with ⟨leftSame, rightSame⟩
          subst leftCertificate
          subst rightCertificate
          exact ⟨rfl, rfl⟩

/-- Exact logical boundary interface for a splitting-tensor inverse step.
Each restricted premise ends in its tensor premise, and the two remaining
contexts partition the original boundary modulo explicit exchange. -/
theorem SplittingTensor.logicalBoundaryData
    {certificate leftCertificate rightCertificate : Certificate}
    {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (splitting : certificate.SplittingTensor left right conclusion)
    (equation : certificate.splitTerminalTensorCandidate?
      left right conclusion = some (leftCertificate, rightCertificate)) :
    ∃ leftContext rightContext leftFormula rightFormula inputSequent,
      leftCertificate.conclusionFormulas? =
        some (leftContext ++ [leftFormula]) ∧
      rightCertificate.conclusionFormulas? =
        some (rightContext ++ [rightFormula]) ∧
      certificate.conclusionFormulas? = some inputSequent ∧
      (Formula.tensor leftFormula rightFormula ::
        (leftContext ++ rightContext)).Perm inputSequent := by
  let fallback : Formula := .atom "" false
  have terminal := splitting.1
  have linkWellFormed := structural.2.2.2.2.1 _ terminal.1
  rcases linkWellFormed with
    ⟨_leftRightDifferent, _leftNotConclusion, _rightNotConclusion,
      leftInBounds, rightInBounds, conclusionInBounds, typing⟩
  cases leftEquation : certificate.formula? left with
  | none => simp [leftEquation] at typing
  | some leftFormula =>
      cases rightEquation : certificate.formula? right with
      | none => simp [leftEquation, rightEquation] at typing
      | some rightFormula =>
          cases conclusionEquation : certificate.formula? conclusion with
          | none =>
              simp [leftEquation, rightEquation, conclusionEquation] at typing
          | some conclusionFormula =>
              have conclusionFormulaEquation : conclusionFormula =
                  Formula.tensor leftFormula rightFormula := by
                simpa [leftEquation, rightEquation, conclusionEquation]
                  using typing
              subst conclusionFormula
              rcases certificate.splitTerminalTensorCandidate?_restriction_equations
                  structural splitting equation with
                ⟨leftRestriction, rightRestriction⟩
              let leftVertices :=
                certificate.tensorLeftVertices left conclusion
              let rightVertices :=
                certificate.tensorRightVertices left conclusion
              let otherConclusions :=
                certificate.tensorOtherConclusions conclusion
              let leftContextVertices :=
                otherConclusions.filter leftVertices.contains
              let rightContextVertices :=
                otherConclusions.filter rightVertices.contains
              let leftContext := leftContextVertices.map fun vertex =>
                certificate.formulas.getD vertex fallback
              let rightContext := rightContextVertices.map fun vertex =>
                certificate.formulas.getD vertex fallback
              let inputSequent := certificate.conclusions.map fun vertex =>
                certificate.formulas.getD vertex fallback
              have leftLabelsRaw :=
                certificate.restrictTo?_conclusionFormulas?_eq_some
                  (TerminalTensor.tensorLeftVertices_in_bounds certificate
                    left conclusion)
                  (TerminalTensor.tensorLeftBoundary_contained structural
                    terminal)
                  leftRestriction fallback
              have rightLabelsRaw :=
                certificate.restrictTo?_conclusionFormulas?_eq_some
                  (TerminalTensor.tensorRightVertices_in_bounds certificate
                    left conclusion)
                  (TerminalTensor.tensorRightBoundary_contained structural
                    splitting)
                  rightRestriction fallback
              have leftLabel : certificate.formulas.getD left fallback =
                  leftFormula := by
                simpa [formula?, leftInBounds] using leftEquation
              have rightLabel : certificate.formulas.getD right fallback =
                  rightFormula := by
                simpa [formula?, rightInBounds] using rightEquation
              have leftLabels : leftCertificate.conclusionFormulas? =
                  some (leftContext ++ [leftFormula]) := by
                simpa only [tensorLeftBoundary, tensorOtherConclusions,
                  leftVertices, otherConclusions, leftContextVertices,
                  leftContext, List.map_append, List.map_singleton,
                  leftLabel] using leftLabelsRaw
              have rightLabels : rightCertificate.conclusionFormulas? =
                  some (rightContext ++ [rightFormula]) := by
                simpa only [tensorRightBoundary, tensorOtherConclusions,
                  rightVertices, otherConclusions, rightContextVertices,
                  rightContext, List.map_append, List.map_singleton,
                  rightLabel] using rightLabelsRaw
              have inputLabels : certificate.conclusionFormulas? =
                  some inputSequent :=
                structural.conclusionFormulas?_eq_getD fallback
              have originalNodup : certificate.conclusions.Nodup :=
                nodup_of_eraseDups_length_eq structural.2.2.2.1
              have rightFilterEquation :
                  otherConclusions.filter rightVertices.contains =
                    otherConclusions.filter
                      (fun vertex => !leftVertices.contains vertex) := by
                apply List.filter_congr
                intro vertex membership
                have erasedMembership :
                    vertex ∈ certificate.conclusions.erase conclusion := by
                  exact membership
                have originalMembership : vertex ∈ certificate.conclusions :=
                  List.mem_of_mem_erase erasedMembership
                have vertexNotConclusion : vertex ≠ conclusion :=
                  (originalNodup.mem_erase_iff.mp erasedMembership).1
                have vertexInBounds :=
                  structural.2.2.1 vertex originalMembership
                by_cases leftMembership : vertex ∈ leftVertices
                · have rightNotMembership : vertex ∉ rightVertices := by
                    intro rightMembership
                    exact TerminalTensor.vertex_partition_disjoint certificate
                      left conclusion vertex leftMembership rightMembership
                  simp [leftMembership, rightNotMembership]
                · have rightMembership : vertex ∈ rightVertices := by
                    exact Or.resolve_left
                      (TerminalTensor.vertex_partition certificate left
                        conclusion vertex vertexInBounds vertexNotConclusion)
                      leftMembership
                  simp [leftMembership, rightMembership]
              have contextVertexPermutation :
                  (leftContextVertices ++ rightContextVertices).Perm
                    otherConclusions := by
                change
                  (otherConclusions.filter leftVertices.contains ++
                    otherConclusions.filter rightVertices.contains).Perm
                    otherConclusions
                rw [rightFilterEquation]
                exact List.filter_append_perm leftVertices.contains
                  otherConclusions
              have contextLabelPermutation := contextVertexPermutation.map
                fun vertex => certificate.formulas.getD vertex fallback
              have normalizedContextLabelPermutation :
                  (leftContext ++ rightContext).Perm
                    (otherConclusions.map fun vertex =>
                      certificate.formulas.getD vertex fallback) := by
                simpa only [List.map_append, leftContext, rightContext] using
                  contextLabelPermutation
              have inputVertexPermutation :=
                List.perm_cons_erase terminal.2
              have inputLabelPermutation := inputVertexPermutation.map
                fun vertex => certificate.formulas.getD vertex fallback
              have conclusionLabel :
                  certificate.formulas.getD conclusion fallback =
                    Formula.tensor leftFormula rightFormula := by
                simpa [formula?, conclusionInBounds] using conclusionEquation
              have normalizedInputLabelPermutation :
                  inputSequent.Perm
                    (Formula.tensor leftFormula rightFormula ::
                      (otherConclusions.map fun vertex =>
                        certificate.formulas.getD vertex fallback)) := by
                simpa only [inputSequent, otherConclusions,
                  tensorOtherConclusions, List.map_cons, conclusionLabel] using
                    inputLabelPermutation
              refine ⟨leftContext, rightContext, leftFormula, rightFormula,
                inputSequent, leftLabels, rightLabels, inputLabels, ?_⟩
              exact (normalizedContextLabelPermutation.cons
                (Formula.tensor leftFormula rightFormula)).trans
                  normalizedInputLabelPermutation.symm

/-- Peeling a terminal par strictly decreases the number of formula
occurrences.  This is the unary branch of the well-founded measure used by
general sequentialization. -/
theorem peelTerminalPar_formulas_size_lt
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalPar left right conclusion) :
    (certificate.peelTerminalPar left right conclusion).formulas.size <
      certificate.formulas.size := by
  have conclusionInBounds := structural.2.2.1 conclusion terminal.2
  have sizeEquation :
      (certificate.peelTerminalPar left right conclusion).formulas.size =
        certificate.formulas.size - 1 := by
    simp [peelTerminalPar, Array.eraseIdxIfInBounds, conclusionInBounds]
  rw [sizeEquation]
  exact Nat.sub_lt structural.1 (by decide)

/-- The left component of a splitting tensor omits the terminal conclusion,
so its formula-occurrence measure is strictly smaller than the input. -/
theorem splitTerminalTensorCandidate?_left_formulas_size_lt
    {certificate leftCertificate rightCertificate : Certificate}
    {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (splitting : certificate.SplittingTensor left right conclusion)
    (equation : certificate.splitTerminalTensorCandidate?
      left right conclusion = some (leftCertificate, rightCertificate)) :
    leftCertificate.formulas.size < certificate.formulas.size := by
  rcases certificate.splitTerminalTensorCandidate?_restriction_equations
      structural splitting equation with ⟨leftEquation, _⟩
  rw [certificate.restrictTo?_formulas_size leftEquation]
  change
    ((List.range certificate.formulas.size).filter fun vertex =>
      vertex != conclusion &&
        (certificate.tensorLeftReachable left conclusion).contains vertex).length <
      certificate.formulas.size
  have strict :
      ((List.range certificate.formulas.size).filter fun vertex =>
        vertex != conclusion &&
          (certificate.tensorLeftReachable left conclusion).contains vertex).length <
        (List.range certificate.formulas.size).length :=
    List.length_filter_lt_length_iff_exists.mpr ⟨conclusion,
      List.mem_range.mpr (structural.2.2.1 conclusion splitting.1.2), by simp⟩
  simpa using strict

/-- The right component of a splitting tensor also omits the terminal
conclusion and therefore strictly decreases the recursive measure. -/
theorem splitTerminalTensorCandidate?_right_formulas_size_lt
    {certificate leftCertificate rightCertificate : Certificate}
    {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (splitting : certificate.SplittingTensor left right conclusion)
    (equation : certificate.splitTerminalTensorCandidate?
      left right conclusion = some (leftCertificate, rightCertificate)) :
    rightCertificate.formulas.size < certificate.formulas.size := by
  rcases certificate.splitTerminalTensorCandidate?_restriction_equations
      structural splitting equation with ⟨_, rightEquation⟩
  rw [certificate.restrictTo?_formulas_size rightEquation]
  change
    ((List.range certificate.formulas.size).filter fun vertex =>
      vertex != conclusion &&
        !(certificate.tensorLeftReachable left conclusion).contains vertex).length <
      certificate.formulas.size
  have strict :
      ((List.range certificate.formulas.size).filter fun vertex =>
        vertex != conclusion &&
          !(certificate.tensorLeftReachable left conclusion).contains vertex).length <
        (List.range certificate.formulas.size).length :=
    List.length_filter_lt_length_iff_exists.mpr ⟨conclusion,
      List.mem_range.mpr (structural.2.2.1 conclusion splitting.1.2), by simp⟩
  simpa using strict

/-- Exact proof interface for the inverse tensor rule. Each premise switching
is the induced restriction of an input switching to one of the two components
cut apart by a mathematically splitting terminal tensor. -/
structure TerminalTensorReduction
    (input leftPremise rightPremise : Certificate)
    (left right conclusion : Vertex) : Prop where
  splitting : input.SplittingTensor left right conclusion
  leftPremiseStructural : leftPremise.StructurallyWellFormed
  rightPremiseStructural : rightPremise.StructurallyWellFormed
  leftSwitchingRestriction : ∀ premiseGraph,
    leftPremise.SwitchingGraph premiseGraph →
      ∃ inputGraph,
        input.SwitchingGraph inputGraph ∧
        premiseGraph = inputGraph.restrictTo
          (input.tensorLeftVertices left conclusion)
  rightSwitchingRestriction : ∀ premiseGraph,
    rightPremise.SwitchingGraph premiseGraph →
      ∃ inputGraph,
        input.SwitchingGraph inputGraph ∧
        premiseGraph = inputGraph.restrictTo
          (input.tensorRightVertices left conclusion)

/-- The concrete terminal-tensor split satisfies the exact induced-component
interface required by sequentialization. -/
theorem splitTerminalTensorCandidate?_reduction
    {certificate leftCertificate rightCertificate : Certificate}
    {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (splitting : certificate.SplittingTensor left right conclusion)
    (equation : certificate.splitTerminalTensorCandidate?
      left right conclusion = some (leftCertificate, rightCertificate)) :
    TerminalTensorReduction certificate leftCertificate rightCertificate
      left right conclusion := by
  rcases certificate.splitTerminalTensorCandidate?_restriction_equations
      structural splitting equation with ⟨leftEquation, rightEquation⟩
  rcases certificate.splitTerminalTensorCandidate?_structurallyWellFormed
      structural splitting equation with ⟨leftStructural, rightStructural⟩
  refine {
    splitting := splitting
    leftPremiseStructural := leftStructural
    rightPremiseStructural := rightStructural
    leftSwitchingRestriction := ?_
    rightSwitchingRestriction := ?_ }
  · intro premiseGraph premiseSwitching
    exact TerminalTensor.restrictTo?_leftSwitchingLift structural splitting
      leftEquation premiseSwitching
  · intro premiseGraph premiseSwitching
    exact TerminalTensor.restrictTo?_rightSwitchingLift structural splitting
      rightEquation premiseSwitching

namespace TerminalTensorReduction

theorem declarativelyCorrect
    {input leftPremise rightPremise : Certificate}
    {left right conclusion : Vertex}
    (reduction : TerminalTensorReduction input leftPremise rightPremise
      left right conclusion)
    (correct : input.DeclarativelyCorrect) :
    leftPremise.DeclarativelyCorrect ∧ rightPremise.DeclarativelyCorrect := by
  constructor
  · refine ⟨reduction.leftPremiseStructural, ?_⟩
    intro premiseGraph premiseSwitching
    rcases reduction.leftSwitchingRestriction premiseGraph premiseSwitching with
      ⟨inputGraph, inputSwitching, rfl⟩
    have inputTree := correct.2 inputGraph inputSwitching
    rcases inputSwitching with ⟨selected, selection, rfl⟩
    exact (TerminalTensor.graph_restrictTo_trees correct.1
      reduction.splitting selection inputTree).1
  · refine ⟨reduction.rightPremiseStructural, ?_⟩
    intro premiseGraph premiseSwitching
    rcases reduction.rightSwitchingRestriction premiseGraph premiseSwitching with
      ⟨inputGraph, inputSwitching, rfl⟩
    have inputTree := correct.2 inputGraph inputSwitching
    rcases inputSwitching with ⟨selected, selection, rfl⟩
    exact (TerminalTensor.graph_restrictTo_trees correct.1
      reduction.splitting selection inputTree).2

theorem check_of_check
    {input leftPremise rightPremise : Certificate}
    {left right conclusion : Vertex}
    (reduction : TerminalTensorReduction input leftPremise rightPremise
      left right conclusion)
    (accepted : input.check = true) :
    leftPremise.check = true ∧ rightPremise.check = true := by
  rcases reduction.declarativelyCorrect
      (input.check_iff_declarativelyCorrect.mp accepted) with
    ⟨leftCorrect, rightCorrect⟩
  exact ⟨leftPremise.check_iff_declarativelyCorrect.mpr leftCorrect,
    rightPremise.check_iff_declarativelyCorrect.mpr rightCorrect⟩

end TerminalTensorReduction

theorem splitTerminalTensorCandidate?_check_of_check
    {certificate leftCertificate rightCertificate : Certificate}
    {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (splitting : certificate.SplittingTensor left right conclusion)
    (equation : certificate.splitTerminalTensorCandidate?
      left right conclusion = some (leftCertificate, rightCertificate))
    (accepted : certificate.check = true) :
    leftCertificate.check = true ∧ rightCertificate.check = true :=
  (certificate.splitTerminalTensorCandidate?_reduction structural splitting
    equation).check_of_check accepted

/-- Checker-gated tensor split. No recursive caller can consume a proposed
component unless both independent proof-net checks succeed. -/
def splitTerminalTensorChecked? (certificate : Certificate)
    (left right conclusion : Vertex) : Option CheckedTensorPremises := do
  let (leftCertificate, rightCertificate) ←
    certificate.splitTerminalTensorCandidate? left right conclusion
  if leftAccepted : leftCertificate.check = true then
    if rightAccepted : rightCertificate.check = true then
      some {
        leftPremise := ⟨leftCertificate, leftAccepted⟩
        rightPremise := ⟨rightCertificate, rightAccepted⟩ }
    else
      none
  else
    none

theorem splitTerminalTensorChecked?_eq_some_exists
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (splitting : certificate.SplittingTensor left right conclusion)
    (accepted : certificate.check = true) :
    ∃ premises,
      certificate.splitTerminalTensorChecked? left right conclusion =
        some premises := by
  rcases certificate.splitTerminalTensorCandidate?_eq_some_exists
      structural splitting with
    ⟨leftCertificate, rightCertificate, candidateEquation⟩
  rcases certificate.splitTerminalTensorCandidate?_check_of_check
      structural splitting candidateEquation accepted with
    ⟨leftAccepted, rightAccepted⟩
  let premises : CheckedTensorPremises := {
    leftPremise := ⟨leftCertificate, leftAccepted⟩
    rightPremise := ⟨rightCertificate, rightAccepted⟩ }
  refine ⟨premises, ?_⟩
  simp [splitTerminalTensorChecked?, candidateEquation, leftAccepted,
    rightAccepted, premises]

/-- Exact proof interface for a terminal-par inverse. It isolates the
certificate bookkeeping obligation from the already-proved graph theorem:
every premise switching must be an edge-order permutation of an original
switching with the terminal par conclusion deleted as a leaf. -/
structure TerminalParReduction (input premise : Certificate)
    (conclusion : Vertex) : Prop where
  premiseStructural : premise.StructurallyWellFormed
  switchingDeletion : ∀ premiseGraph,
    premise.SwitchingGraph premiseGraph →
      ∃ inputGraph,
        input.SwitchingGraph inputGraph ∧
        inputGraph.Leaf conclusion ∧
        premiseGraph.vertexCount =
          (inputGraph.deleteVertex conclusion).vertexCount ∧
        premiseGraph.edges.Perm
          (inputGraph.deleteVertex conclusion).edges

/-- The concrete terminal-par peel satisfies the exact graph-deletion
interface required by sequentialization. -/
theorem peelTerminalPar_reduction
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalPar left right conclusion) :
    TerminalParReduction certificate
      (certificate.peelTerminalPar left right conclusion) conclusion := by
  refine {
    premiseStructural :=
      peelTerminalPar_structurallyWellFormed structural terminal
    switchingDeletion := ?_ }
  intro premiseGraph premiseSwitching
  rcases premiseSwitching with ⟨selected, selection, rfl⟩
  have transformedSelection : ChoiceSelection
      (certificate.parChoices.filterMap
        (ParChoice.deleteVertex? conclusion)) selected := by
    rw [← peelTerminalPar_parChoices structural terminal]
    exact selection
  rcases transformedSelection.liftDelete (by
      intro choice membership
      exact TerminalPar.parChoice_deletion_agreement structural terminal
        membership) with
    ⟨lifted, liftedSelection, selectedEquation⟩
  let inputGraph := certificate.graphForSelection lifted
  refine ⟨inputGraph, ⟨lifted, liftedSelection, rfl⟩,
    TerminalPar.graphForSelection_leaf structural terminal liftedSelection,
    ?_, ?_⟩
  · change
      (certificate.peelTerminalPar left right conclusion).formulas.size =
        certificate.formulas.size - 1
    have conclusionInBounds := structural.2.2.1 conclusion terminal.2
    simp [peelTerminalPar, Array.eraseIdxIfInBounds, conclusionInBounds]
  · change
      ((certificate.peelTerminalPar left right conclusion).fixedEdges ++
        selected).Perm
      ((certificate.fixedEdges ++ lifted).filterMap
        (Edge.deleteVertex? conclusion))
    rw [peelTerminalPar_fixedEdges structural terminal, selectedEquation,
      List.filterMap_append]

namespace TerminalParReduction

theorem declarativelyCorrect {input premise : Certificate}
    {conclusion : Vertex}
    (reduction : TerminalParReduction input premise conclusion)
    (correct : input.DeclarativelyCorrect) :
    premise.DeclarativelyCorrect := by
  refine ⟨reduction.premiseStructural, ?_⟩
  intro premiseGraph premiseSwitching
  rcases reduction.switchingDeletion premiseGraph premiseSwitching with
    ⟨inputGraph, inputSwitching, leaf, vertexCount, edgePermutation⟩
  have inputTree := correct.2 inputGraph inputSwitching
  have deletedTree := inputTree.deleteLeaf leaf
  exact deletedTree.permuteEdges vertexCount.symm edgePermutation.symm

theorem check_of_check {input premise : Certificate} {conclusion : Vertex}
    (reduction : TerminalParReduction input premise conclusion)
    (accepted : input.check = true) :
    premise.check = true := by
  apply premise.check_iff_declarativelyCorrect.mpr
  exact reduction.declarativelyCorrect
    (input.check_iff_declarativelyCorrect.mp accepted)

end TerminalParReduction

theorem peelTerminalPar_check_of_check
    {certificate : Certificate} {left right conclusion : Vertex}
    (structural : certificate.StructurallyWellFormed)
    (terminal : certificate.TerminalPar left right conclusion)
    (accepted : certificate.check = true) :
    (certificate.peelTerminalPar left right conclusion).check = true :=
  (peelTerminalPar_reduction structural terminal).check_of_check accepted

theorem mem_terminalPars_iff (certificate : Certificate)
    (left right conclusion : Vertex) :
    (left, right, conclusion) ∈ certificate.terminalPars ↔
      certificate.TerminalPar left right conclusion := by
  constructor
  · intro membership
    simp only [terminalPars, List.mem_filterMap] at membership
    rcases membership with ⟨link, linkMembership, emitted⟩
    cases link with
    | «axiom» first second => simp at emitted
    | tensor first second result => simp at emitted
    | par first second result =>
        by_cases boundary : result ∈ certificate.conclusions
        · simp [boundary] at emitted
          rcases emitted with ⟨rfl, rfl, rfl⟩
          exact ⟨linkMembership, boundary⟩
        · simp [boundary] at emitted
  · rintro ⟨linkMembership, boundary⟩
    simp only [terminalPars, List.mem_filterMap]
    exact ⟨.par left right conclusion, linkMembership, by simp [boundary]⟩

theorem mem_terminalTensors_iff (certificate : Certificate)
    (left right conclusion : Vertex) :
    (left, right, conclusion) ∈ certificate.terminalTensors ↔
      certificate.TerminalTensor left right conclusion := by
  constructor
  · intro membership
    simp only [terminalTensors, List.mem_filterMap] at membership
    rcases membership with ⟨link, linkMembership, emitted⟩
    cases link with
    | «axiom» first second => simp at emitted
    | par first second result => simp at emitted
    | tensor first second result =>
        by_cases boundary : result ∈ certificate.conclusions
        · simp [boundary] at emitted
          rcases emitted with ⟨rfl, rfl, rfl⟩
          exact ⟨linkMembership, boundary⟩
        · simp [boundary] at emitted
  · rintro ⟨linkMembership, boundary⟩
    simp only [terminalTensors, List.mem_filterMap]
    exact ⟨.tensor left right conclusion, linkMembership, by simp [boundary]⟩

/-! ### Axiom-only base case accounting

The recursive sequentializer stops only when no connective link remains.  The
following lemmas prove that a correct unit-free net at that point is not an
arbitrary matching: connectedness and exact occurrence ownership force one
single axiom over exactly two formula occurrences. -/

private theorem link_eq_axiom_of_no_connective
    {certificate : Certificate}
    (noConnective : ¬ ∃ link ∈ certificate.links,
      link.isConnective = true)
    {link : Link} (membership : link ∈ certificate.links) :
    ∃ left right, link = .axiom left right := by
  cases link with
  | «axiom» left right => exact ⟨left, right, rfl⟩
  | tensor left right conclusion =>
      exact False.elim (noConnective ⟨.tensor left right conclusion,
        membership, by simp [Link.isConnective]⟩)
  | par left right conclusion =>
      exact False.elim (noConnective ⟨.par left right conclusion,
        membership, by simp [Link.isConnective]⟩)

private theorem parChoices_eq_nil_of_no_connective
    {certificate : Certificate}
    (noConnective : ¬ ∃ link ∈ certificate.links,
      link.isConnective = true) :
    certificate.parChoices = [] := by
  unfold parChoices
  apply List.filterMap_eq_nil_iff.mpr
  intro link membership
  rcases link_eq_axiom_of_no_connective noConnective membership with
    ⟨left, right, rfl⟩
  rfl

private theorem fixedEdges_length_eq_links_length_of_no_connective
    {certificate : Certificate}
    (noConnective : ¬ ∃ link ∈ certificate.links,
      link.isConnective = true) :
    certificate.fixedEdges.length = certificate.links.length := by
  unfold fixedEdges
  let emit : Link → List Edge := fun
    | .axiom left right => [{ first := left, second := right }]
    | .tensor left right conclusion =>
        [{ first := left, second := conclusion },
         { first := right, second := conclusion }]
    | .par _ _ _ => []
  change (certificate.links.flatMap emit).length = certificate.links.length
  have allAxiom : ∀ link ∈ certificate.links,
      ∃ left right, link = .axiom left right := by
    intro link membership
    exact link_eq_axiom_of_no_connective noConnective membership
  have general : ∀ links : List Link,
      (∀ link ∈ links, ∃ left right, link = .axiom left right) →
      (links.flatMap emit).length = links.length := by
    intro links all
    induction links with
    | nil => rfl
    | cons head tail ih =>
        rcases all head (by simp) with ⟨left, right, rfl⟩
        have tailAll : ∀ link ∈ tail,
            ∃ first second, link = .axiom first second := by
          intro link membership
          exact all link (by simp [membership])
        simpa [emit] using congrArg Nat.succ (ih tailAll)
  exact general certificate.links allAxiom

private theorem producerCount_eq_zero_of_no_connective
    {certificate : Certificate}
    (noConnective : ¬ ∃ link ∈ certificate.links,
      link.isConnective = true)
    (vertex : Vertex) : certificate.producerCount vertex = 0 := by
  unfold producerCount
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro link membership
  rcases link_eq_axiom_of_no_connective noConnective membership with
    ⟨left, right, rfl⟩
  simp [Link.produces]

private theorem formula_is_atom_of_no_connective
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    (noConnective : ¬ ∃ link ∈ certificate.links,
      link.isConnective = true)
    {vertex : Vertex} (inBounds : vertex < certificate.formulas.size) :
    ∃ name positive,
      certificate.formula? vertex = some (.atom name positive) := by
  have node := structural.2.2.2.2.2 vertex inBounds
  have producerZero :=
    producerCount_eq_zero_of_no_connective noConnective vertex
  have lookup : certificate.formula? vertex =
      some certificate.formulas[vertex] := by
    simp [formula?, Array.getElem?_eq_getElem inBounds]
  unfold NodeWellFormed at node
  rw [lookup] at node
  cases formula : certificate.formulas[vertex] with
  | atom name positive =>
      exact ⟨name, positive, by simpa [formula] using lookup⟩
  | tensor left right =>
      simp [formula] at node
      omega
  | par left right =>
      simp [formula] at node
      omega

private theorem axiomVertices_count_eq_axiomCount
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    (noConnective : ¬ ∃ link ∈ certificate.links,
      link.isConnective = true)
    (vertex : Vertex) :
    (certificate.links.flatMap Link.vertices).count vertex =
      certificate.axiomCount vertex := by
  unfold axiomCount
  have allAxiom : ∀ link ∈ certificate.links,
      ∃ left right, link = .axiom left right := by
    intro link membership
    exact link_eq_axiom_of_no_connective noConnective membership
  have general : ∀ links : List Link,
      (∀ link ∈ links, certificate.LinkWellFormed link) →
      (∀ link ∈ links, ∃ left right, link = .axiom left right) →
      (links.flatMap Link.vertices).count vertex =
        (links.filter (fun link => link.containsAxiomEndpoint vertex)).length := by
    intro links linksWellFormed linksAxiom
    induction links with
    | nil => rfl
    | cons head tail ih =>
        rcases linksAxiom head (by simp) with ⟨left, right, rfl⟩
        have different : left ≠ right :=
          (linksWellFormed (.axiom left right) (by simp)).1
        have tailWellFormed : ∀ link ∈ tail,
            certificate.LinkWellFormed link := by
          intro link membership
          exact linksWellFormed link (by simp [membership])
        have tailAxiom : ∀ link ∈ tail,
            ∃ first second, link = .axiom first second := by
          intro link membership
          exact linksAxiom link (by simp [membership])
        have tailIH := ih tailWellFormed tailAxiom
        by_cases atLeft : vertex = left
        · subst vertex
          simp [Link.vertices, Link.containsAxiomEndpoint,
            Ne.symm different, tailIH]
        · by_cases atRight : vertex = right
          · subst vertex
            simp [Link.vertices, Link.containsAxiomEndpoint,
              different, atLeft, tailIH]
          · simp [Link.vertices, Link.containsAxiomEndpoint,
              atLeft, atRight, Ne.symm atLeft, Ne.symm atRight, tailIH]
  exact general certificate.links structural.2.2.2.2.1 allAxiom

private theorem axiomVertices_perm_range
    {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    (noConnective : ¬ ∃ link ∈ certificate.links,
      link.isConnective = true) :
    (certificate.links.flatMap Link.vertices).Perm
      (List.range certificate.formulas.size) := by
  rw [List.perm_iff_count]
  intro vertex
  rw [axiomVertices_count_eq_axiomCount structural noConnective]
  by_cases inBounds : vertex < certificate.formulas.size
  · rcases formula_is_atom_of_no_connective structural noConnective inBounds with
      ⟨name, positive, formulaEquation⟩
    have node := structural.2.2.2.2.2 vertex inBounds
    have axiomOne : certificate.axiomCount vertex = 1 := by
      simpa [NodeWellFormed, formulaEquation] using node.1
    simp [axiomOne, inBounds]
  · have axiomZero : certificate.axiomCount vertex = 0 := by
      unfold axiomCount
      rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
      intro link membership
      rcases link_eq_axiom_of_no_connective noConnective membership with
        ⟨left, right, rfl⟩
      have wellFormed := structural.2.2.2.2.1 (.axiom left right) membership
      have leftDifferent : left ≠ vertex := fun same =>
        inBounds (same ▸ wellFormed.2.1)
      have rightDifferent : right ≠ vertex := fun same =>
        inBounds (same ▸ wellFormed.2.2.1)
      simp [Link.containsAxiomEndpoint, leftDifferent, rightDifferent]
    simp [axiomZero, inBounds]

/-- A declaratively correct certificate with no connective link has exactly
two formula occurrences and exactly one axiom link.  This is the cardinality
core of the recursive base case. -/
theorem DeclarativelyCorrect.axiomOnly_cardinality
    {certificate : Certificate}
    (correct : certificate.DeclarativelyCorrect)
    (noConnective : ¬ ∃ link ∈ certificate.links,
      link.isConnective = true) :
    certificate.formulas.size = 2 ∧ certificate.links.length = 1 := by
  have endpointPermutation :=
    axiomVertices_perm_range correct.1 noConnective
  have endpointLength :
      (certificate.links.flatMap Link.vertices).length =
        certificate.formulas.size := by
    simpa using endpointPermutation.length_eq
  have twoLinks :
      (certificate.links.flatMap Link.vertices).length =
        2 * certificate.links.length := by
    have allAxiom : ∀ link ∈ certificate.links,
        ∃ left right, link = .axiom left right := by
      intro link membership
      exact link_eq_axiom_of_no_connective noConnective membership
    have general : ∀ links : List Link,
        (∀ link ∈ links, ∃ left right,
          link = .axiom left right) →
        (links.flatMap Link.vertices).length = 2 * links.length := by
      intro links all
      induction links with
      | nil => rfl
      | cons head tail ih =>
          rcases all head (by simp) with ⟨left, right, rfl⟩
          have tailAll : ∀ link ∈ tail,
              ∃ first second, link = .axiom first second := by
            intro link membership
            exact all link (by simp [membership])
          have tailIH := ih tailAll
          simp [Link.vertices, tailIH]
          omega
    exact general certificate.links allAxiom
  have parChoicesNil :=
    parChoices_eq_nil_of_no_connective noConnective
  have selection : ChoiceSelection certificate.parChoices [] := by
    rw [parChoicesNil]
    exact .nil
  have tree := correct.2 (certificate.graphForSelection [])
    ⟨[], selection, rfl⟩
  have edgeLength : certificate.links.length + 1 =
      certificate.formulas.size := by
    have treeCount := tree.2.2
    change (certificate.fixedEdges ++ []).length + 1 =
      certificate.formulas.size at treeCount
    simpa [fixedEdges_length_eq_links_length_of_no_connective noConnective]
      using treeCount
  constructor <;> omega

private theorem parentUseCount_eq_zero_of_no_connective
    {certificate : Certificate}
    (noConnective : ¬ ∃ link ∈ certificate.links,
      link.isConnective = true)
    (vertex : Vertex) : certificate.parentUseCount vertex = 0 := by
  unfold parentUseCount
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro link membership
  rcases link_eq_axiom_of_no_connective noConnective membership with
    ⟨left, right, rfl⟩
  simp [Link.usesAsPremise, Link.premises]

/-- In the axiom-only base case every occurrence is a public conclusion.
Together with boundary uniqueness this says that the stored boundary is a
permutation of the complete vertex range. -/
theorem DeclarativelyCorrect.axiomOnly_conclusions_perm
    {certificate : Certificate}
    (correct : certificate.DeclarativelyCorrect)
    (noConnective : ¬ ∃ link ∈ certificate.links,
      link.isConnective = true) :
    certificate.conclusions.Perm
      (List.range certificate.formulas.size) := by
  have conclusionsNodup : certificate.conclusions.Nodup :=
    nodup_of_eraseDups_length_eq correct.1.2.2.2.1
  apply VertexRenaming.perm_range_of_nodup_complete
    certificate.formulas.size certificate.conclusions conclusionsNodup
  intro vertex
  constructor
  · intro inBounds
    have node := correct.1.2.2.2.2.2 vertex inBounds
    have parentZero :=
      parentUseCount_eq_zero_of_no_connective noConnective vertex
    by_cases boundary : vertex ∈ certificate.conclusions
    · exact boundary
    · have parentOne : certificate.parentUseCount vertex = 1 := by
        simpa [boundary] using node.2
      omega
  · intro membership
    exact correct.1.2.2.1 vertex membership

/-- Complete data needed by the axiom branch of recursive
sequentialization: a unique stored axiom, its dual endpoint labels, its two
possible bounded orientations, and the complete ordered boundary. -/
theorem DeclarativelyCorrect.axiomOnly_data
    {certificate : Certificate}
    (correct : certificate.DeclarativelyCorrect)
    (noConnective : ¬ ∃ link ∈ certificate.links,
      link.isConnective = true) :
    ∃ left right name positive,
      certificate.links = [.axiom left right] ∧
      certificate.formula? left = some (.atom name positive) ∧
      certificate.formula? right = some (.atom name (!positive)) ∧
      ((left = 0 ∧ right = 1) ∨ (left = 1 ∧ right = 0)) ∧
      certificate.conclusions.Perm [0, 1] := by
  rcases correct.axiomOnly_cardinality noConnective with
    ⟨formulaSize, linkLength⟩
  rcases List.length_eq_one_iff.mp linkLength with ⟨link, linksEquation⟩
  have linkMembership : link ∈ certificate.links := by
    rw [linksEquation]
    simp
  rcases link_eq_axiom_of_no_connective noConnective linkMembership with
    ⟨left, right, rfl⟩
  have wellFormed := correct.1.2.2.2.2.1
    (.axiom left right) linkMembership
  rcases wellFormed with
    ⟨different, leftInBounds, rightInBounds, typing⟩
  have orientation :
      (left = 0 ∧ right = 1) ∨ (left = 1 ∧ right = 0) := by
    rw [formulaSize] at leftInBounds rightInBounds
    have leftCases : left = 0 ∨ left = 1 :=
      Nat.le_one_iff_eq_zero_or_eq_one.mp
        (Nat.lt_succ_iff.mp leftInBounds)
    have rightCases : right = 0 ∨ right = 1 :=
      Nat.le_one_iff_eq_zero_or_eq_one.mp
        (Nat.lt_succ_iff.mp rightInBounds)
    rcases leftCases with rfl | rfl <;>
    rcases rightCases with rfl | rfl <;> simp_all
  cases leftEquation : certificate.formula? left with
  | none => simp [leftEquation] at typing
  | some leftFormula =>
      cases leftFormula with
      | tensor first second => simp [leftEquation] at typing
      | par first second => simp [leftEquation] at typing
      | atom name positive =>
          cases rightEquation : certificate.formula? right with
          | none => simp [leftEquation, rightEquation] at typing
          | some rightFormula =>
              simp [leftEquation, rightEquation] at typing
              subst rightFormula
              refine ⟨left, right, name, positive, linksEquation,
                leftEquation, ?_, orientation, ?_⟩
              · simpa [Formula.dual] using rightEquation
              · have boundaryPermutation :=
                  correct.axiomOnly_conclusions_perm noConnective
                rw [formulaSize] at boundaryPermutation
                have rangeTwo : List.range 2 = [0, 1] := by decide
                rwa [rangeTwo] at boundaryPermutation

private theorem perm_zero_one_cases {values : List Vertex}
    (permutation : values.Perm [0, 1]) :
    values = [0, 1] ∨ values = [1, 0] := by
  have lengthEquation : values.length = 2 := by
    simpa using permutation.length_eq
  have nodup : values.Nodup :=
    permutation.nodup_iff.mpr (by decide)
  cases values with
  | nil => simp at lengthEquation
  | cons first tail =>
      cases tail with
      | nil => simp at lengthEquation
      | cons second rest =>
          cases rest with
          | cons third more => simp at lengthEquation
          | nil =>
              have firstMembership : first = 0 ∨ first = 1 := by
                have : first ∈ [0, 1] :=
                  permutation.mem_iff.mp (by simp)
                simpa using this
              have secondMembership : second = 0 ∨ second = 1 := by
                have : second ∈ [0, 1] :=
                  permutation.mem_iff.mp (by simp)
                simpa using this
              rcases firstMembership with rfl | rfl <;>
              rcases secondMembership with rfl | rfl <;> simp_all

private theorem array_eq_pair
    {values : Array α} {first second : α}
    (sizeEquation : values.size = 2)
    (firstEquation : values[0]? = some first)
    (secondEquation : values[1]? = some second) :
    values = #[first, second] := by
  apply Array.ext
  · simpa using sizeEquation
  · intro index leftInBounds rightInBounds
    rw [sizeEquation] at leftInBounds
    have indexCases : index = 0 ∨ index = 1 :=
      Nat.le_one_iff_eq_zero_or_eq_one.mp
        (Nat.lt_succ_iff.mp leftInBounds)
    rcases indexCases with rfl | rfl
    · have firstValue : values[0] = first := by
        rw [Array.getElem?_eq_getElem (by simpa [sizeEquation] using leftInBounds)]
          at firstEquation
        exact Option.some.inj firstEquation
      simpa [firstValue]
    · have secondValue : values[1] = second := by
        rw [Array.getElem?_eq_getElem (by simpa [sizeEquation] using leftInBounds)]
          at secondEquation
        exact Option.some.inj secondEquation
      simpa [secondValue]

/-- Literal classification of the axiom-only base certificate.  The four
cases are exactly axiom orientation times ordered-boundary orientation; no
other checker-accepted base representation exists. -/
theorem DeclarativelyCorrect.axiomOnly_certificate_cases
    {certificate : Certificate}
    (correct : certificate.DeclarativelyCorrect)
    (noConnective : ¬ ∃ link ∈ certificate.links,
      link.isConnective = true) :
    ∃ name positive,
      certificate = {
        formulas := #[.atom name positive, .atom name (!positive)]
        links := [.axiom 0 1]
        conclusions := [0, 1] } ∨
      certificate = {
        formulas := #[.atom name positive, .atom name (!positive)]
        links := [.axiom 0 1]
        conclusions := [1, 0] } ∨
      certificate = {
        formulas := #[.atom name (!positive), .atom name positive]
        links := [.axiom 1 0]
        conclusions := [0, 1] } ∨
      certificate = {
        formulas := #[.atom name (!positive), .atom name positive]
        links := [.axiom 1 0]
        conclusions := [1, 0] } := by
  rcases correct.axiomOnly_cardinality noConnective with
    ⟨formulaSize, _⟩
  rcases correct.axiomOnly_data noConnective with
    ⟨left, right, name, positive, linksEquation,
      leftFormula, rightFormula, orientation, boundaryPermutation⟩
  have boundaryCases := perm_zero_one_cases boundaryPermutation
  rcases orientation with orientation | orientation
  · rcases orientation with ⟨rfl, rfl⟩
    have formulasEquation : certificate.formulas =
        #[.atom name positive, .atom name (!positive)] := by
      apply array_eq_pair formulaSize
      · simpa [Certificate.formula?] using leftFormula
      · simpa [Certificate.formula?] using rightFormula
    refine ⟨name, positive, ?_⟩
    rcases boundaryCases with boundary | boundary
    · left
      apply Certificate.ext_fields formulasEquation linksEquation boundary
    · right; left
      apply Certificate.ext_fields formulasEquation linksEquation boundary
  · rcases orientation with ⟨rfl, rfl⟩
    have formulasEquation : certificate.formulas =
        #[.atom name (!positive), .atom name positive] := by
      apply array_eq_pair formulaSize
      · simpa [Certificate.formula?] using rightFormula
      · simpa [Certificate.formula?] using leftFormula
    refine ⟨name, positive, ?_⟩
    rcases boundaryCases with boundary | boundary
    · right; right; left
      apply Certificate.ext_fields formulasEquation linksEquation boundary
    · right; right; right
      apply Certificate.ext_fields formulasEquation linksEquation boundary

private def swapZeroOne : VertexRenaming 2 :=
  VertexRenaming.swap 2 0 1 (by decide) (by decide)

private theorem axiomCertificate_reindex_swap
    (name : String) (positive : Bool) (boundary : List Vertex) :
    ({ formulas := #[.atom name positive, .atom name (!positive)]
       links := [.axiom 0 1]
       conclusions := boundary } : Certificate).reindex swapZeroOne =
    { formulas := #[.atom name (!positive), .atom name positive]
      links := [.axiom 1 0]
      conclusions := boundary.map swapZeroOne.forward } := by
  apply Certificate.ext_fields
  · apply Array.ext
    · simp
    · intro index leftInBounds rightInBounds
      have indexCases : index = 0 ∨ index = 1 :=
        Nat.le_one_iff_eq_zero_or_eq_one.mp
          (Nat.lt_succ_iff.mp (by simpa using leftInBounds))
      rcases indexCases with rfl | rfl <;>
        simp [Certificate.reindex, swapZeroOne, VertexRenaming.swap]
  · simp [Certificate.reindex, Link.reindex, swapZeroOne,
      VertexRenaming.swap]
  · rfl

private theorem axiomSwap_infer (name : String) (positive : Bool) :
    (CutFreeDerivation.exchange [1, 0]
      (.axiom name positive)).infer? =
    some [.atom name (!positive), .atom name positive] := by
  let atom : Formula := .atom name positive
  let dual : Formula := .atom name (!positive)
  have candidate :
      CutFreeDerivation.reorderCandidate? [atom, dual] [1, 0] =
        some [dual, atom] := by
    rfl
  have permutation : [atom, dual].Perm [dual, atom] := .swap _ _ []
  change CutFreeDerivation.reorder? [atom, dual] [1, 0] =
    some [dual, atom]
  unfold CutFreeDerivation.reorder?
  rw [candidate]
  simp [permutation]

private theorem axiomSwap_build (name : String) (positive : Bool) :
    (CutFreeDerivation.exchange [1, 0]
      (.axiom name positive)).build? =
    some {
      formulas := #[.atom name positive, .atom name (!positive)]
      links := [.axiom 0 1]
      conclusions := [.atom name (!positive), .atom name positive]
      roots := [1, 0] } := by
  let atom : Formula := .atom name positive
  let dual : Formula := .atom name (!positive)
  have candidate :
      CutFreeDerivation.reorderCandidate?
        [(atom, 0), (dual, 1)] [1, 0] =
      some [(dual, 1), (atom, 0)] := by
    rfl
  have permutation :
      [(atom, 0), (dual, 1)].Perm [(dual, 1), (atom, 0)] :=
    .swap _ _ []
  simp [CutFreeDerivation.build?, NetFragment.entries,
    CutFreeDerivation.reorder?, candidate, permutation,
    NetFragment.ofEntries, atom, dual, Formula.dual]

private theorem axiomSwap_desequentialize
    (name : String) (positive : Bool) :
    (CutFreeDerivation.exchange [1, 0]
      (.axiom name positive)).desequentialize? =
    some {
      formulas := #[.atom name positive, .atom name (!positive)]
      links := [.axiom 0 1]
      conclusions := [1, 0] } := by
  rw [CutFreeDerivation.desequentialize?]
  rw [axiomSwap_build]
  rfl

/-- The terminal recursive base already satisfies the full strengthened
`SequentializationResult` contract, including a first-order rule tree and
proof-net equivalence for both axiom orientations and both boundary orders. -/
theorem DeclarativelyCorrect.axiomOnly_sequentialization
    {certificate : Certificate}
    (correct : certificate.DeclarativelyCorrect)
    (noConnective : ¬ ∃ link ∈ certificate.links,
      link.isConnective = true) :
    Nonempty (SequentializationResult certificate) := by
  rcases correct.axiomOnly_certificate_cases noConnective with
    ⟨name, positive, shape⟩
  let atom : Formula := .atom name positive
  let dual : Formula := .atom name (!positive)
  rcases shape with shape | shape | shape | shape
  · subst certificate
    exact ⟨{
      tree := .axiom name positive
      sequent := [atom, dual]
      output := {
        formulas := #[atom, dual]
        links := [.axiom 0 1]
        conclusions := [0, 1] }
      inferred := by rfl
      desequentialized := by rfl
      outputLabels := by rfl
      equivalent := .refl _ }⟩
  · subst certificate
    exact ⟨{
      tree := .exchange [1, 0] (.axiom name positive)
      sequent := [dual, atom]
      output := {
        formulas := #[atom, dual]
        links := [.axiom 0 1]
        conclusions := [1, 0] }
      inferred := by simpa [atom, dual] using axiomSwap_infer name positive
      desequentialized := by
        simpa [atom, dual] using axiomSwap_desequentialize name positive
      outputLabels := by rfl
      equivalent := .refl _ }⟩
  · subst certificate
    exact ⟨{
      tree := .exchange [1, 0] (.axiom name positive)
      sequent := [dual, atom]
      output := {
        formulas := #[atom, dual]
        links := [.axiom 0 1]
        conclusions := [1, 0] }
      inferred := by simpa [atom, dual] using axiomSwap_infer name positive
      desequentialized := by
        simpa [atom, dual] using axiomSwap_desequentialize name positive
      outputLabels := by rfl
      equivalent := by
        apply Certificate.ReindexEquivalent.toProofNetEquivalent
        refine ⟨swapZeroOne, ?_⟩
        simpa [atom, dual, swapZeroOne, VertexRenaming.swap] using
          (axiomCertificate_reindex_swap name positive [1, 0]).symm }⟩
  · subst certificate
    exact ⟨{
      tree := .axiom name positive
      sequent := [atom, dual]
      output := {
        formulas := #[atom, dual]
        links := [.axiom 0 1]
        conclusions := [0, 1] }
      inferred := by rfl
      desequentialized := by rfl
      outputLabels := by rfl
      equivalent := by
        apply Certificate.ReindexEquivalent.toProofNetEquivalent
        refine ⟨swapZeroOne, ?_⟩
        simpa [atom, dual, swapZeroOne, VertexRenaming.swap] using
          (axiomCertificate_reindex_swap name positive [0, 1]).symm }⟩

/-- Logical sequentialization for every checker-accepted unit-free cut-free
MLL certificate.  Recursion follows the mathematical terminal-rule
dichotomy, and termination is justified by the strictly smaller occurrence
arrays of the peeled/split premises. -/
theorem logicalSequentialization_of_check
    (certificate : Certificate) (accepted : certificate.check = true) :
    Nonempty (LogicalSequentializationResult certificate) := by
  have correct : certificate.DeclarativelyCorrect :=
    certificate.check_iff_declarativelyCorrect.mp accepted
  have structural : certificate.StructurallyWellFormed := correct.1
  by_cases connectiveExists : ∃ link ∈ certificate.links,
      link.isConnective = true
  · rcases correct.terminalPar_or_splittingTensor_exists connectiveExists with
      ⟨left, right, conclusion, terminalPar | splittingTensor⟩
    · let premise := certificate.peelTerminalPar left right conclusion
      have premiseAccepted : premise.check = true := by
        exact certificate.peelTerminalPar_check_of_check structural terminalPar
          accepted
      rcases logicalSequentialization_of_check premise premiseAccepted with
        ⟨premiseResult⟩
      rcases terminalPar.logicalBoundaryData structural with
        ⟨context, leftFormula, rightFormula, inputSequent, premiseLabels,
          inputLabels, rebuiltBoundary⟩
      have premiseSequent : premiseResult.sequent =
          context ++ [leftFormula, rightFormula] := by
        exact Option.some.inj
          (premiseResult.inputLabels.symm.trans premiseLabels)
      exact ⟨LogicalSequentializationResult.parRule premiseResult context
        leftFormula rightFormula premiseSequent inputSequent inputLabels
        rebuiltBoundary⟩
    · rcases certificate.splitTerminalTensorCandidate?_eq_some_exists
          structural splittingTensor with
        ⟨leftPremise, rightPremise, splitEquation⟩
      rcases certificate.splitTerminalTensorCandidate?_check_of_check
          structural splittingTensor splitEquation accepted with
        ⟨leftAccepted, rightAccepted⟩
      rcases logicalSequentialization_of_check leftPremise leftAccepted with
        ⟨leftResult⟩
      rcases logicalSequentialization_of_check rightPremise rightAccepted with
        ⟨rightResult⟩
      rcases splittingTensor.logicalBoundaryData structural splitEquation with
        ⟨leftContext, rightContext, leftFormula, rightFormula, inputSequent,
          leftLabels, rightLabels, inputLabels, rebuiltBoundary⟩
      have leftSequent : leftResult.sequent =
          leftContext ++ [leftFormula] := by
        exact Option.some.inj (leftResult.inputLabels.symm.trans leftLabels)
      have rightSequent : rightResult.sequent =
          rightContext ++ [rightFormula] := by
        exact Option.some.inj (rightResult.inputLabels.symm.trans rightLabels)
      exact ⟨LogicalSequentializationResult.tensorRule leftResult rightResult
        leftContext rightContext leftFormula rightFormula leftSequent
        rightSequent inputSequent inputLabels rebuiltBoundary⟩
  · rcases correct.axiomOnly_sequentialization connectiveExists with
      ⟨result⟩
    exact ⟨LogicalSequentializationResult.ofSequentialization result⟩
termination_by certificate.formulas.size
decreasing_by
  · exact certificate.peelTerminalPar_formulas_size_lt structural terminalPar
  · exact certificate.splitTerminalTensorCandidate?_left_formulas_size_lt
      structural splittingTensor splitEquation
  · exact certificate.splitTerminalTensorCandidate?_right_formulas_size_lt
      structural splittingTensor splitEquation

/-- The public proposition-level logical theorem, separated from the stronger
proof-net reconstruction theorem `GenerallySequentializable`. -/
theorem logicallySequentializable : LogicallySequentializable := by
  intro certificate accepted
  exact certificate.logicalSequentialization_of_check accepted

end Certificate

end ProofNetIR
