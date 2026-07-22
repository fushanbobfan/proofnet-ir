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

namespace Certificate

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
  | edge :: edges, keep :: mask =>
      if keep then edge :: retainByMask edges mask
      else retainByMask edges mask
  | _, _ => []

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
  | «axiom» prior ih => simp [linkFullEdges, retainByMask, ih]
  | tensor prior ih => simp [linkFullEdges, retainByMask, ih]
  | parLeft prior ih => simp [linkFullEdges, retainByMask, ih]
  | parRight prior ih => simp [linkFullEdges, retainByMask, ih]

end FullSwitchingSelection

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
  certificate.links.flatMap fun
    | .axiom _ _ => [none]
    | .tensor _ _ _ => [none, none]
    | .par _ _ conclusion => [some conclusion, some conclusion]

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
  simp only [fullEdgeAnnotations, fullEdgeParTargets]
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

@[simp] theorem fullEdgeParTargets_length (certificate : Certificate) :
    certificate.fullEdgeParTargets.length = certificate.fullEdges.length := by
  rcases certificate with ⟨formulas, links, conclusions⟩
  simp only [fullEdgeParTargets, fullEdges]
  induction links with
  | nil => simp
  | cons link rest ih =>
      cases link <;> simp [ih]

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

/-- A simple closed traversal is cusp-free when neither an internal adjacent
pair nor the last/first closing pair forms a cusp. -/
def CuspFreeCycle (certificate : Certificate)
    (cycle : certificate.fullGraph.EdgeSimpleCycle) : Prop :=
  certificate.CuspFreeTraversal cycle.traversed ∧
    match cycle.traversed with
    | [] => False
    | first :: rest =>
        ¬certificate.Cusp ((first :: rest).getLast (by simp)) first

/-- Proposition-level colored acyclicity used by the splitting theorem: there
is no nonempty simple cycle whose every local transition avoids a cusp. -/
def CuspAcyclic (certificate : Certificate) : Prop :=
  ∀ cycle : certificate.fullGraph.EdgeSimpleCycle,
    ¬certificate.CuspFreeCycle cycle

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

end Certificate

end ProofNetIR
