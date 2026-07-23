import ProofNetIR.LocalIdentity

namespace ProofNetIR

/-- Structured failure returned by the executable proof-net sequentializer.
The stage is stable enough for callers to classify failures; the message is
intended for humans. -/
structure SequentializationError where
  stage : String
  message : String
  formulaCount : Nat
  linkCount : Nat
  deriving Repr, DecidableEq, BEq

namespace SequentializationError

def render (error : SequentializationError) : String :=
  s!"{error.stage}: {error.message} " ++
    s!"(formulas={error.formulaCount}, links={error.linkCount})"

end SequentializationError

/-- Runtime result for an accepted certificate.  Unlike the proposition-level
`SequentializationResult`, this value is produced by an executable search and
can be inspected by downstream programs.  It already carries the exact input
boundary, independent inference, desequentialization, output-check, and exact
proof-net-equivalence facts. -/
structure ExecutableSequentializationResult (input : Certificate) where
  tree : CutFreeDerivation
  sequent : List Formula
  output : Certificate
  inferred : tree.infer? = some sequent
  inputLabels : input.conclusionFormulas? = some sequent
  desequentialized : tree.desequentialize? = some output
  outputAccepted : output.check = true
  equivalent : output.ProofNetEquivalent input

namespace ExecutableSequentializationResult

/-- Every successful executable result contains a kernel-typed derivation of
the exact ordered input boundary. -/
theorem kernelDerivation {input : Certificate}
    (result : ExecutableSequentializationResult input) :
    Nonempty (Derivation result.sequent) :=
  result.tree.infer?_sound result.inferred

/-- Project the proof that the reconstructed output differs from the input only
by the documented proof-net equivalence. -/
theorem proofNetEquivalent {input : Certificate}
    (result : ExecutableSequentializationResult input) :
    result.output.ProofNetEquivalent input :=
  result.equivalent

/-- Forget only the runtime error channel while retaining the complete
proposition-level sequentialization contract.  Recursive totality proofs use
this bridge to reuse the graph reconstruction theorems. -/
def toSequentializationResult {input : Certificate}
    (result : ExecutableSequentializationResult input) :
    SequentializationResult input where
  tree := result.tree
  sequent := result.sequent
  output := result.output
  inferred := result.inferred
  desequentialized := result.desequentialized
  outputLabels := by
    rw [result.equivalent.conclusionFormulas?_eq]
    exact result.inputLabels
  equivalent := result.equivalent

end ExecutableSequentializationResult

namespace Certificate

private theorem nodup_map_of_injective {α β : Type} (function : α → β)
    (injective : Function.Injective function) (values : List α)
    (nodup : values.Nodup) : (values.map function).Nodup := by
  induction values with
  | nil => simp
  | cons head tail ih =>
      have parts := List.nodup_cons.mp nodup
      rw [List.map_cons, List.nodup_cons]
      constructor
      · intro membership
        rcases List.mem_map.mp membership with
          ⟨original, originalMembership, same⟩
        have : original = head := injective same
        subst original
        exact parts.1 originalMembership
      · exact ih parts.2

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

/-- A bounded bijection permutes the complete finite vertex range even when
written in inverse-image order. -/
private theorem vertexRenaming_inverse_range_perm {bound : Nat}
    (vertexMap : VertexRenaming bound) :
    (List.range bound).map vertexMap.inverse |>.Perm (List.range bound) := by
  apply VertexRenaming.perm_range_of_nodup_complete
  · exact nodup_map_of_injective vertexMap.inverse
      vertexMap.symm.forward_injective (List.range bound) List.nodup_range
  · intro vertex
    constructor
    · intro inBounds
      apply List.mem_map.mpr
      refine ⟨vertexMap.forward vertex, ?_, vertexMap.inverse_forward vertex⟩
      simp [(vertexMap.forward_lt_iff vertex).mpr inBounds]
    · intro membership
      rcases List.mem_map.mp membership with
        ⟨image, imageInRange, same⟩
      have imageInBounds : image < bound := by simpa using imageInRange
      rw [← same]
      exact (vertexMap.inverse_lt_iff image).mpr imageInBounds

/-- Reading the source formula array in inverse-image order returns exactly
the reindexed formula array. -/
theorem reindexFormulaOrder_lookup (certificate : Certificate)
    (vertexMap : VertexRenaming certificate.formulas.size) :
    ((List.range certificate.formulas.size).map vertexMap.inverse).mapM
        (fun index => certificate.formulas.toList[index]?) =
      some (certificate.reindex vertexMap).formulas.toList := by
  let source := certificate.formulas.toList
  let target := (certificate.reindex vertexMap).formulas.toList
  let fallback : Formula := .atom "" false
  let value : Nat → Formula := fun index =>
    source.getD (vertexMap.inverse index) fallback
  have defined : ∀ index ∈ List.range certificate.formulas.size,
      source[vertexMap.inverse index]? = some (value index) := by
    intro index membership
    have indexInBounds : index < certificate.formulas.size := by
      simpa using membership
    have inverseInBounds : vertexMap.inverse index < source.length := by
      simpa [source] using
        (vertexMap.inverse_lt_iff index).mpr indexInBounds
    simp [value, List.getD, inverseInBounds]
  have targetEquation :
      (List.range certificate.formulas.size).map value = target := by
    apply List.ext_getElem
    · simp [target]
    · intro index leftInBounds rightInBounds
      have indexInBounds : index < certificate.formulas.size := by
        simpa using leftInBounds
      simp [value, source, target, List.getD, indexInBounds,
        Certificate.reindex]
  rw [List.mapM_map]
  rw [list_mapM_eq_some_map_of_forall
    (List.range certificate.formulas.size)
    ((fun index => certificate.formulas.toList[index]?) ∘ vertexMap.inverse)
    value]
  · simp [target, targetEquation]
  · simpa [source] using defined

private theorem ofOrder_inverseRange_forward {bound : Nat}
    (vertexMap : VertexRenaming bound)
    (order : List Vertex)
    (orderEquation : order = (List.range bound).map vertexMap.inverse)
    (lengthEquation : order.length = bound) (nodup : order.Nodup)
    (complete : ∀ vertex, vertex < bound ↔ vertex ∈ order)
    {vertex : Vertex} (inBounds : vertex < bound) :
    (VertexRenaming.ofOrder bound order lengthEquation nodup complete).forward
        vertex = vertexMap.forward vertex := by
  rw [VertexRenaming.ofOrder_forward_inBounds bound order lengthEquation nodup
    complete inBounds]
  have forwardInBounds : vertexMap.forward vertex < order.length := by
    simpa [lengthEquation] using
      (vertexMap.forward_lt_iff vertex).mpr inBounds
  have valueAtForward : order[vertexMap.forward vertex] = vertex := by
    subst order
    simp only [List.getElem_map, List.getElem_range]
    exact vertexMap.inverse_forward vertex
  have firstOccurrence := VertexRenaming.idxOf_getElem_of_nodup order nodup
    (vertexMap.forward vertex) forwardInBounds
  rw [valueAtForward] at firstOccurrence
  exact firstOccurrence

private theorem reindex_eq_of_forward_eq_on_bounds {certificate : Certificate}
    (structural : certificate.StructurallyWellFormed)
    (leftMap rightMap : VertexRenaming certificate.formulas.size)
    (forwardEquation : ∀ vertex, vertex < certificate.formulas.size →
      leftMap.forward vertex = rightMap.forward vertex) :
    certificate.reindex leftMap = certificate.reindex rightMap := by
  have inverseEquation : ∀ vertex, vertex < certificate.formulas.size →
      leftMap.inverse vertex = rightMap.inverse vertex := by
    intro vertex inBounds
    apply leftMap.forward_injective
    calc
      leftMap.forward (leftMap.inverse vertex) = vertex :=
        leftMap.forward_inverse vertex
      _ = rightMap.forward (rightMap.inverse vertex) :=
        (rightMap.forward_inverse vertex).symm
      _ = leftMap.forward (rightMap.inverse vertex) := by
        rw [forwardEquation (rightMap.inverse vertex)
          ((rightMap.inverse_lt_iff vertex).mpr inBounds)]
  apply Certificate.ext_fields
  · apply Array.ext
    · simp
    · intro index leftInBounds rightInBounds
      simp [Certificate.reindex,
        inverseEquation index (by simpa using leftInBounds)]
  · apply List.map_congr_left
    intro link membership
    have wellFormed := structural.2.2.2.2.1 link membership
    cases link with
    | «axiom» first second =>
        simp [Link.reindex,
          forwardEquation first (wellFormed.vertex_in_bounds (by simp [Link.vertices])),
          forwardEquation second (wellFormed.vertex_in_bounds (by simp [Link.vertices]))]
    | tensor first second result =>
        simp [Link.reindex,
          forwardEquation first (wellFormed.vertex_in_bounds (by simp [Link.vertices])),
          forwardEquation second (wellFormed.vertex_in_bounds (by simp [Link.vertices])),
          forwardEquation result (wellFormed.vertex_in_bounds (by simp [Link.vertices]))]
    | par first second result =>
        simp [Link.reindex,
          forwardEquation first (wellFormed.vertex_in_bounds (by simp [Link.vertices])),
          forwardEquation second (wellFormed.vertex_in_bounds (by simp [Link.vertices])),
          forwardEquation result (wellFormed.vertex_in_bounds (by simp [Link.vertices]))]
  · apply List.map_congr_left
    intro vertex membership
    exact forwardEquation vertex (structural.2.2.1 vertex membership)

private def sequentializationError (certificate : Certificate)
    (stage message : String) : SequentializationError := {
  stage
  message
  formulaCount := certificate.formulas.size
  linkCount := certificate.links.length }

private def firstSome (function : α → Option β) : List α → Option β
  | [] => none
  | head :: tail =>
      match function head with
      | some value => some value
      | none => firstSome function tail

private theorem firstSome_isSome_of_mem (function : α → Option β)
    (inputs : List α) (input : α) (membership : input ∈ inputs)
    (success : (function input).isSome = true) :
    (firstSome function inputs).isSome = true := by
  induction inputs with
  | nil => simp at membership
  | cons head tail ih =>
      simp only [List.mem_cons] at membership
      rcases membership with same | membership
      · subst head
        cases equation : function input with
        | none => simp [equation] at success
        | some value => simp [firstSome, equation]
      · cases equation : function head with
        | none => simpa [firstSome, equation] using ih membership
        | some value => simp [firstSome, equation]

private theorem firstSome_eq_some {function : α → Option β}
    {inputs : List α} {output : β}
    (equation : firstSome function inputs = some output) :
    ∃ input ∈ inputs, function input = some output := by
  induction inputs with
  | nil => simp [firstSome] at equation
  | cons head tail ih =>
      cases headEquation : function head with
      | none =>
          rcases ih (by simpa [firstSome, headEquation] using equation) with
            ⟨input, membership, success⟩
          exact ⟨input, by simp [membership], success⟩
      | some value =>
          have same : value = output := by
            simpa [firstSome, headEquation] using equation
          subst value
          exact ⟨head, by simp, headEquation⟩

/-- Backtracking kernel for `matchingFormulaOrders`.  Keeping the recursive
enumerator named makes its completeness contract available to the totality
proof instead of burying it in a local definition. -/
def matchingFormulaOrdersVisit (source : List Formula) (used : List Nat) :
    List Formula → List (List Nat)
  | [] => [[]]
  | formula :: rest =>
      (List.range source.length).filter (fun index =>
        !used.contains index && source[index]? == some formula) |>.flatMap
          fun index =>
            (matchingFormulaOrdersVisit source (index :: used) rest).map
              fun suffix => index :: suffix

/-- Enumerate every explicit occurrence permutation from `source` to `target`.
The search branches only between still-unused occurrences carrying the required
formula, rather than over all factorial permutations.  This is essential for
completeness when a boundary contains repeated formula labels. -/
def matchingFormulaOrders (source target : List Formula) : List (List Nat) :=
  if source.length != target.length then
    []
  else
    matchingFormulaOrdersVisit source [] target

/-- Completeness of the occurrence backtracker relative to an explicit fresh,
duplicate-free lookup order.  This is the finite-search lemma needed to connect
an extensional vertex bijection to the executable equivalence witness. -/
theorem matchingFormulaOrdersVisit_complete (source target : List Formula)
    (used order : List Nat)
    (fresh : ∀ index ∈ order, index ∉ used)
    (nodup : order.Nodup)
    (lookup : order.mapM (fun index => source[index]?) = some target) :
    order ∈ matchingFormulaOrdersVisit source used target := by
  induction target generalizing used order with
  | nil =>
      cases order with
      | nil => simp [matchingFormulaOrdersVisit]
      | cons index suffix =>
          cases headLookup : source[index]? with
          | none => simp [headLookup] at lookup
          | some value =>
              cases tailLookup :
                  suffix.mapM (fun position => source[position]?) with
              | none => simp [headLookup, tailLookup] at lookup
              | some values => simp [headLookup, tailLookup] at lookup
  | cons formula rest ih =>
      cases order with
      | nil => simp at lookup
      | cons index suffix =>
          cases headLookup : source[index]? with
          | none => simp [headLookup] at lookup
          | some actual =>
              cases tailLookup : suffix.mapM (fun position => source[position]?) with
              | none => simp [headLookup, tailLookup] at lookup
              | some values =>
                  have consEquation : actual :: values = formula :: rest := by
                    simpa [headLookup, tailLookup] using lookup
                  have actualEquation : actual = formula := by
                    exact (List.cons.inj consEquation).1
                  have valuesEquation : values = rest := by
                    exact (List.cons.inj consEquation).2
                  subst actual
                  subst values
                  rcases getElem?_eq_some_iff.mp headLookup with
                    ⟨indexInBounds, indexValue⟩
                  have indexFresh : index ∉ used :=
                    fresh index (by simp)
                  have nodupParts := List.nodup_cons.mp nodup
                  have suffixFresh : ∀ candidate ∈ suffix,
                      candidate ∉ index :: used := by
                    intro candidate membership
                    simp only [List.mem_cons, not_or]
                    constructor
                    · intro same
                      subst candidate
                      exact nodupParts.1 membership
                    · exact fresh candidate (by simp [membership])
                  have suffixMembership : suffix ∈
                      matchingFormulaOrdersVisit source (index :: used) rest :=
                    ih (index :: used) suffix suffixFresh nodupParts.2 tailLookup
                  simp only [matchingFormulaOrdersVisit, List.mem_flatMap]
                  refine ⟨index, ?_, ?_⟩
                  · simp [indexInBounds, indexFresh, indexValue]
                  · exact List.mem_map.mpr ⟨suffix, suffixMembership, rfl⟩

/-- Every duplicate-free full occurrence order with the requested pointwise
formula lookup appears in the optimized top-level enumeration. -/
theorem matchingFormulaOrders_complete (source target : List Formula)
    (order : List Nat)
    (sameLength : source.length = target.length)
    (permutation : order.Perm (List.range source.length))
    (lookup : order.mapM (fun index => source[index]?) = some target) :
    order ∈ matchingFormulaOrders source target := by
  have nodup : order.Nodup :=
    permutation.nodup_iff.mpr List.nodup_range
  have generated := matchingFormulaOrdersVisit_complete source target [] order
    (by simp) nodup lookup
  simpa [matchingFormulaOrders, sameLength] using generated

/-- A formula-occurrence alignment kernel with a position-sensitive admissibility
predicate.  The proof-net identity search uses this to enforce the ordered
conclusion boundary while candidates are generated, rather than after a full
duplicate-label permutation has already been materialized. -/
def matchingFormulaOrdersVisitConstrained (source : List Formula)
    (allowed : Nat → Nat → Bool) (position : Nat) (used : List Nat) :
    List Formula → List (List Nat)
  | [] => [[]]
  | formula :: rest =>
      (List.range source.length).filter (fun index =>
        !used.contains index && source[index]? == some formula &&
          allowed position index) |>.flatMap fun index =>
            (matchingFormulaOrdersVisitConstrained source allowed
              (position + 1) (index :: used) rest).map fun suffix =>
                index :: suffix

/-- Completeness of the constrained occurrence backtracker.  Every explicit
fresh alignment satisfying the pointwise admissibility predicate is generated. -/
theorem matchingFormulaOrdersVisitConstrained_complete
    (source target : List Formula) (allowed : Nat → Nat → Bool)
    (position : Nat) (used order : List Nat)
    (fresh : ∀ index ∈ order, index ∉ used)
    (nodup : order.Nodup)
    (lookup : order.mapM (fun index => source[index]?) = some target)
    (allowedOrder : ∀ offset (inBounds : offset < order.length),
      allowed (position + offset) order[offset] = true) :
    order ∈ matchingFormulaOrdersVisitConstrained source allowed position
      used target := by
  induction target generalizing position used order with
  | nil =>
      cases order with
      | nil => simp [matchingFormulaOrdersVisitConstrained]
      | cons index suffix =>
          cases headLookup : source[index]? with
          | none => simp [headLookup] at lookup
          | some value =>
              cases tailLookup :
                  suffix.mapM (fun candidate => source[candidate]?) with
              | none => simp [headLookup, tailLookup] at lookup
              | some values => simp [headLookup, tailLookup] at lookup
  | cons formula rest ih =>
      cases order with
      | nil => simp at lookup
      | cons index suffix =>
          cases headLookup : source[index]? with
          | none => simp [headLookup] at lookup
          | some actual =>
              cases tailLookup :
                  suffix.mapM (fun candidate => source[candidate]?) with
              | none => simp [headLookup, tailLookup] at lookup
              | some values =>
                  have consEquation : actual :: values = formula :: rest := by
                    simpa [headLookup, tailLookup] using lookup
                  have actualEquation : actual = formula :=
                    (List.cons.inj consEquation).1
                  have valuesEquation : values = rest :=
                    (List.cons.inj consEquation).2
                  subst actual
                  subst values
                  rcases getElem?_eq_some_iff.mp headLookup with
                    ⟨indexInBounds, indexValue⟩
                  have indexFresh : index ∉ used :=
                    fresh index (by simp)
                  have nodupParts := List.nodup_cons.mp nodup
                  have suffixFresh : ∀ candidate ∈ suffix,
                      candidate ∉ index :: used := by
                    intro candidate membership
                    simp only [List.mem_cons, not_or]
                    exact ⟨fun same => nodupParts.1 (same ▸ membership),
                      fresh candidate (by simp [membership])⟩
                  have headAllowed : allowed position index = true := by
                    have sourceAllowed := allowedOrder 0 (by simp)
                    change allowed position index = true at sourceAllowed
                    exact sourceAllowed
                  have suffixAllowed : ∀ offset
                      (inBounds : offset < suffix.length),
                      allowed (position + 1 + offset) suffix[offset] = true := by
                    intro offset inBounds
                    have sourceAllowed := allowedOrder (offset + 1) (by
                      simpa using Nat.succ_lt_succ inBounds)
                    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                      sourceAllowed
                  have suffixMembership : suffix ∈
                      matchingFormulaOrdersVisitConstrained source allowed
                        (position + 1) (index :: used) rest :=
                    ih (position + 1) (index :: used) suffix
                      suffixFresh nodupParts.2 tailLookup suffixAllowed
                  simp only [matchingFormulaOrdersVisitConstrained,
                    List.mem_flatMap]
                  refine ⟨index, ?_, ?_⟩
                  · simp [indexInBounds, indexFresh, indexValue, headAllowed]
                  · exact List.mem_map.mpr
                      ⟨suffix, suffixMembership, rfl⟩

/-- Ordered conclusion positions constrain a target vertex to the source
vertex occurring at the same boundary position.  Non-boundary targets remain
unconstrained. -/
def conclusionCompatible (left right : Certificate)
    (targetVertex sourceVertex : Vertex) : Bool :=
  (left.conclusions.zip right.conclusions).all fun pair =>
    pair.2 != targetVertex || pair.1 == sourceVertex

/-- The exact identity search combines ordered-boundary and numeric-free
one-hop incidence constraints before extending an occurrence alignment. -/
def identityCandidateCompatible (left right : Certificate)
    (targetVertex sourceVertex : Vertex) : Bool :=
  conclusionCompatible left right targetVertex sourceVertex &&
    localIdentityCompatible left right targetVertex sourceVertex

/-- Enumerate formula-compatible occurrence bijections while applying the
ordered-boundary constraints during generation. -/
def matchingFormulaOrdersForCertificates (left right : Certificate) :
    List (List Nat) :=
  if left.formulas.size != right.formulas.size then
    []
  else
    matchingFormulaOrdersVisitConstrained left.formulas.toList
      (identityCandidateCompatible left right) 0 [] right.formulas.toList

private theorem conclusionCompatibility_all_inverse
    (conclusions : List Vertex) {bound : Nat}
    (vertexMap : VertexRenaming bound) (target : Vertex) :
    (conclusions.zip (conclusions.map vertexMap.forward)).all
        (fun pair =>
          pair.2 != target || pair.1 == vertexMap.inverse target) = true := by
  induction conclusions with
  | nil => simp
  | cons head tail ih =>
      by_cases same : vertexMap.forward head = target
      · have inverseSame : head = vertexMap.inverse target := by
          rw [← same]
          exact (vertexMap.inverse_forward head).symm
        simp [inverseSame, ih]
      · simp [same, ih]

/-- The constrained certificate enumerator remains complete for every direct
proof-net equivalence witness. -/
theorem matchingFormulaOrdersForCertificates_complete
    {left right : Certificate}
    (vertexMap : VertexRenaming left.formulas.size)
    (relation : (left.reindex vertexMap).LinkPermutationEquivalent right) :
    let order := (List.range left.formulas.size).map vertexMap.inverse
    order ∈ matchingFormulaOrdersForCertificates left right := by
  let order := (List.range left.formulas.size).map vertexMap.inverse
  have sameSize : left.formulas.size = right.formulas.size := by
    rw [← left.reindex_formulas_size vertexMap, relation.formulas]
  have sameLength : left.formulas.toList.length = right.formulas.toList.length := by
    simpa using congrArg Array.size relation.formulas
  have permutation : order.Perm (List.range left.formulas.toList.length) := by
    simpa [order] using vertexRenaming_inverse_range_perm vertexMap
  have lookup : order.mapM (fun index => left.formulas.toList[index]?) =
      some right.formulas.toList := by
    have generated := reindexFormulaOrder_lookup left vertexMap
    rw [relation.formulas] at generated
    simpa [order] using generated
  have nodup : order.Nodup :=
    permutation.nodup_iff.mpr List.nodup_range
  have allowedOrder : ∀ offset (inBounds : offset < order.length),
      identityCandidateCompatible left right offset order[offset] = true := by
    intro offset inBounds
    have offsetInBounds : offset < left.formulas.size := by
      simpa [order] using inBounds
    have orderAt : order[offset] = vertexMap.inverse offset := by
      simp [order]
    rw [orderAt]
    have conclusionAllowed : conclusionCompatible left right offset
        (vertexMap.inverse offset) = true := by
      unfold conclusionCompatible
      rw [← relation.conclusions]
      simpa [Certificate.reindex_conclusions] using
        conclusionCompatibility_all_inverse left.conclusions vertexMap offset
    have localAllowed : localIdentityCompatible left right offset
        (vertexMap.inverse offset) = true :=
      localIdentityCompatible_inverse vertexMap relation offset
    simp [identityCandidateCompatible, conclusionAllowed, localAllowed]
  have generated := matchingFormulaOrdersVisitConstrained_complete
    left.formulas.toList right.formulas.toList
      (identityCandidateCompatible left right)
    0 [] order (by simp) nodup lookup (by
      intro offset inBounds
      simpa using allowedOrder offset inBounds)
  simpa [matchingFormulaOrdersForCertificates, sameSize, order] using generated

private theorem matchingFormulaOrders_complete_of_reorder?
    {source target : List Formula} {order : List Nat}
    (accepted : CutFreeDerivation.reorder? source order = some target) :
    order ∈ matchingFormulaOrders source target := by
  have permutation : source.Perm target :=
    CutFreeDerivation.reorder?_perm accepted
  have candidateEquation :
      CutFreeDerivation.reorderCandidate? source order = some target := by
    unfold CutFreeDerivation.reorder? at accepted
    cases candidateResult :
        CutFreeDerivation.reorderCandidate? source order with
    | none => simp [candidateResult] at accepted
    | some candidate =>
        by_cases candidatePermutation : source.Perm candidate
        · have same : candidate = target := by
            simpa [candidateResult, candidatePermutation] using accepted
          exact congrArg some same
        · simp [candidateResult, candidatePermutation] at accepted
  have lookup :
      order.mapM (fun index => source[index]?) = some target := by
    unfold CutFreeDerivation.reorderCandidate? at candidateEquation
    split at candidateEquation
    · exact candidateEquation
    · contradiction
  have guard :
      (order.length == source.length &&
        order.eraseDups.length == order.length &&
        order.all (fun index => index < source.length)) = true := by
    unfold CutFreeDerivation.reorderCandidate? at candidateEquation
    split at candidateEquation
    · assumption
    · contradiction
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at guard
  rcases guard with ⟨⟨_orderLength, eraseLength⟩, _bounds⟩
  have nodup : order.Nodup :=
    nodup_of_eraseDups_length_eq eraseLength
  have generated := matchingFormulaOrdersVisit_complete source target [] order
    (by simp) nodup lookup
  simpa [matchingFormulaOrders, permutation.length_eq] using generated

/-- Deterministic first matching occurrence permutation.  The executable
sequentializer itself tries the complete list until proof-net equivalence holds. -/
def matchingFormulaOrder? (source target : List Formula) : Option (List Nat) :=
  (matchingFormulaOrders source target).head?

/-- A computational witness for the flattened proof-net equivalence relation. -/
structure DirectEquivalenceWitness (left right : Certificate) where
  vertexMap : VertexRenaming left.formulas.size
  linkPermutation :
    (left.reindex vertexMap).LinkPermutationEquivalent right

namespace DirectEquivalenceWitness

theorem proofNetEquivalent {left right : Certificate}
    (witness : DirectEquivalenceWitness left right) :
    left.ProofNetEquivalent right :=
  (show left.DirectProofNetEquivalent right from
    ⟨witness.vertexMap, witness.linkPermutation⟩).toProofNetEquivalent

end DirectEquivalenceWitness

private def renamingOfOrder? (bound : Nat) (order : List Vertex) :
    Option (VertexRenaming bound) :=
  if permutation : order.Perm (List.range bound) then
    let lengthEquation : order.length = bound := by
      simpa using permutation.length_eq
    let nodup : order.Nodup :=
      permutation.nodup_iff.mpr List.nodup_range
    let complete : ∀ vertex, vertex < bound ↔ vertex ∈ order := by
      intro vertex
      rw [permutation.mem_iff]
      simp
    some (VertexRenaming.ofOrder bound order lengthEquation nodup complete)
  else
    none

private theorem renamingOfOrder?_inverseRange {bound : Nat}
    (vertexMap : VertexRenaming bound) :
    ∃ canonicalMap,
      renamingOfOrder? bound
          ((List.range bound).map vertexMap.inverse) = some canonicalMap ∧
      ∀ vertex, vertex < bound →
        canonicalMap.forward vertex = vertexMap.forward vertex := by
  let order := (List.range bound).map vertexMap.inverse
  have permutation : order.Perm (List.range bound) := by
    simpa [order] using vertexRenaming_inverse_range_perm vertexMap
  change ∃ canonicalMap,
    renamingOfOrder? bound order = some canonicalMap ∧
      ∀ vertex, vertex < bound →
        canonicalMap.forward vertex = vertexMap.forward vertex
  unfold renamingOfOrder?
  rw [dif_pos permutation]
  refine ⟨_, rfl, ?_⟩
  intro vertex inBounds
  apply ofOrder_inverseRange_forward vertexMap order
    (by simp [order])
  exact inBounds

/-- Decide the exact v0.4 proof-net identity relation by enumerating only
formula-compatible vertex bijections, then checking link multiset equality and
the ordered conclusion boundary.  Unlike `reindexEquivalent?`, this decision
is intentionally insensitive to link-list storage order. -/
def directProofNetEquivalentWitness? (left right : Certificate) :
    Option (DirectEquivalenceWitness left right) :=
  firstSome (fun order => do
    let vertexMap ← renamingOfOrder? left.formulas.size order
    let reindexed := left.reindex vertexMap
    if formulas : reindexed.formulas = right.formulas then
      if links : reindexed.links.Perm right.links then
        if conclusions : reindexed.conclusions = right.conclusions then
          some {
            vertexMap
            linkPermutation := ⟨formulas, links, conclusions⟩ }
        else
          none
      else
        none
    else
      none) (matchingFormulaOrdersForCertificates left right)

/-- The executable direct-equivalence search is complete on structurally
well-formed left certificates.  In particular, link-list reordering cannot hide
an existing bounded-renaming witness from the finite occurrence search. -/
theorem directProofNetEquivalentWitness?_complete {left right : Certificate}
    (leftStructural : left.StructurallyWellFormed)
    (equivalent : left.DirectProofNetEquivalent right) :
    (directProofNetEquivalentWitness? left right).isSome = true := by
  rcases equivalent with ⟨vertexMap, relation⟩
  let order := (List.range left.formulas.size).map vertexMap.inverse
  have orderMembership : order ∈
      matchingFormulaOrdersForCertificates left right :=
    matchingFormulaOrdersForCertificates_complete vertexMap relation
  rcases renamingOfOrder?_inverseRange vertexMap with
    ⟨canonicalMap, canonicalResult, forwardEquation⟩
  have reindexEquation : left.reindex canonicalMap = left.reindex vertexMap :=
    reindex_eq_of_forward_eq_on_bounds leftStructural canonicalMap vertexMap
      forwardEquation
  have canonicalRelation :
      (left.reindex canonicalMap).LinkPermutationEquivalent right := by
    rw [reindexEquation]
    exact relation
  unfold directProofNetEquivalentWitness?
  apply firstSome_isSome_of_mem _ _ order orderMembership
  simp [order, canonicalResult, canonicalRelation.formulas]
  split
  · split
    · rfl
    · rename_i noConclusions
      exact (noConclusions canonicalRelation.conclusions).elim
  · rename_i noLinks
    exact (noLinks canonicalRelation.links).elim

/-- Executable decision procedure for the proof-net identity used by general
sequentialization.  Completeness is stated below on structurally well-formed
left certificates, which includes every checker-accepted certificate. -/
def proofNetEquivalent? (left right : Certificate) : Bool :=
  (directProofNetEquivalentWitness? left right).isSome

/-- On the library's well-formed domain, the executable Boolean agrees exactly
with the equivalence generated by bounded vertex renaming and link-list
permutation.  It does not quotient the ordered conclusion boundary. -/
theorem proofNetEquivalent?_eq_true_iff {left right : Certificate}
    (leftStructural : left.StructurallyWellFormed) :
    proofNetEquivalent? left right = true ↔
      left.ProofNetEquivalent right := by
  constructor
  · intro accepted
    cases equation : directProofNetEquivalentWitness? left right with
    | none => simp [proofNetEquivalent?, equation] at accepted
    | some witness => exact witness.proofNetEquivalent
  · intro equivalent
    simpa [proofNetEquivalent?] using
      directProofNetEquivalentWitness?_complete leftStructural
        (proofNetEquivalent_iff_direct.mp equivalent)

private def alignTree? (input : Certificate) (tree : CutFreeDerivation)
    (target : List Formula) : Option CutFreeDerivation := do
  let source ← tree.infer?
  firstSome (fun order =>
    let aligned := CutFreeDerivation.exchange order tree
    if aligned.infer? != some target then
      none
    else
      match aligned.desequentializeChecked? with
      | some checked =>
          match directProofNetEquivalentWitness? checked.certificate input with
          | some _ => some aligned
          | none => none
      | none => none) (matchingFormulaOrders source target)

private theorem alignTree?_complete {input : Certificate}
    {tree : CutFreeDerivation} {source target : List Formula}
    {order : List Nat} {checked : CutFreeDerivation.CheckedCertificate}
    (sourceEquation : tree.infer? = some source)
    (orderMembership : order ∈ matchingFormulaOrders source target)
    (inferred : (CutFreeDerivation.exchange order tree).infer? = some target)
    (checkedEquation :
      (CutFreeDerivation.exchange order tree).desequentializeChecked? =
        some checked)
    (equivalent : checked.certificate.DirectProofNetEquivalent input) :
    (alignTree? input tree target).isSome = true := by
  have checkedStructural : checked.certificate.StructurallyWellFormed :=
    (checked.certificate.check_sound_declarative checked.accepted).1
  have equivalenceFound :=
    directProofNetEquivalentWitness?_complete checkedStructural equivalent
  unfold alignTree?
  simp only [sourceEquation]
  apply firstSome_isSome_of_mem _ _ order orderMembership
  simp [inferred, checkedEquation]
  cases equation : directProofNetEquivalentWitness? checked.certificate input with
  | none => simp [equation] at equivalenceFound
  | some witness => simp

private theorem alignTree?_sound {input : Certificate}
    {tree aligned : CutFreeDerivation} {target : List Formula}
    (labels : input.conclusionFormulas? = some target)
    (equation : alignTree? input tree target = some aligned) :
    ∃ result : ExecutableSequentializationResult input,
      result.tree = aligned := by
  unfold alignTree? at equation
  cases sourceEquation : tree.infer? with
  | none => simp [sourceEquation] at equation
  | some source =>
      simp only [sourceEquation] at equation
      rcases firstSome_eq_some equation with
        ⟨order, _orderMembership, branchEquation⟩
      let candidate := CutFreeDerivation.exchange order tree
      by_cases inferred : candidate.infer? = some target
      · cases checkedEquation : candidate.desequentializeChecked? with
        | none =>
            simp [candidate, inferred, checkedEquation] at branchEquation
        | some checked =>
            cases witnessEquation :
                directProofNetEquivalentWitness? checked.certificate input with
            | none =>
                simp [candidate, inferred, checkedEquation, witnessEquation]
                  at branchEquation
            | some witness =>
                have same : candidate = aligned := by
                  simpa [candidate, inferred, checkedEquation,
                    witnessEquation] using branchEquation
                have desequentialized :
                    candidate.desequentialize? = some checked.certificate := by
                  unfold CutFreeDerivation.desequentializeChecked?
                    at checkedEquation
                  cases outputEquation : candidate.desequentialize? with
                  | none => simp [outputEquation] at checkedEquation
                  | some output =>
                      by_cases outputAccepted : output.check = true
                      · have checkedSame :
                            CutFreeDerivation.CheckedCertificate.mk output
                              outputAccepted = checked := by
                          simpa [outputEquation, outputAccepted] using
                            checkedEquation
                        have outputSame : output = checked.certificate :=
                          congrArg (·.certificate) checkedSame
                        exact congrArg some outputSame
                      · simp [outputEquation, outputAccepted] at checkedEquation
                let result : ExecutableSequentializationResult input := {
                  tree := candidate
                  sequent := target
                  output := checked.certificate
                  inferred := inferred
                  inputLabels := labels
                  desequentialized := desequentialized
                  outputAccepted := checked.accepted
                  equivalent := witness.proofNetEquivalent }
                exact ⟨result, by simpa [result] using same⟩
      · simp [candidate, inferred] at branchEquation

private theorem alignTree?_complete_of_desequentialize
    {input output : Certificate} {tree : CutFreeDerivation}
    {source target : List Formula} {order : List Nat}
    (inputAccepted : input.check = true)
    (sourceEquation : tree.infer? = some source)
    (orderMembership : order ∈ matchingFormulaOrders source target)
    (inferred : (CutFreeDerivation.exchange order tree).infer? = some target)
    (desequentialized :
      (CutFreeDerivation.exchange order tree).desequentialize? = some output)
    (equivalent : output.DirectProofNetEquivalent input) :
    (alignTree? input tree target).isSome = true := by
  have outputAccepted : output.check = true := by
    rw [equivalent.toProofNetEquivalent.check_eq]
    exact inputAccepted
  let checked : CutFreeDerivation.CheckedCertificate :=
    ⟨output, outputAccepted⟩
  apply alignTree?_complete sourceEquation orderMembership inferred
    (checked := checked)
  · simp [CutFreeDerivation.desequentializeChecked?, desequentialized,
      outputAccepted, checked]
  · exact equivalent

private theorem axiomExchangeIdentity_infer (name : String)
    (positive : Bool) :
    (CutFreeDerivation.exchange [0, 1]
      (.axiom name positive)).infer? =
    some [.atom name positive, .atom name (!positive)] := by
  let atom : Formula := .atom name positive
  let dual : Formula := .atom name (!positive)
  have candidate :
      CutFreeDerivation.reorderCandidate? [atom, dual] [0, 1] =
        some [atom, dual] := by
    rfl
  change CutFreeDerivation.reorder? [atom, dual] [0, 1] =
    some [atom, dual]
  unfold CutFreeDerivation.reorder?
  rw [candidate]
  simp

private theorem axiomExchangeSwap_infer (name : String)
    (positive : Bool) :
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

private theorem axiomExchangeIdentity_desequentialize (name : String)
    (positive : Bool) :
    (CutFreeDerivation.exchange [0, 1]
      (.axiom name positive)).desequentialize? =
    some {
      formulas := #[.atom name positive, .atom name (!positive)]
      links := [.axiom 0 1]
      conclusions := [0, 1] } := by
  let atom : Formula := .atom name positive
  let dual : Formula := .atom name (!positive)
  have candidate :
      CutFreeDerivation.reorderCandidate?
        [(atom, 0), (dual, 1)] [0, 1] =
      some [(atom, 0), (dual, 1)] := by
    rfl
  simp [CutFreeDerivation.desequentialize?, CutFreeDerivation.build?,
    NetFragment.entries, CutFreeDerivation.reorder?, candidate,
    NetFragment.ofEntries, NetFragment.toCertificate, atom, dual,
    Formula.dual]

private theorem axiomExchangeSwap_desequentialize (name : String)
    (positive : Bool) :
    (CutFreeDerivation.exchange [1, 0]
      (.axiom name positive)).desequentialize? =
    some {
      formulas := #[.atom name positive, .atom name (!positive)]
      links := [.axiom 0 1]
      conclusions := [1, 0] } := by
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
  simp [CutFreeDerivation.desequentialize?, CutFreeDerivation.build?,
    NetFragment.entries, CutFreeDerivation.reorder?, candidate, permutation,
    NetFragment.ofEntries, NetFragment.toCertificate, atom, dual,
    Formula.dual]

private theorem axiomDirectSwap (name : String) (positive : Bool)
    (boundary : List Vertex) :
    ({ formulas := #[.atom name positive, .atom name (!positive)]
       links := [.axiom 0 1]
       conclusions := boundary } : Certificate).DirectProofNetEquivalent
    { formulas := #[.atom name (!positive), .atom name positive]
      links := [.axiom 1 0]
      conclusions := boundary.map
        (VertexRenaming.swap 2 0 1 (by decide) (by decide)).forward } := by
  let swap := VertexRenaming.swap 2 0 1 (by decide) (by decide)
  refine ⟨swap, ?_⟩
  constructor
  · apply Array.ext
    · simp [Certificate.reindex]
    · intro index leftInBounds rightInBounds
      have indexCases : index = 0 ∨ index = 1 :=
        Nat.le_one_iff_eq_zero_or_eq_one.mp
          (Nat.lt_succ_iff.mp (by simpa using leftInBounds))
      rcases indexCases with rfl | rfl <;>
        simp [Certificate.reindex, swap, VertexRenaming.swap]
  · simp [Link.reindex, swap, VertexRenaming.swap]
  · change boundary.map swap.forward =
      boundary.map
        (VertexRenaming.swap 2 0 1 (by decide) (by decide)).forward
    rfl

private def axiomTree? (certificate : Certificate)
    (target : List Formula) : Option CutFreeDerivation :=
  if certificate.links.any (fun link => link.isConnective) then
    none
  else
    firstSome (fun formula =>
      match formula with
      | .atom name positive =>
          alignTree? certificate (.axiom name positive) target
      | _ => none) certificate.formulas.toList

private theorem axiomTree?_of_alignedAxiom {certificate : Certificate}
    {target : List Formula} {name : String} {positive : Bool}
    (noConnective :
      certificate.links.any (fun link => link.isConnective) = false)
    (formulaMembership :
      Formula.atom name positive ∈ certificate.formulas.toList)
    (aligned :
      (alignTree? certificate (.axiom name positive) target).isSome = true) :
    (axiomTree? certificate target).isSome = true := by
  unfold axiomTree?
  simp only [noConnective, Bool.false_eq_true, ↓reduceIte]
  apply firstSome_isSome_of_mem _ _ (.atom name positive)
    formulaMembership
  exact aligned

private theorem axiomTree?_sound {certificate : Certificate}
    {target : List Formula} {tree : CutFreeDerivation}
    (labels : certificate.conclusionFormulas? = some target)
    (equation : axiomTree? certificate target = some tree) :
    ∃ result : ExecutableSequentializationResult certificate,
      result.tree = tree := by
  unfold axiomTree? at equation
  split at equation
  · contradiction
  · rcases firstSome_eq_some equation with
      ⟨formula, _formulaMembership, branchEquation⟩
    cases formula with
    | atom name positive =>
        exact alignTree?_sound labels branchEquation
    | tensor left right => simp at branchEquation
    | par left right => simp at branchEquation

/-- The executable axiom branch is total on the checker-accepted base case.
This is the first inverse-rule case where the proposition-level
sequentialization theorem is connected all the way to the runtime search. -/
private theorem axiomTree?_complete {certificate : Certificate}
    (accepted : certificate.check = true) {target : List Formula}
    (labels : certificate.conclusionFormulas? = some target)
    (noConnective : ¬ ∃ link ∈ certificate.links,
      link.isConnective = true) :
    (axiomTree? certificate target).isSome = true := by
  have correct := certificate.check_sound_declarative accepted
  rcases correct.axiomOnly_certificate_cases noConnective with
    ⟨name, positive, shape⟩
  rcases shape with shape | shape | shape | shape
  · subst certificate
    simp [Certificate.conclusionFormulas?, Certificate.formula?] at labels
    subst target
    apply axiomTree?_of_alignedAxiom (name := name) (positive := positive)
      (by rfl) (by simp)
    have orderMembership :
        [0, 1] ∈ matchingFormulaOrders
          [.atom name positive, .atom name (!positive)]
          [.atom name positive, .atom name (!positive)] :=
      matchingFormulaOrders_complete _ _ _ (by simp)
        (by change [0, 1].Perm [0, 1]; exact .refl _) (by simp)
    exact alignTree?_complete_of_desequentialize accepted rfl
      orderMembership (axiomExchangeIdentity_infer name positive)
      (axiomExchangeIdentity_desequentialize name positive)
      (.refl _)
  · subst certificate
    simp [Certificate.conclusionFormulas?, Certificate.formula?] at labels
    subst target
    apply axiomTree?_of_alignedAxiom (name := name) (positive := positive)
      (by rfl) (by simp)
    have orderMembership :
        [1, 0] ∈ matchingFormulaOrders
          [.atom name positive, .atom name (!positive)]
          [.atom name (!positive), .atom name positive] :=
      matchingFormulaOrders_complete _ _ _ (by simp)
        (.swap _ _ []) (by simp)
    exact alignTree?_complete_of_desequentialize accepted rfl
      orderMembership (axiomExchangeSwap_infer name positive)
      (axiomExchangeSwap_desequentialize name positive)
      (.refl _)
  · subst certificate
    simp [Certificate.conclusionFormulas?, Certificate.formula?] at labels
    subst target
    apply axiomTree?_of_alignedAxiom (name := name) (positive := positive)
      (by rfl) (by simp)
    have orderMembership :
        [1, 0] ∈ matchingFormulaOrders
          [.atom name positive, .atom name (!positive)]
          [.atom name (!positive), .atom name positive] :=
      matchingFormulaOrders_complete _ _ _ (by simp)
        (.swap _ _ []) (by simp)
    exact alignTree?_complete_of_desequentialize accepted rfl
      orderMembership (axiomExchangeSwap_infer name positive)
      (axiomExchangeSwap_desequentialize name positive)
      (axiomDirectSwap name positive [1, 0])
  · subst certificate
    simp [Certificate.conclusionFormulas?, Certificate.formula?] at labels
    subst target
    apply axiomTree?_of_alignedAxiom (name := name) (positive := positive)
      (by rfl) (by simp)
    have orderMembership :
        [0, 1] ∈ matchingFormulaOrders
          [.atom name positive, .atom name (!positive)]
          [.atom name positive, .atom name (!positive)] :=
      matchingFormulaOrders_complete _ _ _ (by simp)
        (by change [0, 1].Perm [0, 1]; exact .refl _) (by simp)
    exact alignTree?_complete_of_desequentialize accepted rfl
      orderMembership (axiomExchangeIdentity_infer name positive)
      (axiomExchangeIdentity_desequentialize name positive)
      (axiomDirectSwap name positive [0, 1])

private def rebuildParTree? (input : Certificate)
    (premiseTree : CutFreeDerivation)
    (target : List Formula) : Option CutFreeDerivation := do
  let premiseSequent ← premiseTree.infer?
  if premiseSequent.length < 2 then
    none
  else
    let focus := premiseSequent.length - 2
    alignTree? input (.par focus focus premiseTree) target

private theorem rebuildParTree?_complete
    {input : Certificate} {left right conclusion : Vertex}
    (structural : input.StructurallyWellFormed)
    (terminal : input.TerminalPar left right conclusion)
    (inputAccepted : input.check = true)
    (premiseAccepted :
      (input.peelTerminalPar left right conclusion).check = true)
    (premiseResult : ExecutableSequentializationResult
      (input.peelTerminalPar left right conclusion))
    {target : List Formula}
    (labels : input.conclusionFormulas? = some target) :
    (rebuildParTree? input premiseResult.tree target).isSome = true := by
  let propositionResult := premiseResult.toSequentializationResult
  rcases TerminalPar.sequentializationResultShaped structural terminal
      premiseAccepted propositionResult with
    ⟨result, order, treeShape, premiseLength⟩
  have resultSequent : result.sequent = target := by
    exact Option.some.inj (result.inputLabels.symm.trans labels)
  let rawTree := CutFreeDerivation.par
    (propositionResult.sequent.length - 2)
    (propositionResult.sequent.length - 2) propositionResult.tree
  have alignedInfer :
      (CutFreeDerivation.exchange order rawTree).infer? = some target := by
    rw [← treeShape]
    simpa [resultSequent] using result.inferred
  have alignedDeselect :
      (CutFreeDerivation.exchange order rawTree).desequentialize? =
        some result.output := by
    rw [← treeShape]
    exact result.desequentialized
  have premiseLength' : 2 ≤ premiseResult.sequent.length := by
    simpa [propositionResult,
      ExecutableSequentializationResult.toSequentializationResult] using
      premiseLength
  cases sourceEquation : rawTree.infer? with
  | none =>
      simp [CutFreeDerivation.infer?, sourceEquation] at alignedInfer
  | some source =>
      have reordered : CutFreeDerivation.reorder? source order = some target := by
        simpa [CutFreeDerivation.infer?, sourceEquation] using alignedInfer
      have orderMembership :=
        matchingFormulaOrders_complete_of_reorder? reordered
      have alignmentFound := alignTree?_complete_of_desequentialize
        inputAccepted sourceEquation orderMembership alignedInfer
        alignedDeselect result.equivalent.toDirect
      have notShort : ¬ premiseResult.sequent.length < 2 :=
        Nat.not_lt.mpr premiseLength'
      simpa [rebuildParTree?, premiseResult.inferred, notShort, rawTree,
        propositionResult,
        ExecutableSequentializationResult.toSequentializationResult] using
        alignmentFound

private theorem rebuildParTree?_sound {input : Certificate}
    {premiseTree tree : CutFreeDerivation} {target : List Formula}
    (labels : input.conclusionFormulas? = some target)
    (equation : rebuildParTree? input premiseTree target = some tree) :
    ∃ result : ExecutableSequentializationResult input,
      result.tree = tree := by
  unfold rebuildParTree? at equation
  cases premiseEquation : premiseTree.infer? with
  | none => simp [premiseEquation] at equation
  | some premiseSequent =>
      by_cases short : premiseSequent.length < 2
      · simp [premiseEquation, short] at equation
      · exact alignTree?_sound labels (by
          simpa [premiseEquation, short] using equation)

private def rebuildTensorTree? (input : Certificate)
    (leftTree rightTree : CutFreeDerivation)
    (target : List Formula) : Option CutFreeDerivation := do
  let leftSequent ← leftTree.infer?
  let rightSequent ← rightTree.infer?
  if leftSequent.isEmpty || rightSequent.isEmpty then
    none
  else
    alignTree? input (.tensor (leftSequent.length - 1)
      (rightSequent.length - 1) leftTree rightTree) target

private theorem rebuildTensorTree?_complete
    {input leftCertificate rightCertificate : Certificate}
    {left right conclusion : Vertex}
    (structural : input.StructurallyWellFormed)
    (splitting : input.SplittingTensor left right conclusion)
    (splitEquation : input.splitTerminalTensorCandidate?
      left right conclusion = some (leftCertificate, rightCertificate))
    (inputAccepted : input.check = true)
    (leftAccepted : leftCertificate.check = true)
    (rightAccepted : rightCertificate.check = true)
    (leftResult : ExecutableSequentializationResult leftCertificate)
    (rightResult : ExecutableSequentializationResult rightCertificate)
    {target : List Formula}
    (labels : input.conclusionFormulas? = some target) :
    (rebuildTensorTree? input leftResult.tree rightResult.tree target).isSome =
      true := by
  let leftPropositionResult := leftResult.toSequentializationResult
  let rightPropositionResult := rightResult.toSequentializationResult
  rcases TerminalTensor.sequentializationResultShaped structural splitting
      splitEquation leftAccepted rightAccepted leftPropositionResult
      rightPropositionResult with
    ⟨result, order, treeShape, leftLength, rightLength⟩
  have resultSequent : result.sequent = target := by
    exact Option.some.inj (result.inputLabels.symm.trans labels)
  let rawTree := CutFreeDerivation.tensor
    (leftPropositionResult.sequent.length - 1)
    (rightPropositionResult.sequent.length - 1)
    leftPropositionResult.tree rightPropositionResult.tree
  have alignedInfer :
      (CutFreeDerivation.exchange order rawTree).infer? = some target := by
    rw [← treeShape]
    simpa [resultSequent] using result.inferred
  have alignedDeselect :
      (CutFreeDerivation.exchange order rawTree).desequentialize? =
        some result.output := by
    rw [← treeShape]
    exact result.desequentialized
  have leftLength' : 1 ≤ leftResult.sequent.length := by
    simpa [leftPropositionResult,
      ExecutableSequentializationResult.toSequentializationResult] using
      leftLength
  have rightLength' : 1 ≤ rightResult.sequent.length := by
    simpa [rightPropositionResult,
      ExecutableSequentializationResult.toSequentializationResult] using
      rightLength
  cases sourceEquation : rawTree.infer? with
  | none =>
      simp [CutFreeDerivation.infer?, sourceEquation] at alignedInfer
  | some source =>
      have reordered : CutFreeDerivation.reorder? source order = some target := by
        simpa [CutFreeDerivation.infer?, sourceEquation] using alignedInfer
      have orderMembership :=
        matchingFormulaOrders_complete_of_reorder? reordered
      have alignmentFound := alignTree?_complete_of_desequentialize
        inputAccepted sourceEquation orderMembership alignedInfer
        alignedDeselect result.equivalent.toDirect
      have leftNonNil : leftResult.sequent ≠ [] := by
        intro empty
        rw [empty] at leftLength'
        change 1 ≤ 0 at leftLength'
        omega
      have rightNonNil : rightResult.sequent ≠ [] := by
        intro empty
        rw [empty] at rightLength'
        change 1 ≤ 0 at rightLength'
        omega
      simpa [rebuildTensorTree?, leftResult.inferred, rightResult.inferred,
        leftNonNil, rightNonNil, rawTree, leftPropositionResult,
        rightPropositionResult,
        ExecutableSequentializationResult.toSequentializationResult] using
        alignmentFound

private theorem rebuildTensorTree?_sound {input : Certificate}
    {leftTree rightTree tree : CutFreeDerivation} {target : List Formula}
    (labels : input.conclusionFormulas? = some target)
    (equation : rebuildTensorTree? input leftTree rightTree target = some tree) :
    ∃ result : ExecutableSequentializationResult input,
      result.tree = tree := by
  unfold rebuildTensorTree? at equation
  cases leftEquation : leftTree.infer? with
  | none => simp [leftEquation] at equation
  | some leftSequent =>
      cases rightEquation : rightTree.infer? with
      | none => simp [leftEquation, rightEquation] at equation
      | some rightSequent =>
          cases leftSequent with
          | nil => simp [leftEquation, rightEquation] at equation
          | cons leftHead leftTail =>
              cases rightSequent with
              | nil => simp [leftEquation, rightEquation] at equation
              | cons rightHead rightTail =>
                  exact alignTree?_sound labels (by
                    simpa [leftEquation, rightEquation] using equation)

private def parTreeFrom
    (recurse : Certificate → Except SequentializationError CutFreeDerivation)
    (certificate : Certificate) (target : List Formula) :
    Option CutFreeDerivation :=
  firstSome (fun candidate =>
    let (left, right, conclusion) := candidate
    match certificate.peelTerminalParChecked? left right conclusion with
    | none => none
    | some premise =>
        match recurse premise.certificate with
        | .error _ => none
        | .ok premiseTree =>
            rebuildParTree? certificate premiseTree target)
    certificate.terminalPars

private def tensorTreeFrom
    (recurse : Certificate → Except SequentializationError CutFreeDerivation)
    (certificate : Certificate) (target : List Formula) :
    Option CutFreeDerivation :=
  firstSome (fun candidate =>
    let (left, right, conclusion) := candidate
    match certificate.splitTerminalTensorChecked? left right conclusion with
    | none => none
    | some premises =>
        match recurse premises.leftPremise.certificate with
        | .error _ => none
        | .ok leftTree =>
            match recurse premises.rightPremise.certificate with
            | .error _ => none
            | .ok rightTree =>
                rebuildTensorTree? certificate leftTree rightTree target)
    certificate.terminalTensors

private theorem parTreeFrom_sound
    (recurse : Certificate →
      Except SequentializationError CutFreeDerivation)
    {certificate : Certificate} {target : List Formula}
    {tree : CutFreeDerivation}
    (labels : certificate.conclusionFormulas? = some target)
    (equation : parTreeFrom recurse certificate target = some tree) :
    ∃ result : ExecutableSequentializationResult certificate,
      result.tree = tree := by
  unfold parTreeFrom at equation
  rcases firstSome_eq_some equation with
    ⟨candidate, _membership, branchEquation⟩
  rcases candidate with ⟨left, ⟨right, conclusion⟩⟩
  cases premiseEquation :
      certificate.peelTerminalParChecked? left right conclusion with
  | none => simp [premiseEquation] at branchEquation
  | some premise =>
      cases recursiveEquation : recurse premise.certificate with
      | error error =>
          simp [premiseEquation, recursiveEquation] at branchEquation
      | ok premiseTree =>
          exact rebuildParTree?_sound labels (by
            simpa [premiseEquation, recursiveEquation] using branchEquation)

private theorem tensorTreeFrom_sound
    (recurse : Certificate →
      Except SequentializationError CutFreeDerivation)
    {certificate : Certificate} {target : List Formula}
    {tree : CutFreeDerivation}
    (labels : certificate.conclusionFormulas? = some target)
    (equation : tensorTreeFrom recurse certificate target = some tree) :
    ∃ result : ExecutableSequentializationResult certificate,
      result.tree = tree := by
  unfold tensorTreeFrom at equation
  rcases firstSome_eq_some equation with
    ⟨candidate, _membership, branchEquation⟩
  rcases candidate with ⟨left, ⟨right, conclusion⟩⟩
  cases premisesEquation :
      certificate.splitTerminalTensorChecked? left right conclusion with
  | none => simp [premisesEquation] at branchEquation
  | some premises =>
      cases leftEquation : recurse premises.leftPremise.certificate with
      | error error =>
          simp [premisesEquation, leftEquation] at branchEquation
      | ok leftTree =>
          cases rightEquation : recurse premises.rightPremise.certificate with
          | error error =>
              simp [premisesEquation, leftEquation, rightEquation]
                at branchEquation
          | ok rightTree =>
              exact rebuildTensorTree?_sound labels (by
                simpa [premisesEquation, leftEquation, rightEquation] using
                  branchEquation)

private theorem parTreeFrom_complete_of_candidate
    (recurse : Certificate →
      Except SequentializationError CutFreeDerivation)
    {certificate : Certificate} {target : List Formula}
    {left right conclusion : Vertex}
    (membership :
      (left, right, conclusion) ∈ certificate.terminalPars)
    {premise : CutFreeDerivation.CheckedCertificate}
    (premiseEquation :
      certificate.peelTerminalParChecked? left right conclusion = some premise)
    (premiseResult :
      ExecutableSequentializationResult premise.certificate)
    (recursiveEquation : recurse premise.certificate = .ok premiseResult.tree)
    (rebuildFound :
      (rebuildParTree? certificate premiseResult.tree target).isSome = true) :
    (parTreeFrom recurse certificate target).isSome = true := by
  unfold parTreeFrom
  apply firstSome_isSome_of_mem _ _ (left, right, conclusion) membership
  simpa [premiseEquation, recursiveEquation] using rebuildFound

private theorem tensorTreeFrom_complete_of_candidate
    (recurse : Certificate →
      Except SequentializationError CutFreeDerivation)
    {certificate : Certificate} {target : List Formula}
    {left right conclusion : Vertex}
    (membership :
      (left, right, conclusion) ∈ certificate.terminalTensors)
    {premises : CheckedTensorPremises}
    (premisesEquation :
      certificate.splitTerminalTensorChecked? left right conclusion =
        some premises)
    (leftResult : ExecutableSequentializationResult
      premises.leftPremise.certificate)
    (rightResult : ExecutableSequentializationResult
      premises.rightPremise.certificate)
    (leftRecursive :
      recurse premises.leftPremise.certificate = .ok leftResult.tree)
    (rightRecursive :
      recurse premises.rightPremise.certificate = .ok rightResult.tree)
    (rebuildFound :
      (rebuildTensorTree? certificate leftResult.tree rightResult.tree target).isSome =
        true) :
    (tensorTreeFrom recurse certificate target).isSome = true := by
  unfold tensorTreeFrom
  apply firstSome_isSome_of_mem _ _ (left, right, conclusion) membership
  simpa [premisesEquation, leftRecursive, rightRecursive] using rebuildFound

private theorem splitTerminalTensorChecked?_candidateEquation
    {certificate : Certificate} {left right conclusion : Vertex}
    {premises : CheckedTensorPremises}
    (equation : certificate.splitTerminalTensorChecked?
      left right conclusion = some premises) :
    certificate.splitTerminalTensorCandidate? left right conclusion =
      some (premises.leftPremise.certificate,
        premises.rightPremise.certificate) := by
  unfold splitTerminalTensorChecked? at equation
  cases candidateEquation :
      certificate.splitTerminalTensorCandidate? left right conclusion with
  | none => simp [candidateEquation] at equation
  | some pair =>
      rcases pair with ⟨leftCertificate, rightCertificate⟩
      by_cases leftAccepted : leftCertificate.check = true
      · by_cases rightAccepted : rightCertificate.check = true
        · have same : ({
              leftPremise := ⟨leftCertificate, leftAccepted⟩
              rightPremise := ⟨rightCertificate, rightAccepted⟩ } :
              CheckedTensorPremises) = premises := by
            simpa [candidateEquation, leftAccepted, rightAccepted] using
              equation
          have leftSame : leftCertificate =
              premises.leftPremise.certificate :=
            congrArg (fun value => value.leftPremise.certificate) same
          have rightSame : rightCertificate =
              premises.rightPremise.certificate :=
            congrArg (fun value => value.rightPremise.certificate) same
          exact congrArg some (Prod.ext leftSame rightSame)
        · simp [candidateEquation, leftAccepted, rightAccepted] at equation
      · simp [candidateEquation, leftAccepted] at equation

/-- Fuel-bounded executable inverse-rule search.  Every recursive premise is
independently checker-gated.  Fuel is exposed only for diagnostics and tests;
`sequentialize` supplies one more than the number of formula occurrences. -/
def executableTreeWithFuel : Nat → Certificate →
    Except SequentializationError CutFreeDerivation
  | 0, certificate =>
      .error (sequentializationError certificate "fuel"
        "inverse-rule search exhausted its occurrence bound")
  | fuel + 1, certificate =>
      if certificate.check != true then
        .error (sequentializationError certificate "input"
          "certificate was rejected by the proof-net checker")
      else
        match certificate.conclusionFormulas? with
        | none =>
            .error (sequentializationError certificate "boundary"
              "accepted certificate had unreadable conclusion labels")
        | some target =>
            match axiomTree? certificate target with
            | some tree => .ok tree
            | none =>
                let parTree := parTreeFrom
                  (executableTreeWithFuel fuel) certificate target
                match parTree with
                | some tree => .ok tree
                | none =>
                    let tensorTree := tensorTreeFrom
                      (executableTreeWithFuel fuel) certificate target
                    match tensorTree with
                    | some tree => .ok tree
                    | none =>
                        .error (sequentializationError certificate "search"
                          "no checker-preserving inverse rule reconstructed a derivation")

/-- Any positive fuel suffices for the executable axiom-only branch.  The
proof uses the literal base-case classification and the finite alignment
search completeness theorem above; it does not assume that evaluation happens
to succeed on the four representations. -/
private theorem executableTreeWithFuel_axiomOnly
    (certificate : Certificate) (accepted : certificate.check = true)
    {target : List Formula}
    (labels : certificate.conclusionFormulas? = some target)
    (noConnective : ¬ ∃ link ∈ certificate.links,
      link.isConnective = true) (fuel : Nat) :
    ∃ tree, certificate.executableTreeWithFuel (fuel + 1) = .ok tree := by
  have axiomFound := axiomTree?_complete accepted labels noConnective
  cases equation : axiomTree? certificate target with
  | none => simp [equation] at axiomFound
  | some tree =>
      refine ⟨tree, ?_⟩
      simp [executableTreeWithFuel, accepted, labels, equation]

/-- The fuel-bounded runtime search is complete whenever its fuel strictly
exceeds the input occurrence count.  The returned witness is already packaged
with the same proof-bearing contract used by the public API. -/
private theorem executableTreeWithFuel_complete
    (fuel : Nat) (certificate : Certificate)
    (accepted : certificate.check = true)
    (fuelBound : certificate.formulas.size < fuel) :
    ∃ result : ExecutableSequentializationResult certificate,
      certificate.executableTreeWithFuel fuel = .ok result.tree := by
  induction fuel generalizing certificate with
  | zero => omega
  | succ fuel ih =>
      have correct : certificate.DeclarativelyCorrect :=
        certificate.check_iff_declarativelyCorrect.mp accepted
      have structural : certificate.StructurallyWellFormed := correct.1
      rcases certificate.sequentialization_of_check accepted with
        ⟨existenceResult⟩
      let target := existenceResult.sequent
      have labels : certificate.conclusionFormulas? = some target := by
        simpa [target] using existenceResult.inputLabels
      by_cases connectiveExists : ∃ link ∈ certificate.links,
          link.isConnective = true
      · rcases connectiveExists with ⟨connective, connectiveMembership,
          connectiveTrue⟩
        have connectiveAny :
            certificate.links.any (fun link => link.isConnective) = true := by
          simp only [List.any_eq_true]
          exact ⟨connective, connectiveMembership, connectiveTrue⟩
        have axiomNone : axiomTree? certificate target = none := by
          simp [axiomTree?, connectiveAny]
        have connectiveExists' : ∃ link ∈ certificate.links,
            link.isConnective = true :=
          ⟨connective, connectiveMembership, connectiveTrue⟩
        rcases correct.terminalPar_or_splittingTensor_exists
            connectiveExists' with
          ⟨left, right, conclusion, terminal | splitting⟩
        · let premiseCertificate :=
            certificate.peelTerminalPar left right conclusion
          have premiseAccepted : premiseCertificate.check = true := by
            exact certificate.peelTerminalPar_check_of_check structural
              terminal accepted
          have premiseSmaller : premiseCertificate.formulas.size <
              certificate.formulas.size := by
            exact certificate.peelTerminalPar_formulas_size_lt structural
              terminal
          have premiseFuel : premiseCertificate.formulas.size < fuel := by
            omega
          rcases ih premiseCertificate premiseAccepted premiseFuel with
            ⟨premiseResult, recursiveEquation⟩
          let checked : CutFreeDerivation.CheckedCertificate :=
            ⟨premiseCertificate, premiseAccepted⟩
          have checkedEquation :
              certificate.peelTerminalParChecked? left right conclusion =
                some checked := by
            simp [peelTerminalParChecked?,
              certificate.peelTerminalParCandidate?_eq_some structural
                terminal,
              premiseCertificate, premiseAccepted, checked]
          let checkedResult :
              ExecutableSequentializationResult checked.certificate := by
            simpa [checked] using premiseResult
          have recursiveChecked :
              checked.certificate.executableTreeWithFuel fuel =
                .ok checkedResult.tree := by
            simpa [checked, checkedResult] using recursiveEquation
          have rebuildFound :
              (rebuildParTree? certificate checkedResult.tree target).isSome =
                true := by
            simpa [checked, checkedResult, premiseCertificate] using
              rebuildParTree?_complete structural terminal accepted
                premiseAccepted premiseResult labels
          have membership :
              (left, right, conclusion) ∈ certificate.terminalPars :=
            (certificate.mem_terminalPars_iff left right conclusion).mpr
              terminal
          have parFound := parTreeFrom_complete_of_candidate
            (executableTreeWithFuel fuel) membership checkedEquation
            checkedResult recursiveChecked rebuildFound
          cases parEquation : parTreeFrom
              (executableTreeWithFuel fuel) certificate target with
          | none => simp [parEquation] at parFound
          | some tree =>
              rcases parTreeFrom_sound
                  (executableTreeWithFuel fuel) labels parEquation
                with ⟨result, resultTree⟩
              refine ⟨result, ?_⟩
              simp [executableTreeWithFuel, accepted, labels, axiomNone,
                parEquation, resultTree]
        · rcases certificate.splitTerminalTensorChecked?_eq_some_exists
              structural splitting accepted with
            ⟨premises, premisesEquation⟩
          have candidateEquation :=
            splitTerminalTensorChecked?_candidateEquation premisesEquation
          have leftSmaller : premises.leftPremise.certificate.formulas.size <
              certificate.formulas.size :=
            certificate.splitTerminalTensorCandidate?_left_formulas_size_lt
              structural splitting candidateEquation
          have rightSmaller : premises.rightPremise.certificate.formulas.size <
              certificate.formulas.size :=
            certificate.splitTerminalTensorCandidate?_right_formulas_size_lt
              structural splitting candidateEquation
          have leftFuel : premises.leftPremise.certificate.formulas.size <
              fuel := by omega
          have rightFuel : premises.rightPremise.certificate.formulas.size <
              fuel := by omega
          rcases ih premises.leftPremise.certificate
              premises.leftPremise.accepted leftFuel with
            ⟨leftResult, leftRecursive⟩
          rcases ih premises.rightPremise.certificate
              premises.rightPremise.accepted rightFuel with
            ⟨rightResult, rightRecursive⟩
          have rebuildFound := rebuildTensorTree?_complete structural splitting
            candidateEquation accepted premises.leftPremise.accepted
              premises.rightPremise.accepted leftResult rightResult labels
          have membership :
              (left, right, conclusion) ∈ certificate.terminalTensors :=
            (certificate.mem_terminalTensors_iff left right conclusion).mpr
              splitting.1
          have tensorFound := tensorTreeFrom_complete_of_candidate
            (executableTreeWithFuel fuel) membership
              premisesEquation leftResult rightResult leftRecursive
              rightRecursive rebuildFound
          cases parEquation : parTreeFrom
              (executableTreeWithFuel fuel) certificate target with
          | some tree =>
              rcases parTreeFrom_sound
                  (executableTreeWithFuel fuel) labels parEquation
                with ⟨result, resultTree⟩
              refine ⟨result, ?_⟩
              simp [executableTreeWithFuel, accepted, labels, axiomNone,
                parEquation, resultTree]
          | none =>
              cases tensorEquation : tensorTreeFrom
                  (executableTreeWithFuel fuel) certificate target
              with
              | none => simp [tensorEquation] at tensorFound
              | some tree =>
                  rcases tensorTreeFrom_sound
                      (executableTreeWithFuel fuel) labels
                        tensorEquation with
                    ⟨result, resultTree⟩
                  refine ⟨result, ?_⟩
                  simp [executableTreeWithFuel, accepted, labels, axiomNone,
                    parEquation, tensorEquation, resultTree]
      · have axiomFound :=
          axiomTree?_complete accepted labels connectiveExists
        cases axiomEquation : axiomTree? certificate target with
        | none => simp [axiomEquation] at axiomFound
        | some tree =>
            rcases axiomTree?_sound labels axiomEquation with
              ⟨result, resultTree⟩
            refine ⟨result, ?_⟩
            simp [executableTreeWithFuel, accepted, labels, axiomEquation,
              resultTree]

/-- Executable certificate-to-derivation API.  Successful results are
proof-bearing values, while failures retain a stable stage and certificate
size instead of collapsing to `none`. -/
def sequentialize (certificate : Certificate) :
    Except SequentializationError
      (ExecutableSequentializationResult certificate) := do
  if _inputAccepted : certificate.check = true then
    let tree ← certificate.executableTreeWithFuel
      (certificate.formulas.size + 1)
    match labels : certificate.conclusionFormulas? with
    | none =>
        throw (sequentializationError certificate "boundary"
          "could not read the input conclusion labels")
    | some sequent =>
        if inferred : tree.infer? = some sequent then
          match desequentialized : tree.desequentialize? with
          | none =>
              throw (sequentializationError certificate "output"
                "reconstructed tree did not desequentialize")
          | some output =>
              if outputAccepted : output.check = true then
                match directProofNetEquivalentWitness? output certificate with
                | some witness =>
                  have equivalent : output.ProofNetEquivalent certificate :=
                    witness.proofNetEquivalent
                  pure {
                    tree
                    sequent
                    output
                    inferred
                    inputLabels := labels
                    desequentialized
                    outputAccepted
                    equivalent }
                | none =>
                  throw (sequentializationError certificate "equivalence"
                    "reconstructed output was not proof-net-equivalent to the input")
              else
                throw (sequentializationError certificate "output"
                  "desequentialized tree was rejected by the proof-net checker")
        else
          throw (sequentializationError certificate "inference"
            "reconstructed tree did not infer the exact input boundary")
  else
    throw (sequentializationError certificate "input"
      "certificate was rejected by the proof-net checker")

/-- Universal success theorem for the public runtime API.  Every certificate
accepted by the reference checker evaluates to a proof-bearing executable
sequentialization result; staged errors are therefore reserved for rejected
inputs or violations of the proved implementation contract. -/
theorem sequentialize_complete (certificate : Certificate)
    (accepted : certificate.check = true) :
    ∃ result : ExecutableSequentializationResult certificate,
      certificate.sequentialize = .ok result := by
  rcases executableTreeWithFuel_complete
      (certificate.formulas.size + 1) certificate accepted (by omega) with
    ⟨treeResult, treeEquation⟩
  have outputStructural : treeResult.output.StructurallyWellFormed :=
    (treeResult.output.check_sound_declarative
      treeResult.outputAccepted).1
  have witnessFound := directProofNetEquivalentWitness?_complete
    outputStructural treeResult.equivalent.toDirect
  cases witnessEquation :
      directProofNetEquivalentWitness? treeResult.output certificate with
  | none => simp [witnessEquation] at witnessFound
  | some witness =>
      let result : ExecutableSequentializationResult certificate := {
        tree := treeResult.tree
        sequent := treeResult.sequent
        output := treeResult.output
        inferred := treeResult.inferred
        inputLabels := treeResult.inputLabels
        desequentialized := treeResult.desequentialized
        outputAccepted := treeResult.outputAccepted
        equivalent := witness.proofNetEquivalent }
      refine ⟨result, ?_⟩
      unfold sequentialize
      rw [dif_pos accepted]
      rw [treeEquation]
      simp only [bind, Except.bind]
      split
      · rename_i labelsEquation
        have impossible := treeResult.inputLabels
        rw [labelsEquation] at impossible
        contradiction
      · rename_i sequent labelsEquation
        have sameSequent : sequent = treeResult.sequent := by
          exact Option.some.inj
            (labelsEquation.symm.trans treeResult.inputLabels)
        subst sequent
        split
        · rename_i inferredEquation
          split
          · rename_i desequentializedEquation
            have impossible := treeResult.desequentialized
            rw [desequentializedEquation] at impossible
            contradiction
          · rename_i output desequentializedEquation
            have outputSame : output = treeResult.output := by
              exact Option.some.inj
                (desequentializedEquation.symm.trans
                  treeResult.desequentialized)
            subst output
            rw [dif_pos treeResult.outputAccepted]
            rw [witnessEquation]
            rfl
        · rename_i notInferred
          exact (notInferred treeResult.inferred).elim

end Certificate

end ProofNetIR
