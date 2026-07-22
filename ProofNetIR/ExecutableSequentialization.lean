import ProofNetIR.Sequentialization

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

theorem proofNetEquivalent {input : Certificate}
    (result : ExecutableSequentializationResult input) :
    result.output.ProofNetEquivalent input :=
  result.equivalent

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
      none) (matchingFormulaOrders left.formulas.toList right.formulas.toList)

/-- The executable direct-equivalence search is complete on structurally
well-formed left certificates.  In particular, link-list reordering cannot hide
an existing bounded-renaming witness from the finite occurrence search. -/
theorem directProofNetEquivalentWitness?_complete {left right : Certificate}
    (leftStructural : left.StructurallyWellFormed)
    (equivalent : left.DirectProofNetEquivalent right) :
    (directProofNetEquivalentWitness? left right).isSome = true := by
  rcases equivalent with ⟨vertexMap, relation⟩
  let order := (List.range left.formulas.size).map vertexMap.inverse
  have sameLength : left.formulas.toList.length = right.formulas.toList.length := by
    simpa using congrArg Array.size relation.formulas
  have permutation : order.Perm (List.range left.formulas.toList.length) := by
    simpa [order] using vertexRenaming_inverse_range_perm vertexMap
  have lookup : order.mapM (fun index => left.formulas.toList[index]?) =
      some right.formulas.toList := by
    have generated := reindexFormulaOrder_lookup left vertexMap
    rw [relation.formulas] at generated
    simpa [order] using generated
  have orderMembership : order ∈
      matchingFormulaOrders left.formulas.toList right.formulas.toList :=
    matchingFormulaOrders_complete left.formulas.toList right.formulas.toList
      order sameLength permutation lookup
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

private def rebuildParTree? (input : Certificate)
    (premiseTree : CutFreeDerivation)
    (target : List Formula) : Option CutFreeDerivation := do
  let premiseSequent ← premiseTree.infer?
  if premiseSequent.length < 2 then
    none
  else
    let focus := premiseSequent.length - 2
    alignTree? input (.par focus focus premiseTree) target

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
                let parTree := firstSome (fun candidate =>
                  let (left, right, conclusion) := candidate
                  match certificate.peelTerminalParChecked?
                      left right conclusion with
                  | none => none
                  | some premise =>
                      match executableTreeWithFuel fuel premise.certificate with
                      | .error _ => none
                      | .ok premiseTree =>
                          rebuildParTree? certificate premiseTree target)
                    certificate.terminalPars
                match parTree with
                | some tree => .ok tree
                | none =>
                    let tensorTree := firstSome (fun candidate =>
                      let (left, right, conclusion) := candidate
                      match certificate.splitTerminalTensorChecked?
                          left right conclusion with
                      | none => none
                      | some premises =>
                          match executableTreeWithFuel fuel
                              premises.leftPremise.certificate with
                          | .error _ => none
                          | .ok leftTree =>
                              match executableTreeWithFuel fuel
                                  premises.rightPremise.certificate with
                              | .error _ => none
                              | .ok rightTree =>
                                  rebuildTensorTree? certificate leftTree
                                    rightTree target)
                        certificate.terminalTensors
                    match tensorTree with
                    | some tree => .ok tree
                    | none =>
                        .error (sequentializationError certificate "search"
                          "no checker-preserving inverse rule reconstructed a derivation")

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

end Certificate

end ProofNetIR
