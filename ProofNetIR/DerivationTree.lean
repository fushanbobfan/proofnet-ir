import ProofNetIR.Reconstruct

namespace ProofNetIR

/-- First-order syntax for arbitrary cut-free, unit-free one-sided MLL
derivations. Tensor and par store the occurrence positions selected by the
rule; exchange stores an explicit permutation of occurrence indices. -/
inductive CutFreeDerivation where
  | axiom (name : String) (positive : Bool)
  | tensor (leftFocus rightFocus : Nat)
      (left right : CutFreeDerivation)
  | par (leftFocus rightFocus : Nat) (premise : CutFreeDerivation)
  | exchange (order : List Nat) (premise : CutFreeDerivation)
  deriving Repr, DecidableEq

/-- Internal desequentialization state. `conclusions` and `roots` are kept in
lockstep; constructors below never expose this representation to callers. -/
structure NetFragment where
  formulas : Array Formula
  links : List Link
  conclusions : List Formula
  roots : List Vertex
  deriving Repr, DecidableEq

namespace NetFragment

def entries (fragment : NetFragment) : List (Formula × Vertex) :=
  fragment.conclusions.zip fragment.roots

def ofEntries (formulas : Array Formula) (links : List Link)
    (entries : List (Formula × Vertex)) : NetFragment :=
  { formulas
    links
    conclusions := entries.map Prod.fst
    roots := entries.map Prod.snd }

def toCertificate (fragment : NetFragment) : Certificate :=
  { formulas := fragment.formulas
    links := fragment.links
    conclusions := fragment.roots }

end NetFragment

namespace CutFreeDerivation

/-- Remove and return the element at `index`, preserving the order of all
remaining elements. -/
def pick? : List α → Nat → Option (α × List α)
  | [], _ => none
  | head :: tail, 0 => some (head, tail)
  | head :: tail, index + 1 => do
      let (selected, remaining) ← pick? tail index
      pure (selected, head :: remaining)

/-- Apply an explicit permutation written as original occurrence indices.
Malformed, duplicated, missing, or out-of-bounds orders are rejected. -/
def reorderCandidate? (values : List α) (order : List Nat) : Option (List α) :=
  if order.length == values.length &&
      order.eraseDups.length == order.length &&
      order.all (fun index => index < values.length) then
    order.mapM fun index => values[index]?
  else
    none

/-- Reordering additionally validates the mathematical permutation relation.
This redundant check exposes a direct proof boundary for downstream theorems. -/
def reorder? [DecidableEq α] (values : List α) (order : List Nat) :
    Option (List α) := do
  let reordered ← reorderCandidate? values order
  if values.Perm reordered then some reordered else none

theorem reorder?_perm [DecidableEq α] {values reordered : List α}
    {order : List Nat} (accepted : reorder? values order = some reordered) :
    values.Perm reordered := by
  unfold reorder? at accepted
  cases candidateResult : reorderCandidate? values order with
  | none => simp [candidateResult] at accepted
  | some candidate =>
      by_cases permutation : values.Perm candidate
      · have same : candidate = reordered := by
          simpa [candidateResult, permutation] using accepted
        simpa [same] using permutation
      · simp [candidateResult, permutation] at accepted

/-- Infer the conclusion sequent of the first-order rule tree independently of
the proof-net fragment construction. -/
def infer? : CutFreeDerivation → Option (List Formula)
  | .axiom name positive =>
      let formula : Formula := .atom name positive
      some [formula, formula.dual]
  | .tensor leftFocus rightFocus leftTree rightTree => do
      let leftSequent ← infer? leftTree
      let rightSequent ← infer? rightTree
      let (left, leftContext) ← pick? leftSequent leftFocus
      let (right, rightContext) ← pick? rightSequent rightFocus
      pure (.tensor left right :: (leftContext ++ rightContext))
  | .par leftFocus rightFocus premise => do
      let sequent ← infer? premise
      let (left, afterLeft) ← pick? sequent leftFocus
      let (right, context) ← pick? afterLeft rightFocus
      pure (context ++ [.par left right])
  | .exchange order premise => do
      let sequent ← infer? premise
      reorder? sequent order

theorem pick?_perm {values : List α} {index : Nat} {selected : α}
    {remaining : List α}
    (accepted : pick? values index = some (selected, remaining)) :
    values.Perm (selected :: remaining) := by
  induction values generalizing index remaining with
  | nil => simp [pick?] at accepted
  | cons head tail ih =>
      cases index with
      | zero =>
          simp [pick?] at accepted
          obtain ⟨rfl, rfl⟩ := accepted
          exact .refl _
      | succ prior =>
          simp only [pick?] at accepted
          cases result : pick? tail prior with
          | none => simp [result] at accepted
          | some pair =>
              rcases pair with ⟨chosen, rest⟩
              simp [result] at accepted
              obtain ⟨rfl, rfl⟩ := accepted
              exact (ih result).cons head |>.trans (.swap chosen head rest)

/-- Selecting the first element after a known prefix removes exactly that
element and preserves the prefix and suffix order. -/
theorem pick?_append_cons (before : List α) (selected : α)
    (suffix : List α) :
    pick? (before ++ selected :: suffix) before.length =
      some (selected, before ++ suffix) := by
  induction before with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.cons_append, List.length_cons, pick?]
      rw [ih]
      rfl

/-- A par rule focused on the final two occurrences has the expected
right-boundary sequent, independently of the size of the preceding context. -/
theorem infer?_parLast
    {premise : CutFreeDerivation} {context : List Formula}
    {left right : Formula}
    (premiseInference : premise.infer? = some (context ++ [left, right])) :
    (CutFreeDerivation.par context.length context.length premise).infer? =
      some (context ++ [.par left right]) := by
  simp [infer?, premiseInference, pick?_append_cons]

/-- Tensor focused on the final occurrence of each premise produces the
tensor formula followed by the two untouched contexts. -/
theorem infer?_tensorLast
    {leftTree rightTree : CutFreeDerivation}
    {leftContext rightContext : List Formula}
    {left right : Formula}
    (leftInference : leftTree.infer? = some (leftContext ++ [left]))
    (rightInference : rightTree.infer? = some (rightContext ++ [right])) :
    (CutFreeDerivation.tensor leftContext.length rightContext.length
      leftTree rightTree).infer? =
      some (.tensor left right :: (leftContext ++ rightContext)) := by
  simp [infer?, leftInference, rightInference, pick?_append_cons]

/-- Successful first-order inference denotes a genuine kernel-typed derivation
in the independent `Derivation` sequent calculus. -/
theorem infer?_sound {tree : CutFreeDerivation} {sequent : List Formula}
    (accepted : tree.infer? = some sequent) :
    Nonempty (Derivation sequent) := by
  induction tree generalizing sequent with
  | «axiom» name positive =>
      simp [infer?] at accepted
      subst sequent
      exact ⟨Derivation.axiom name positive⟩
  | tensor leftFocus rightFocus leftTree rightTree leftIH rightIH =>
      simp only [infer?] at accepted
      cases leftResult : leftTree.infer? with
      | none => simp [leftResult] at accepted
      | some leftSequent =>
          cases rightResult : rightTree.infer? with
          | none => simp [leftResult, rightResult] at accepted
          | some rightSequent =>
              cases leftPick : pick? leftSequent leftFocus with
              | none => simp [leftResult, rightResult, leftPick] at accepted
              | some leftPair =>
                  rcases leftPair with ⟨leftFormula, leftContext⟩
                  cases rightPick : pick? rightSequent rightFocus with
                  | none =>
                      simp [leftResult, rightResult, rightPick] at accepted
                  | some rightPair =>
                      rcases rightPair with ⟨rightFormula, rightContext⟩
                      simp [leftResult, rightResult, leftPick, rightPick] at accepted
                      subst sequent
                      obtain ⟨leftDerivation⟩ := leftIH leftResult
                      obtain ⟨rightDerivation⟩ := rightIH rightResult
                      let leftFocused :
                          Derivation (leftFormula :: leftContext) :=
                        .exchange (pick?_perm leftPick) leftDerivation
                      let rightFocused :
                          Derivation (rightFormula :: rightContext) :=
                        .exchange (pick?_perm rightPick) rightDerivation
                      exact ⟨Derivation.tensor leftFocused rightFocused⟩
  | par leftFocus rightFocus premise ih =>
      simp only [infer?] at accepted
      cases premiseResult : premise.infer? with
      | none => simp [premiseResult] at accepted
      | some premiseSequent =>
          cases leftPick : pick? premiseSequent leftFocus with
          | none => simp [premiseResult, leftPick] at accepted
          | some leftPair =>
              rcases leftPair with ⟨leftFormula, afterLeft⟩
              cases rightPick : pick? afterLeft rightFocus with
              | none => simp [premiseResult, leftPick, rightPick] at accepted
              | some rightPair =>
                  rcases rightPair with ⟨rightFormula, context⟩
                  simp [premiseResult, leftPick, rightPick] at accepted
                  subst sequent
                  obtain ⟨premiseDerivation⟩ := ih premiseResult
                  have toFront : premiseSequent.Perm
                      (leftFormula :: rightFormula :: context) :=
                    (pick?_perm leftPick).trans
                      ((pick?_perm rightPick).cons leftFormula)
                  have rotate : (leftFormula :: rightFormula :: context).Perm
                      (context ++ [leftFormula, rightFormula]) := by
                    simpa using (List.perm_append_comm :
                      List.Perm ([leftFormula, rightFormula] ++ context)
                        (context ++ [leftFormula, rightFormula]))
                  let focused : Derivation
                      (context ++ [leftFormula, rightFormula]) :=
                    .exchange (toFront.trans rotate) premiseDerivation
                  exact ⟨Derivation.parTail focused⟩
  | exchange order premise ih =>
      simp only [infer?] at accepted
      cases premiseResult : premise.infer? with
      | none => simp [premiseResult] at accepted
      | some premiseSequent =>
          simp [premiseResult] at accepted
          obtain ⟨premiseDerivation⟩ := ih premiseResult
          exact ⟨Derivation.exchange
            (reorder?_perm accepted) premiseDerivation⟩

def shiftEntry (offset : Nat) (entry : Formula × Vertex) : Formula × Vertex :=
  (entry.1, entry.2 + offset)

/-- Validate a cut-free derivation tree while desequentializing it. Failure is
limited to invalid occurrence positions or an invalid explicit exchange. -/
def build? : CutFreeDerivation → Option NetFragment
  | .axiom name positive =>
      let formula : Formula := .atom name positive
      some {
        formulas := #[formula, formula.dual]
        links := [.axiom 0 1]
        conclusions := [formula, formula.dual]
        roots := [0, 1] }
  | .tensor leftFocus rightFocus leftTree rightTree => do
      let leftFragment ← build? leftTree
      let rightFragment ← build? rightTree
      let (leftSelected, leftRemaining) ←
        pick? leftFragment.entries leftFocus
      let (rightSelected, rightRemaining) ←
        pick? rightFragment.entries rightFocus
      let offset := leftFragment.formulas.size
      let shiftedRightRemaining :=
        rightRemaining.map (shiftEntry offset)
      let shiftedRightRoot := rightSelected.2 + offset
      let combinedFormulas :=
        leftFragment.formulas ++ rightFragment.formulas
      let conclusionFormula :=
        Formula.tensor leftSelected.1 rightSelected.1
      let conclusionRoot := combinedFormulas.size
      let links := leftFragment.links ++
        rightFragment.links.map (·.shift offset) ++ [
          .tensor leftSelected.2 shiftedRightRoot conclusionRoot]
      pure <| NetFragment.ofEntries
        (combinedFormulas.push conclusionFormula) links
        ((conclusionFormula, conclusionRoot) ::
          (leftRemaining ++ shiftedRightRemaining))
  | .par leftFocus rightFocus premise => do
      let fragment ← build? premise
      let (leftSelected, afterLeft) ← pick? fragment.entries leftFocus
      let (rightSelected, remaining) ← pick? afterLeft rightFocus
      let conclusionFormula :=
        Formula.par leftSelected.1 rightSelected.1
      let conclusionRoot := fragment.formulas.size
      let links := fragment.links ++ [
        .par leftSelected.2 rightSelected.2 conclusionRoot]
      pure <| NetFragment.ofEntries
        (fragment.formulas.push conclusionFormula) links
        (remaining ++ [(conclusionFormula, conclusionRoot)])
  | .exchange order premise => do
      let fragment ← build? premise
      let reordered ← reorder? fragment.entries order
      pure <| NetFragment.ofEntries fragment.formulas fragment.links reordered

/-- Exact fragment equation for applying par to the last two boundary
entries. This is the certificate-building counterpart of `infer?_parLast`. -/
theorem build?_parLast
    {premise : CutFreeDerivation} {fragment : NetFragment}
    {context : List (Formula × Vertex)}
    {left right : Formula} {leftRoot rightRoot : Vertex}
    (premiseBuild : premise.build? = some fragment)
    (entriesEquation : fragment.entries =
      context ++ [(left, leftRoot), (right, rightRoot)]) :
    (CutFreeDerivation.par context.length context.length premise).build? =
      some (NetFragment.ofEntries
        (fragment.formulas.push (.par left right))
        (fragment.links ++ [
          .par leftRoot rightRoot fragment.formulas.size])
        (context ++ [(.par left right, fragment.formulas.size)])) := by
  simp [build?, premiseBuild, entriesEquation, pick?_append_cons]

/-- Exact fragment equation for tensor focused on the last boundary entry of
each child. The right context is shifted by the complete left formula-array
size, exactly as in the executable desequentializer. -/
theorem build?_tensorLast
    {leftTree rightTree : CutFreeDerivation}
    {leftFragment rightFragment : NetFragment}
    {leftContext rightContext : List (Formula × Vertex)}
    {left right : Formula} {leftRoot rightRoot : Vertex}
    (leftBuild : leftTree.build? = some leftFragment)
    (rightBuild : rightTree.build? = some rightFragment)
    (leftEntries : leftFragment.entries =
      leftContext ++ [(left, leftRoot)])
    (rightEntries : rightFragment.entries =
      rightContext ++ [(right, rightRoot)]) :
    (CutFreeDerivation.tensor leftContext.length rightContext.length
      leftTree rightTree).build? =
      some (NetFragment.ofEntries
        ((leftFragment.formulas ++ rightFragment.formulas).push
          (.tensor left right))
        (leftFragment.links ++
          rightFragment.links.map (·.shift leftFragment.formulas.size) ++ [
            .tensor leftRoot
              (rightRoot + leftFragment.formulas.size)
              (leftFragment.formulas ++ rightFragment.formulas).size])
        ((.tensor left right,
            (leftFragment.formulas ++ rightFragment.formulas).size) ::
          (leftContext ++ rightContext.map
            (shiftEntry leftFragment.formulas.size)))) := by
  simp [build?, leftBuild, rightBuild, leftEntries, rightEntries,
    pick?_append_cons]

def conclusions? (tree : CutFreeDerivation) : Option (List Formula) :=
  tree.build?.map NetFragment.conclusions

def desequentialize? (tree : CutFreeDerivation) : Option Certificate :=
  tree.build?.map NetFragment.toCertificate

/-- A certificate bundled with the kernel-checked fact that the executable
reference checker accepted it. -/
structure CheckedCertificate where
  certificate : Certificate
  accepted : certificate.check = true

def desequentializeChecked? (tree : CutFreeDerivation) :
    Option CheckedCertificate := do
  let certificate ← tree.desequentialize?
  if accepted : certificate.check = true then
    some ⟨certificate, accepted⟩
  else
    none

/-- End-to-end checked result connecting the inferred sequent, an independent
kernel-typed derivation, the proof-net boundary labels, and checker acceptance. -/
structure ElaboratedCertificate where
  sequent : List Formula
  derivation : Nonempty (Derivation sequent)
  certificate : Certificate
  conclusionLabels : certificate.conclusionFormulas? = some sequent
  accepted : certificate.check = true

/-- The strongest public v0.2+ entry point for first-order derivation trees.
Every returned value carries both sequent-calculus and proof-net evidence. -/
def elaborate? (tree : CutFreeDerivation) : Option ElaboratedCertificate :=
  match inferred : tree.infer? with
  | none => none
  | some sequent =>
      match tree.desequentialize? with
      | none => none
      | some certificate =>
          if labels : certificate.conclusionFormulas? = some sequent then
            if accepted : certificate.check = true then
              some {
                sequent
                derivation := tree.infer?_sound inferred
                certificate
                conclusionLabels := labels
                accepted }
            else
              none
          else
            none

def conclusionCount (tree : CutFreeDerivation) : Nat :=
  tree.conclusions?.map List.length |>.getD 0

def rotateOrder (length offset : Nat) : List Nat :=
  let indices := List.range length
  let pivot := if length == 0 then 0 else offset % length
  indices.drop pivot ++ indices.take pivot

/-- Deterministic broad-family generator used by the v0.2 dataset. Every
recursive step chooses arbitrary occurrences for tensor, optionally introduces
a par, and optionally records an explicit exchange. -/
def generate (seed : Nat) : Nat → CutFreeDerivation
  | 0 => .axiom s!"p{seed % 11}" (seed.testBit 0)
  | depth + 1 =>
      let left := generate (seed * 2 + 1) depth
      let right := generate (seed * 2 + 2) depth
      let leftCount := left.conclusionCount
      let rightCount := right.conclusionCount
      let tensorTree := .tensor
        (seed % leftCount) ((seed / 3) % rightCount) left right
      let tensorCount := tensorTree.conclusionCount
      let withPar :=
        if tensorCount > 1 && seed.testBit 1 then
          .par (seed % tensorCount)
            ((seed / 5) % (tensorCount - 1)) tensorTree
        else
          tensorTree
      let finalCount := withPar.conclusionCount
      if finalCount > 1 && seed % 3 == 0 then
        .exchange (rotateOrder finalCount (seed / 7 + 1)) withPar
      else
        withPar

end CutFreeDerivation

end ProofNetIR
