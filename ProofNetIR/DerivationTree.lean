import Lean.Elab.Tactic.Omega
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

/-- Formula labels and occurrence roots are maintained in lockstep by every
fragment constructor used by the desequentializer. -/
def Balanced (fragment : NetFragment) : Prop :=
  fragment.conclusions.length = fragment.roots.length

theorem ofEntries_balanced (formulas : Array Formula) (links : List Link)
    (entries : List (Formula × Vertex)) :
    (ofEntries formulas links entries).Balanced := by
  simp [Balanced, ofEntries]

theorem entries_map_fst (fragment : NetFragment)
    (balanced : fragment.Balanced) :
    fragment.entries.map Prod.fst = fragment.conclusions := by
  unfold entries
  exact List.map_fst_zip (Nat.le_of_eq balanced)

theorem entries_map_snd (fragment : NetFragment)
    (balanced : fragment.Balanced) :
    fragment.entries.map Prod.snd = fragment.roots := by
  unfold entries
  exact List.map_snd_zip (Nat.le_of_eq balanced.symm)

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

/-- If duplicate erasure preserves the full list length, the original list
contained no duplicates. This bridges Boolean permutation guards to `Nodup`. -/
theorem nodup_of_eraseDups_length_eq [BEq α] [LawfulBEq α]
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

private theorem perm_of_nodup_subset_length [BEq α] [LawfulBEq α]
    {left right : List α}
    (leftNodup : left.Nodup) (rightNodup : right.Nodup)
    (subset : left ⊆ right) (sameLength : left.length = right.length) :
    left.Perm right := by
  induction left generalizing right with
  | nil =>
      have : right = [] := List.eq_nil_of_length_eq_zero sameLength.symm
      subst right
      exact .refl []
  | cons head tail ih =>
      have headMembership : head ∈ right := subset (by simp)
      have tailNodup := (List.nodup_cons.mp leftNodup).2
      have headFresh := (List.nodup_cons.mp leftNodup).1
      have erasedNodup := rightNodup.erase head
      have tailSubset : tail ⊆ right.erase head := by
        intro value membership
        apply (List.mem_erase_of_ne (b := head) (by
          intro same
          subst value
          exact headFresh membership)).mpr
        exact subset (by simp [membership])
      have tailLength : tail.length = (right.erase head).length := by
        rw [List.length_erase_of_mem headMembership]
        have rightPositive := List.length_pos_of_mem headMembership
        have totalLength : tail.length + 1 = right.length := by
          simpa [Nat.add_comm] using sameLength
        omega
      exact (ih tailNodup erasedNodup tailSubset tailLength).cons head |>.trans
        (List.perm_cons_erase headMembership).symm

private theorem mapM_some_perm {function : α → Option β}
    {left right : List α} (permutation : left.Perm right)
    {leftResult : List β}
    (accepted : left.mapM function = some leftResult) :
    ∃ rightResult : List β,
      right.mapM function = some rightResult ∧
        leftResult.Perm rightResult := by
  induction permutation generalizing leftResult
  case nil =>
      simp at accepted
      subst leftResult
      exact ⟨[], rfl, .refl []⟩
  case cons head leftTail rightTail permutation ih =>
      simp only [List.mapM_cons] at accepted ⊢
      cases headResult : function head with
      | none => simp [headResult] at accepted
      | some mappedHead =>
          cases leftTailResult : List.mapM function leftTail with
          | none => simp [headResult, leftTailResult] at accepted
          | some mappedTail =>
              simp [headResult, leftTailResult] at accepted
              subst leftResult
              rcases ih leftTailResult with
                ⟨rightTail, rightEquation, tailPermutation⟩
              refine ⟨mappedHead :: rightTail, ?_,
                tailPermutation.cons mappedHead⟩
              simp [rightEquation]
  case swap first second tail =>
      simp only [List.mapM_cons] at accepted ⊢
      cases firstResult : function first with
      | none => simp [firstResult] at accepted
      | some mappedFirst =>
          cases secondResult : function second with
          | none => simp [firstResult, secondResult] at accepted
          | some mappedSecond =>
              cases tailResult : tail.mapM function with
              | none =>
                  simp [firstResult, secondResult, tailResult] at accepted
              | some mappedTail =>
                  simp [firstResult, secondResult, tailResult] at accepted
                  subst leftResult
                  refine ⟨mappedFirst :: mappedSecond :: mappedTail, ?_, ?_⟩
                  · simp
                  · exact .swap mappedFirst mappedSecond mappedTail
  case trans firstPermutation secondPermutation firstIH secondIH =>
      rcases firstIH accepted with
        ⟨middleResult, middleEquation, firstResultPermutation⟩
      rcases secondIH middleEquation with
        ⟨rightResult, rightEquation, secondResultPermutation⟩
      exact ⟨rightResult, rightEquation,
        firstResultPermutation.trans secondResultPermutation⟩

private theorem range_mapM_getElem? (values : List α) :
    (List.range values.length).mapM (fun index => values[index]?) =
      some values := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.length_cons]
      rw [List.range_succ_eq_map]
      simp only [List.mapM_cons, List.getElem?_cons_zero, List.mapM_map]
      have shifted :
          (List.range tail.length).mapM
              ((fun index => (head :: tail)[index]?) ∘ Nat.succ) =
            some tail := by
        have functionEquation :
            ((fun index => (head :: tail)[index]?) ∘ Nat.succ) =
              (fun index => tail[index]?) := by
          funext index
          rfl
        rw [functionEquation]
        exact ih
      rw [shifted]
      rfl

/-- Apply an explicit permutation written as original occurrence indices.
Malformed, duplicated, missing, or out-of-bounds orders are rejected. -/
def reorderCandidate? (values : List α) (order : List Nat) : Option (List α) :=
  if order.length == values.length &&
      order.eraseDups.length == order.length &&
      order.all (fun index => index < values.length) then
    order.mapM fun index => values[index]?
  else
    none

/-- Every accepted index candidate is already a genuine permutation of the
input occurrences. Thus the later element-level `Perm` guard is redundant,
including when projected formula labels contain duplicates. -/
theorem reorderCandidate?_perm [DecidableEq α]
    {values reordered : List α} {order : List Nat}
    (accepted : reorderCandidate? values order = some reordered) :
    values.Perm reordered := by
  unfold reorderCandidate? at accepted
  split at accepted
  · rename_i guard
    have guardParts :
        (order.length = values.length ∧
          order.eraseDups.length = order.length) ∧
          ∀ index ∈ order, index < values.length := by
      simpa [Bool.and_eq_true, List.all_eq_true] using guard
    rcases guardParts with ⟨⟨lengthEquation, eraseLength⟩, bounded⟩
    have orderNodup : order.Nodup :=
      nodup_of_eraseDups_length_eq eraseLength
    have rangeNodup : (List.range values.length).Nodup :=
      List.nodup_range
    have orderSubset : order ⊆ List.range values.length := by
      intro index membership
      simp only [List.mem_range]
      exact bounded index membership
    have orderPermutation : order.Perm (List.range values.length) :=
      perm_of_nodup_subset_length orderNodup rangeNodup orderSubset
        (by simpa using lengthEquation)
    rcases mapM_some_perm orderPermutation accepted with
      ⟨rangeResult, rangeEquation, resultPermutation⟩
    rw [range_mapM_getElem?] at rangeEquation
    simp at rangeEquation
    subst rangeResult
    exact resultPermutation.symm
  · simp at accepted

/-- Reordering additionally validates the mathematical permutation relation.
This redundant check exposes a direct proof boundary for downstream theorems. -/
def reorder? [DecidableEq α] (values : List α) (order : List Nat) :
    Option (List α) := do
  let reordered ← reorderCandidate? values order
  if values.Perm reordered then some reordered else none

/-- The explicit index guard already implies the redundant element-level
permutation check, so both executable reorder layers agree exactly. -/
theorem reorder?_eq_reorderCandidate? [DecidableEq α]
    (values : List α) (order : List Nat) :
    reorder? values order = reorderCandidate? values order := by
  unfold reorder?
  cases accepted : reorderCandidate? values order with
  | none => rfl
  | some reordered =>
      change (if values.Perm reordered then some reordered else none) =
        some reordered
      rw [if_pos (reorderCandidate?_perm accepted)]

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

/-- Selecting an occurrence and then forgetting auxiliary data is the same as
first forgetting that data and selecting at the same position. -/
theorem pick?_map (function : α → β) (values : List α) (index : Nat) :
    pick? (values.map function) index =
      (pick? values index).map fun selected =>
        (function selected.1, selected.2.map function) := by
  induction values generalizing index with
  | nil => rfl
  | cons head tail ih =>
      cases index with
      | zero => rfl
      | succ prior =>
          simp only [List.map_cons, pick?]
          rw [ih]
          cases pick? tail prior <;> rfl

/-- A successful selection after projection comes from a unique occurrence
selection before projection, even when projected labels are duplicated. -/
theorem pick?_exists_of_map_eq_some (function : α → β)
    {values : List α} {index : Nat} {selected : β}
    {remaining : List β}
    (accepted : pick? (values.map function) index =
      some (selected, remaining)) :
    ∃ actualSelected : α, ∃ actualRemaining : List α,
      pick? values index = some (actualSelected, actualRemaining) ∧
        function actualSelected = selected ∧
        actualRemaining.map function = remaining := by
  rw [pick?_map] at accepted
  cases actual : pick? values index with
  | none => simp [actual] at accepted
  | some pair =>
      rcases pair with ⟨actualSelected, actualRemaining⟩
      simp [actual] at accepted
      rcases accepted with ⟨selectedEquation, remainingEquation⟩
      exact ⟨actualSelected, actualRemaining, rfl,
        selectedEquation, remainingEquation⟩

private theorem mapM_getElem?_map (function : α → β)
    (values : List α) (indices : List Nat) :
    indices.mapM (fun index => (values.map function)[index]?) =
      (indices.mapM fun index => values[index]?).map (List.map function) := by
  induction indices with
  | nil => rfl
  | cons index tail ih =>
      simp only [List.getElem?_map] at ih
      simp only [List.mapM_cons, List.getElem?_map]
      cases headEquation : values[index]? with
      | none => simp
      | some value =>
          cases tailEquation : tail.mapM (fun index => values[index]?) with
          | none =>
              have mappedTail :
                  tail.mapM (fun index => Option.map function values[index]?) =
                    none := by
                rw [ih, tailEquation]
                rfl
              simp [mappedTail]
          | some remaining =>
              have mappedTail :
                  tail.mapM (fun index => Option.map function values[index]?) =
                    some (remaining.map function) := by
                rw [ih, tailEquation]
                rfl
              simp [mappedTail]

/-- Reorder-candidate construction commutes with pointwise projection. -/
theorem reorderCandidate?_map (function : α → β)
    (values : List α) (order : List Nat) :
    reorderCandidate? (values.map function) order =
      (reorderCandidate? values order).map (List.map function) := by
  unfold reorderCandidate?
  simp only [List.length_map]
  split
  · exact mapM_getElem?_map function values order
  · rfl

/-- Any accepted explicit reorder remains accepted after a pointwise
projection, and produces the projected target in the same occurrence order. -/
theorem reorder?_map_of_eq_some [DecidableEq α] [DecidableEq β]
    (function : α → β) {values reordered : List α} {order : List Nat}
    (accepted : reorder? values order = some reordered) :
    reorder? (values.map function) order = some (reordered.map function) := by
  unfold reorder? at accepted ⊢
  cases candidateEquation : reorderCandidate? values order with
  | none => simp [candidateEquation] at accepted
  | some candidate =>
      by_cases permutation : values.Perm candidate
      · have candidateSame : candidate = reordered := by
          simpa [candidateEquation, permutation] using accepted
        subst candidate
        have mappedCandidate :
            reorderCandidate? (values.map function) order =
              some (reordered.map function) := by
          rw [reorderCandidate?_map, candidateEquation]
          rfl
        simp [mappedCandidate, permutation.map function]
      · simp [candidateEquation, permutation] at accepted

/-- A successful reorder after projection lifts to the same occurrence-index
reorder before projection. This direction does not require projection to be
injective because the index guard, rather than formula equality, controls the
permutation. -/
theorem reorder?_exists_of_map_eq_some [DecidableEq α] [DecidableEq β]
    (function : α → β) {values : List α} {mapped : List β}
    {order : List Nat}
    (accepted : reorder? (values.map function) order = some mapped) :
    ∃ reordered : List α,
      reorder? values order = some reordered ∧
        reordered.map function = mapped := by
  rw [reorder?_eq_reorderCandidate?] at accepted ⊢
  rw [reorderCandidate?_map] at accepted
  cases candidate : reorderCandidate? values order with
  | none => simp [candidate] at accepted
  | some reordered =>
      simp [candidate] at accepted
      subst mapped
      exact ⟨reordered, rfl, rfl⟩

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

/-- Every successfully built fragment keeps formula labels and occurrence
roots at the same boundary length. -/
theorem build?_balanced {tree : CutFreeDerivation} {fragment : NetFragment}
    (equation : tree.build? = some fragment) : fragment.Balanced := by
  induction tree generalizing fragment with
  | «axiom» name positive =>
      simp [build?] at equation
      subst fragment
      rfl
  | tensor leftFocus rightFocus leftTree rightTree leftIH rightIH =>
      simp only [build?] at equation
      cases leftEquation : leftTree.build? with
      | none => simp [leftEquation] at equation
      | some leftFragment =>
          cases rightEquation : rightTree.build? with
          | none => simp [leftEquation, rightEquation] at equation
          | some rightFragment =>
              cases leftPick : pick? leftFragment.entries leftFocus with
              | none =>
                  simp [leftEquation, rightEquation, leftPick] at equation
              | some leftPair =>
                  cases rightPick : pick? rightFragment.entries rightFocus with
                  | none =>
                      simp [leftEquation, rightEquation, rightPick]
                        at equation
                  | some rightPair =>
                      simp [leftEquation, rightEquation, leftPick, rightPick]
                        at equation
                      subst fragment
                      exact NetFragment.ofEntries_balanced _ _ _
  | par leftFocus rightFocus premise ih =>
      simp only [build?] at equation
      cases premiseEquation : premise.build? with
      | none => simp [premiseEquation] at equation
      | some premiseFragment =>
          cases leftPick : pick? premiseFragment.entries leftFocus with
          | none => simp [premiseEquation, leftPick] at equation
          | some leftPair =>
              cases rightPick : pick? leftPair.2 rightFocus with
              | none =>
                  simp [premiseEquation, leftPick, rightPick] at equation
              | some rightPair =>
                  simp [premiseEquation, leftPick, rightPick] at equation
                  subst fragment
                  exact NetFragment.ofEntries_balanced _ _ _
  | exchange order premise ih =>
      simp only [build?] at equation
      cases premiseEquation : premise.build? with
      | none => simp [premiseEquation] at equation
      | some premiseFragment =>
          cases reorderedEquation : reorder? premiseFragment.entries order with
          | none =>
              simp [premiseEquation, reorderedEquation] at equation
          | some reordered =>
              simp [premiseEquation, reorderedEquation] at equation
              subst fragment
              exact NetFragment.ofEntries_balanced _ _ _

/-- The independent formula inference pass agrees exactly with the formula
boundary of every successfully built fragment. -/
theorem infer?_of_build? {tree : CutFreeDerivation} {fragment : NetFragment}
    (equation : tree.build? = some fragment) :
    tree.infer? = some fragment.conclusions := by
  induction tree generalizing fragment with
  | «axiom» name positive =>
      simp [build?] at equation
      subst fragment
      rfl
  | tensor leftFocus rightFocus leftTree rightTree leftIH rightIH =>
      simp only [build?] at equation
      cases leftEquation : leftTree.build? with
      | none => simp [leftEquation] at equation
      | some leftFragment =>
          cases rightEquation : rightTree.build? with
          | none => simp [leftEquation, rightEquation] at equation
          | some rightFragment =>
              cases leftPick : pick? leftFragment.entries leftFocus with
              | none =>
                  simp [leftEquation, rightEquation, leftPick] at equation
              | some leftPair =>
                  rcases leftPair with ⟨leftSelected, leftRemaining⟩
                  cases rightPick : pick? rightFragment.entries rightFocus with
                  | none =>
                      simp [leftEquation, rightEquation, rightPick]
                        at equation
                  | some rightPair =>
                      rcases rightPair with ⟨rightSelected, rightRemaining⟩
                      simp [leftEquation, rightEquation, leftPick, rightPick]
                        at equation
                      subst fragment
                      have leftEntries := leftFragment.entries_map_fst
                        (build?_balanced leftEquation)
                      have rightEntries := rightFragment.entries_map_fst
                        (build?_balanced rightEquation)
                      have leftFormulaPick :
                          pick? leftFragment.conclusions leftFocus =
                            some (leftSelected.1,
                              leftRemaining.map Prod.fst) := by
                        rw [← leftEntries, pick?_map, leftPick]
                        rfl
                      have rightFormulaPick :
                          pick? rightFragment.conclusions rightFocus =
                            some (rightSelected.1,
                              rightRemaining.map Prod.fst) := by
                        rw [← rightEntries, pick?_map, rightPick]
                        rfl
                      simp [infer?, leftIH leftEquation, rightIH rightEquation,
                        leftFormulaPick, rightFormulaPick,
                        NetFragment.ofEntries, shiftEntry, List.map_append]
  | par leftFocus rightFocus premise ih =>
      simp only [build?] at equation
      cases premiseEquation : premise.build? with
      | none => simp [premiseEquation] at equation
      | some premiseFragment =>
          cases leftPick : pick? premiseFragment.entries leftFocus with
          | none => simp [premiseEquation, leftPick] at equation
          | some leftPair =>
              rcases leftPair with ⟨leftSelected, afterLeft⟩
              cases rightPick : pick? afterLeft rightFocus with
              | none =>
                  simp [premiseEquation, leftPick, rightPick] at equation
              | some rightPair =>
                  rcases rightPair with ⟨rightSelected, remaining⟩
                  simp [premiseEquation, leftPick, rightPick] at equation
                  subst fragment
                  have premiseEntries := premiseFragment.entries_map_fst
                    (build?_balanced premiseEquation)
                  have leftFormulaPick :
                      pick? premiseFragment.conclusions leftFocus =
                        some (leftSelected.1, afterLeft.map Prod.fst) := by
                    rw [← premiseEntries, pick?_map, leftPick]
                    rfl
                  have rightFormulaPick :
                      pick? (afterLeft.map Prod.fst) rightFocus =
                        some (rightSelected.1, remaining.map Prod.fst) := by
                    rw [pick?_map, rightPick]
                    rfl
                  simp [infer?, ih premiseEquation, leftFormulaPick,
                    rightFormulaPick, NetFragment.ofEntries, List.map_append]
  | exchange order premise ih =>
      simp only [build?] at equation
      cases premiseEquation : premise.build? with
      | none => simp [premiseEquation] at equation
      | some premiseFragment =>
          cases reorderedEquation : reorder? premiseFragment.entries order with
          | none =>
              simp [premiseEquation, reorderedEquation] at equation
          | some reordered =>
              simp [premiseEquation, reorderedEquation] at equation
              subst fragment
              have premiseEntries := premiseFragment.entries_map_fst
                (build?_balanced premiseEquation)
              have formulaReorder := reorder?_map_of_eq_some
                Prod.fst reorderedEquation
              rw [premiseEntries] at formulaReorder
              simp [infer?, ih premiseEquation, formulaReorder,
                NetFragment.ofEntries]

/-- Formula-level validation and occurrence-aware fragment construction have
the same success domain. In particular, a first-order rule tree accepted by
`infer?` cannot later fail in `build?`, including exchanges over duplicate
formula labels. -/
theorem build?_exists_of_infer?
    {tree : CutFreeDerivation} {sequent : List Formula}
    (accepted : tree.infer? = some sequent) :
    ∃ fragment : NetFragment, tree.build? = some fragment := by
  induction tree generalizing sequent with
  | «axiom» name positive =>
      exact ⟨_, rfl⟩
  | tensor leftFocus rightFocus leftTree rightTree leftIH rightIH =>
      simp only [infer?] at accepted
      cases leftInference : leftTree.infer? with
      | none => simp [leftInference] at accepted
      | some leftSequent =>
          cases rightInference : rightTree.infer? with
          | none => simp [leftInference, rightInference] at accepted
          | some rightSequent =>
              cases leftFormulaPick : pick? leftSequent leftFocus with
              | none =>
                  simp [leftInference, rightInference, leftFormulaPick]
                    at accepted
              | some leftPair =>
                  rcases leftPair with ⟨leftFormula, leftContext⟩
                  cases rightFormulaPick : pick? rightSequent rightFocus with
                  | none =>
                      simp [leftInference, rightInference, rightFormulaPick]
                        at accepted
                  | some rightPair =>
                      rcases rightPair with ⟨rightFormula, rightContext⟩
                      rcases leftIH leftInference with
                        ⟨leftFragment, leftBuild⟩
                      rcases rightIH rightInference with
                        ⟨rightFragment, rightBuild⟩
                      have leftConclusions :
                          leftFragment.conclusions = leftSequent := by
                        have agreement := infer?_of_build? leftBuild
                        rw [leftInference] at agreement
                        exact Option.some.inj agreement |>.symm
                      have rightConclusions :
                          rightFragment.conclusions = rightSequent := by
                        have agreement := infer?_of_build? rightBuild
                        rw [rightInference] at agreement
                        exact Option.some.inj agreement |>.symm
                      have leftEntries := leftFragment.entries_map_fst
                        (build?_balanced leftBuild)
                      have rightEntries := rightFragment.entries_map_fst
                        (build?_balanced rightBuild)
                      have projectedLeftPick :
                          pick? (leftFragment.entries.map Prod.fst) leftFocus =
                            some (leftFormula, leftContext) := by
                        rw [leftEntries, leftConclusions]
                        exact leftFormulaPick
                      have projectedRightPick :
                          pick? (rightFragment.entries.map Prod.fst) rightFocus =
                            some (rightFormula, rightContext) := by
                        rw [rightEntries, rightConclusions]
                        exact rightFormulaPick
                      rcases pick?_exists_of_map_eq_some Prod.fst
                          projectedLeftPick with
                        ⟨leftSelected, leftRemaining, leftPick, _, _⟩
                      rcases pick?_exists_of_map_eq_some Prod.fst
                          projectedRightPick with
                        ⟨rightSelected, rightRemaining, rightPick, _, _⟩
                      simp [build?, leftBuild, rightBuild, leftPick, rightPick]
  | par leftFocus rightFocus premise ih =>
      simp only [infer?] at accepted
      cases premiseInference : premise.infer? with
      | none => simp [premiseInference] at accepted
      | some premiseSequent =>
          cases leftFormulaPick : pick? premiseSequent leftFocus with
          | none => simp [premiseInference, leftFormulaPick] at accepted
          | some leftPair =>
              rcases leftPair with ⟨leftFormula, afterLeft⟩
              cases rightFormulaPick : pick? afterLeft rightFocus with
              | none =>
                  simp [premiseInference, leftFormulaPick, rightFormulaPick]
                    at accepted
              | some rightPair =>
                  rcases rightPair with ⟨rightFormula, context⟩
                  rcases ih premiseInference with ⟨fragment, premiseBuild⟩
                  have conclusions : fragment.conclusions = premiseSequent := by
                    have agreement := infer?_of_build? premiseBuild
                    rw [premiseInference] at agreement
                    exact Option.some.inj agreement |>.symm
                  have entries := fragment.entries_map_fst
                    (build?_balanced premiseBuild)
                  have projectedLeftPick :
                      pick? (fragment.entries.map Prod.fst) leftFocus =
                        some (leftFormula, afterLeft) := by
                    rw [entries, conclusions]
                    exact leftFormulaPick
                  rcases pick?_exists_of_map_eq_some Prod.fst
                      projectedLeftPick with
                    ⟨leftSelected, afterLeftEntries, leftPick,
                      leftFormulaEquation, afterLeftFormulas⟩
                  have projectedRightPick :
                      pick? (afterLeftEntries.map Prod.fst) rightFocus =
                        some (rightFormula, context) := by
                    rw [afterLeftFormulas]
                    exact rightFormulaPick
                  rcases pick?_exists_of_map_eq_some Prod.fst
                      projectedRightPick with
                    ⟨rightSelected, remaining, rightPick, _, _⟩
                  simp [build?, premiseBuild, leftPick, rightPick]
  | exchange order premise ih =>
      simp only [infer?] at accepted
      cases premiseInference : premise.infer? with
      | none => simp [premiseInference] at accepted
      | some premiseSequent =>
          simp [premiseInference] at accepted
          rcases ih premiseInference with ⟨fragment, premiseBuild⟩
          have conclusions : fragment.conclusions = premiseSequent := by
            have agreement := infer?_of_build? premiseBuild
            rw [premiseInference] at agreement
            exact Option.some.inj agreement |>.symm
          have entries := fragment.entries_map_fst
            (build?_balanced premiseBuild)
          have projectedReorder :
              reorder? (fragment.entries.map Prod.fst) order =
                some sequent := by
            rw [entries, conclusions]
            exact accepted
          rcases reorder?_exists_of_map_eq_some Prod.fst projectedReorder with
            ⟨reordered, entryReorder, _⟩
          simp [build?, premiseBuild, entryReorder]

/-- Exact synchronization of the independent formula pass and the
occurrence-aware builder. -/
theorem infer?_eq_some_iff_build?_conclusions
    {tree : CutFreeDerivation} {sequent : List Formula} :
    tree.infer? = some sequent ↔
      ∃ fragment : NetFragment,
        tree.build? = some fragment ∧ fragment.conclusions = sequent := by
  constructor
  · intro accepted
    rcases build?_exists_of_infer? accepted with ⟨fragment, build⟩
    have agreement := infer?_of_build? build
    rw [accepted] at agreement
    exact ⟨fragment, build, Option.some.inj agreement |>.symm⟩
  · rintro ⟨fragment, build, rfl⟩
    exact infer?_of_build? build

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

/-- Build a proof-net certificate from a validated first-order rule tree.
Malformed resource positions or exchanges return `none`. -/
def desequentialize? (tree : CutFreeDerivation) : Option Certificate :=
  tree.build?.map NetFragment.toCertificate

/-- Expose the internal fragment witnessed by a successful public
desequentialization result. -/
theorem build?_exists_of_desequentialize?
    {tree : CutFreeDerivation} {certificate : Certificate}
    (equation : tree.desequentialize? = some certificate) :
    ∃ fragment : NetFragment,
      tree.build? = some fragment ∧
        fragment.toCertificate = certificate := by
  unfold desequentialize? at equation
  cases buildEquation : tree.build? with
  | none => simp [buildEquation] at equation
  | some fragment =>
      simp [buildEquation] at equation
      subst certificate
      exact ⟨fragment, rfl, rfl⟩

/-- A certificate bundled with the kernel-checked fact that the executable
reference checker accepted it. -/
structure CheckedCertificate where
  certificate : Certificate
  accepted : certificate.check = true

/-- Desequentialize and retain the result only when the reference proof-net
checker accepts it. -/
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

/-- Backward-compatible root-namespace bridge used by the sequentialization
proofs and downstream code. -/
theorem nodup_of_eraseDups_length_eq [BEq α] [LawfulBEq α]
    {values : List α}
    (sameLength : values.eraseDups.length = values.length) :
    values.Nodup :=
  CutFreeDerivation.nodup_of_eraseDups_length_eq sameLength

end ProofNetIR
