import ProofNetIR.Checker
import ProofNetIR.Generate

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
def reorder? (values : List α) (order : List Nat) : Option (List α) :=
  if order.length == values.length &&
      order.eraseDups.length == order.length &&
      order.all (fun index => index < values.length) then
    order.mapM fun index => values[index]?
  else
    none

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
