namespace ProofNetIR

/-- A formula of unit-free multiplicative linear logic (MLL). -/
inductive Formula where
  | atom (name : String) (positive : Bool)
  | tensor (left right : Formula)
  | par (left right : Formula)
  deriving Repr, DecidableEq

namespace Formula

/-- Linear negation, including the De Morgan duality between tensor and par. -/
def dual : Formula → Formula
  | .atom name positive => .atom name (!positive)
  | .tensor left right => .par left.dual right.dual
  | .par left right => .tensor left.dual right.dual

@[simp] theorem dual_dual (formula : Formula) : formula.dual.dual = formula := by
  induction formula with
  | atom name positive => simp [dual]
  | tensor left right ihLeft ihRight => simp [dual, ihLeft, ihRight]
  | par left right ihLeft ihRight => simp [dual, ihLeft, ihRight]

def isAtom : Formula → Bool
  | .atom _ _ => true
  | _ => false

end Formula
end ProofNetIR
