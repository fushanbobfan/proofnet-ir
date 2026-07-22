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

/-- Number of multiplicative connectives in a formula. This is a strict rank
for following a premise occurrence to the conclusion of a tensor or par link. -/
def complexity : Formula → Nat
  | .atom _ _ => 0
  | .tensor left right => left.complexity + right.complexity + 1
  | .par left right => left.complexity + right.complexity + 1

theorem complexity_lt_tensor_left (left right : Formula) :
    left.complexity < (Formula.tensor left right).complexity := by
  simpa [complexity] using Nat.lt_succ_of_le (Nat.le_add_right left.complexity
    right.complexity)

theorem complexity_lt_tensor_right (left right : Formula) :
    right.complexity < (Formula.tensor left right).complexity := by
  simpa [complexity] using Nat.lt_succ_of_le (Nat.le_add_left right.complexity
    left.complexity)

theorem complexity_lt_par_left (left right : Formula) :
    left.complexity < (Formula.par left right).complexity := by
  simpa [complexity] using Nat.lt_succ_of_le (Nat.le_add_right left.complexity
    right.complexity)

theorem complexity_lt_par_right (left right : Formula) :
    right.complexity < (Formula.par left right).complexity := by
  simpa [complexity] using Nat.lt_succ_of_le (Nat.le_add_left right.complexity
    left.complexity)

end Formula
end ProofNetIR
