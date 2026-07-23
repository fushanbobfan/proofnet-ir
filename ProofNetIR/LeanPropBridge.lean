namespace ProofNetIR.LeanProp

universe u

/-!
# A resource-explicit bridge to Lean propositions

This module is deliberately separate from the proof-net certificate model.
It gives a small, kernel-interpreted two-context calculus whose judgments have
the shape `persistent ; linear |- goal`. Persistent weakening and contraction
are syntax; there are no corresponding linear constructors.

The connectives below are Lean's ordinary propositions. In particular, this
module does not identify `And` with MLL tensor, `Or` with par, or persistent
hypotheses with proof-net occurrences.
-/

/-- Heterogeneous proof values matching a proposition context exactly. -/
inductive Assumptions : List Prop → Type where
  | nil : Assumptions []
  | cons {proposition : Prop} {context : List Prop} :
      proposition → Assumptions context → Assumptions (proposition :: context)

/-- Proof-relevant permutation syntax. `List.Perm` lives in `Prop` and cannot
be eliminated into the heterogeneous `Assumptions` type; this Type-valued
witness records exactly the same exchange steps as executable data. -/
inductive ContextPermutation : List Prop → List Prop → Type where
  | nil : ContextPermutation [] []
  | cons {proposition : Prop} {source target : List Prop} :
      ContextPermutation source target →
      ContextPermutation (proposition :: source) (proposition :: target)
  | swap (first second : Prop) (rest : List Prop) :
      ContextPermutation (second :: first :: rest) (first :: second :: rest)
  | trans {first middle last : List Prop} :
      ContextPermutation first middle → ContextPermutation middle last →
      ContextPermutation first last

namespace ContextPermutation

/-- Reverse a proof-relevant context permutation. -/
def symm {left right : List Prop} :
    ContextPermutation left right → ContextPermutation right left
  | .nil => .nil
  | .cons permutation => .cons permutation.symm
  | .swap first second rest => .swap second first rest
  | .trans first second => .trans second.symm first.symm

/-- Forget proof-relevant permutation data to the proposition-level relation. -/
theorem toListPerm {left right : List Prop} :
    ContextPermutation left right → left.Perm right
  | .nil => .nil
  | .cons permutation => .cons _ permutation.toListPerm
  | .swap first second rest => .swap first second rest
  | .trans first second => first.toListPerm.trans second.toListPerm

end ContextPermutation

namespace Assumptions

/-- Concatenate proof environments in the same order as their contexts. -/
def append {left right : List Prop} :
    Assumptions left → Assumptions right → Assumptions (left ++ right)
  | .nil, rightValues => rightValues
  | .cons proof rest, rightValues => .cons proof (append rest rightValues)

/-- Split an environment at a statically known context boundary. -/
def split (left right : List Prop) :
    Assumptions (left ++ right) → Assumptions left × Assumptions right :=
  match left with
  | [] => fun values => (.nil, values)
  | _ :: tail => fun
      | .cons proof rest =>
          let (leftValues, rightValues) := split tail right rest
          (.cons proof leftValues, rightValues)

/-- Splitting an appended proof environment recovers the two inputs. -/
theorem split_append {left right : List Prop}
    (leftValues : Assumptions left) (rightValues : Assumptions right) :
    split left right (append leftValues rightValues) =
      (leftValues, rightValues) := by
  induction left with
  | nil =>
      cases leftValues
      rfl
  | cons _ tail inductionHypothesis =>
      cases leftValues with
      | cons proof rest =>
          simp [append, split, inductionHypothesis rest]

/-- Transport proof values along an explicit context permutation. -/
def permute {left right : List Prop} :
    ContextPermutation left right → Assumptions left → Assumptions right
  | .nil, .nil => .nil
  | .cons permutation, .cons proof rest =>
      .cons proof (permute permutation rest)
  | .swap _ _ _, .cons first (.cons second rest) =>
      .cons second (.cons first rest)
  | .trans first second, values =>
      permute second (permute first values)

/-- Executing an exchange and its explicit inverse restores the original
heterogeneous proof environment. -/
theorem permute_symm {left right : List Prop}
    (permutation : ContextPermutation left right)
    (values : Assumptions left) :
    permute permutation.symm (permute permutation values) = values := by
  induction permutation with
  | nil =>
      cases values
      rfl
  | cons permutation inductionHypothesis =>
      cases values with
      | cons proof rest =>
          simp [permute, ContextPermutation.symm,
            inductionHypothesis rest]
  | swap first second rest =>
      cases values with
      | cons secondProof tail =>
          cases tail with
          | cons firstProof tail => rfl
  | trans first second firstIH secondIH =>
      change permute first.symm
        (permute second.symm (permute second (permute first values))) = values
      rw [secondIH, firstIH]

end Assumptions

/-- A proof template indexed by an explicit persistent context, an exact-use
linear context, and a Lean proposition. Binary rules concatenate both input
contexts. Reusing a persistent assumption therefore produces two copies that
must be discharged by `persistentContract`; discarding one must pass through
`persistentWeaken`. No rule weakens or contracts the linear context. -/
inductive Derivation : List Prop → List Prop → Prop → Type (u + 1) where
  | persistentAxiom {proposition : Prop} :
      Derivation [proposition] [] proposition
  | linearAxiom {proposition : Prop} :
      Derivation [] [proposition] proposition
  | persistentWeaken {persistent linear : List Prop} {extra goal : Prop} :
      Derivation persistent linear goal →
      Derivation (extra :: persistent) linear goal
  | persistentContract {persistent linear : List Prop} {shared goal : Prop} :
      Derivation (shared :: shared :: persistent) linear goal →
      Derivation (shared :: persistent) linear goal
  | persistentExchange {source target linear : List Prop} {goal : Prop} :
      ContextPermutation source target → Derivation source linear goal →
      Derivation target linear goal
  | linearExchange {persistent source target : List Prop} {goal : Prop} :
      ContextPermutation source target → Derivation persistent source goal →
      Derivation persistent target goal
  | andIntro {persistentLeft persistentRight linearLeft linearRight : List Prop}
      {left right : Prop} :
      Derivation persistentLeft linearLeft left →
      Derivation persistentRight linearRight right →
      Derivation (persistentLeft ++ persistentRight)
        (linearLeft ++ linearRight) (left ∧ right)
  | andElimLeft {persistent linear : List Prop} {left right : Prop} :
      Derivation persistent linear (left ∧ right) →
      Derivation persistent linear left
  | andElimRight {persistent linear : List Prop} {left right : Prop} :
      Derivation persistent linear (left ∧ right) →
      Derivation persistent linear right
  | impIntro {persistent linear : List Prop} {antecedent consequent : Prop} :
      Derivation (antecedent :: persistent) linear consequent →
      Derivation persistent linear (antecedent → consequent)
  | impElim {persistentFunction persistentArgument linearFunction linearArgument :
        List Prop} {antecedent consequent : Prop} :
      Derivation persistentFunction linearFunction (antecedent → consequent) →
      Derivation persistentArgument linearArgument antecedent →
      Derivation (persistentFunction ++ persistentArgument)
        (linearFunction ++ linearArgument) consequent
  | eqRewrite {α : Type u} {left right : α} {motive : α → Prop}
      {persistentEquality persistentMotive linearEquality linearMotive :
        List Prop} :
      Derivation persistentEquality linearEquality (left = right) →
      Derivation persistentMotive linearMotive (motive left) →
      Derivation (persistentEquality ++ persistentMotive)
        (linearEquality ++ linearMotive) (motive right)
  | forallElim {α : Type u} {predicate : α → Prop}
      {persistent linear : List Prop} (term : α) :
      Derivation persistent linear (∀ value, predicate value) →
      Derivation persistent linear (predicate term)
  | existsIntro {α : Type u} {predicate : α → Prop}
      {persistent linear : List Prop} (witness : α) :
      Derivation persistent linear (predicate witness) →
      Derivation persistent linear (∃ value, predicate value)

namespace Derivation

/-- Number of linear-axiom leaves in a proof template. Persistent structural
rules do not alter this count, while binary rules add the disjoint branches. -/
noncomputable def linearAxiomCount {persistent linear : List Prop} {goal : Prop} :
    Derivation persistent linear goal → Nat := by
  intro derivation
  induction derivation with
  | persistentAxiom => exact 0
  | linearAxiom => exact 1
  | persistentWeaken _ count => exact count
  | persistentContract _ count => exact count
  | persistentExchange _ _ count => exact count
  | linearExchange _ _ count => exact count
  | andIntro _ _ leftCount rightCount => exact leftCount + rightCount
  | andElimLeft _ count => exact count
  | andElimRight _ count => exact count
  | impIntro _ count => exact count
  | impElim _ _ functionCount argumentCount =>
      exact functionCount + argumentCount
  | eqRewrite _ _ equalityCount motiveCount =>
      exact equalityCount + motiveCount
  | forallElim _ _ count => exact count
  | existsIntro _ _ count => exact count

/-- Every linear context occurrence is represented by exactly one linear
axiom leaf. This is the bridge's syntactic exact-use invariant. -/
theorem linearAxiomCount_eq_length {persistent linear : List Prop} {goal : Prop}
    (derivation : Derivation persistent linear goal) :
    derivation.linearAxiomCount = linear.length := by
  induction derivation with
  | persistentAxiom => rfl
  | linearAxiom => rfl
  | persistentWeaken _ inductionHypothesis => exact inductionHypothesis
  | persistentContract _ inductionHypothesis => exact inductionHypothesis
  | persistentExchange _ _ inductionHypothesis => exact inductionHypothesis
  | linearExchange permutation _ inductionHypothesis =>
      exact inductionHypothesis.trans permutation.toListPerm.length_eq
  | andIntro leftDerivation rightDerivation leftIH rightIH =>
      change leftDerivation.linearAxiomCount +
        rightDerivation.linearAxiomCount = _
      rw [leftIH, rightIH, List.length_append]
  | andElimLeft _ inductionHypothesis => exact inductionHypothesis
  | andElimRight _ inductionHypothesis => exact inductionHypothesis
  | impIntro _ inductionHypothesis => exact inductionHypothesis
  | impElim functionDerivation argumentDerivation functionIH argumentIH =>
      change functionDerivation.linearAxiomCount +
        argumentDerivation.linearAxiomCount = _
      rw [functionIH, argumentIH, List.length_append]
  | eqRewrite equalityDerivation motiveDerivation equalityIH motiveIH =>
      change equalityDerivation.linearAxiomCount +
        motiveDerivation.linearAxiomCount = _
      rw [equalityIH, motiveIH, List.length_append]
  | forallElim _ _ inductionHypothesis => exact inductionHypothesis
  | existsIntro _ _ inductionHypothesis => exact inductionHypothesis

/-- Interpret a resource-explicit derivation as an actual Lean proof term.
The function is total and checked by the Lean kernel. Its recursion is also the
soundness proof for every public proof-template constructor. -/
theorem toProof {persistent linear : List Prop} {goal : Prop}
    (derivation : Derivation persistent linear goal) :
    Assumptions persistent → Assumptions linear → goal := by
  induction derivation with
  | persistentAxiom =>
      intro persistentValues linearValues
      cases persistentValues with
      | cons proof rest =>
          cases rest
          cases linearValues
          exact proof
  | linearAxiom =>
      intro persistentValues linearValues
      cases persistentValues
      cases linearValues with
      | cons proof rest =>
          cases rest
          exact proof
  | persistentWeaken _ inductionHypothesis =>
      intro persistentValues linearValues
      cases persistentValues with
      | cons _ rest => exact inductionHypothesis rest linearValues
  | persistentContract _ inductionHypothesis =>
      intro persistentValues linearValues
      cases persistentValues with
      | cons sharedProof rest =>
          exact inductionHypothesis
            (.cons sharedProof (.cons sharedProof rest)) linearValues
  | persistentExchange permutation _ inductionHypothesis =>
      intro persistentValues linearValues
      exact inductionHypothesis
        (Assumptions.permute permutation.symm persistentValues) linearValues
  | linearExchange permutation _ inductionHypothesis =>
      intro persistentValues linearValues
      exact inductionHypothesis persistentValues
        (Assumptions.permute permutation.symm linearValues)
  | andIntro _ _ leftIH rightIH =>
      intro persistentValues linearValues
      let (persistentLeftValues, persistentRightValues) :=
        Assumptions.split _ _ persistentValues
      let (linearLeftValues, linearRightValues) :=
        Assumptions.split _ _ linearValues
      exact ⟨leftIH persistentLeftValues linearLeftValues,
        rightIH persistentRightValues linearRightValues⟩
  | andElimLeft _ inductionHypothesis =>
      intro persistentValues linearValues
      exact (inductionHypothesis persistentValues linearValues).1
  | andElimRight _ inductionHypothesis =>
      intro persistentValues linearValues
      exact (inductionHypothesis persistentValues linearValues).2
  | impIntro _ inductionHypothesis =>
      intro persistentValues linearValues antecedentProof
      exact inductionHypothesis (.cons antecedentProof persistentValues)
        linearValues
  | impElim _ _ functionIH argumentIH =>
      intro persistentValues linearValues
      let (persistentFunctionValues, persistentArgumentValues) :=
        Assumptions.split _ _ persistentValues
      let (linearFunctionValues, linearArgumentValues) :=
        Assumptions.split _ _ linearValues
      exact functionIH persistentFunctionValues linearFunctionValues
        (argumentIH persistentArgumentValues linearArgumentValues)
  | eqRewrite _ _ equalityIH motiveIH =>
      intro persistentValues linearValues
      let (persistentEqualityValues, persistentMotiveValues) :=
        Assumptions.split _ _ persistentValues
      let (linearEqualityValues, linearMotiveValues) :=
        Assumptions.split _ _ linearValues
      exact equalityIH persistentEqualityValues linearEqualityValues ▸
        motiveIH persistentMotiveValues linearMotiveValues
  | forallElim term _ inductionHypothesis =>
      intro persistentValues linearValues
      exact inductionHypothesis persistentValues linearValues term
  | existsIntro witness _ inductionHypothesis =>
      intro persistentValues linearValues
      exact ⟨witness, inductionHypothesis persistentValues linearValues⟩

/-- A closed bridge derivation reconstructs a closed Lean theorem. -/
theorem close {goal : Prop} (derivation : Derivation [] [] goal) : goal :=
  derivation.toProof .nil .nil

end Derivation

end ProofNetIR.LeanProp
