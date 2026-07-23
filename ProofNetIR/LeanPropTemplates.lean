import ProofNetIR.LeanPropBridge

namespace ProofNetIR.LeanProp.Templates

universe u

open Derivation

/-- Persistent contraction is required to use one hypothesis in both branches. -/
def duplicate (proposition : Prop) :
    Derivation.{0} [] [] (proposition → proposition ∧ proposition) :=
  .impIntro (.persistentContract (.andIntro
    (.persistentAxiom (proposition := proposition))
    (.persistentAxiom (proposition := proposition))))

/-- Persistent weakening explicitly discards the second assumption. -/
def discardSecond (left right : Prop) :
    Derivation.{0} [] [] (left → right → left) :=
  .impIntro (.impIntro (.persistentWeaken
    (.persistentAxiom (proposition := left))))

/-- Linear hypotheses are split exactly between the conjunction branches. -/
def linearPair (left right : Prop) :
    Derivation.{0} [] [left, right] (left ∧ right) :=
  .andIntro (.linearAxiom (proposition := left))
    (.linearAxiom (proposition := right))

/-- Linear modus ponens consumes the function and its argument once each. -/
def linearModusPonens (antecedent consequent : Prop) :
    Derivation.{0} [] [antecedent → consequent, antecedent] consequent :=
  .impElim (.linearAxiom (proposition := antecedent → consequent))
    (.linearAxiom (proposition := antecedent))

/-- Equality rewriting is a first-class proof-template node. -/
def rewrite {α : Type u} (left right : α) (motive : α → Prop) :
    Derivation [] [] (left = right → motive left → motive right) :=
  .impIntro (.impIntro (.persistentExchange (.swap _ _ [])
    (.eqRewrite
      (.persistentAxiom (proposition := left = right))
      (.persistentAxiom (proposition := motive left)))))

/-- Universal instantiation is reconstructed directly in the kernel. -/
def instantiate {α : Type u} (predicate : α → Prop) (term : α) :
    Derivation [] [] ((∀ value, predicate value) → predicate term) :=
  .impIntro (.forallElim term
    (.persistentAxiom (proposition := ∀ value, predicate value)))

/-- Existential introduction records its witness in the proof template. -/
def witness {α : Type u} (predicate : α → Prop) (term : α) :
    Derivation [] [] (predicate term → ∃ value, predicate value) :=
  .impIntro (.existsIntro term
    (.persistentAxiom (proposition := predicate term)))

theorem duplicate_proof (proposition : Prop) :
    proposition → proposition ∧ proposition :=
  (duplicate proposition).close

theorem discardSecond_proof (left right : Prop) : left → right → left :=
  (discardSecond left right).close

theorem linearPair_proof (left right : Prop)
    (leftProof : left) (rightProof : right) : left ∧ right :=
  (linearPair left right).toProof .nil (.cons leftProof (.cons rightProof .nil))

theorem linearModusPonens_proof (antecedent consequent : Prop)
    (functionProof : antecedent → consequent) (argumentProof : antecedent) :
    consequent :=
  (linearModusPonens antecedent consequent).toProof .nil
    (.cons functionProof (.cons argumentProof .nil))

theorem rewrite_proof {α : Type u} (left right : α) (motive : α → Prop) :
    left = right → motive left → motive right :=
  (rewrite left right motive).close

theorem instantiate_proof {α : Type u} (predicate : α → Prop) (term : α) :
    (∀ value, predicate value) → predicate term :=
  (instantiate predicate term).close

theorem witness_proof {α : Type u} (predicate : α → Prop) (term : α) :
    predicate term → ∃ value, predicate value :=
  (witness predicate term).close

end ProofNetIR.LeanProp.Templates
