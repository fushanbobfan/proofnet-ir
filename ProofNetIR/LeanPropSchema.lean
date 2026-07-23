import ProofNetIR.LeanPropBridge

namespace ProofNetIR.LeanProp.Schema

/-!
# First-order propositional proof-template schemas

This module supplies proposition-independent codes that can be generated and
eventually parsed from untrusted input. It intentionally covers only atoms,
ordinary conjunction, and ordinary implication. Equality and quantifier nodes
remain in the typed `LeanProp.Derivation` layer until a type-safe external term
language is specified.
-/

/-- Serializable proposition syntax for the first schema version. -/
inductive Formula where
  | atom (name : String)
  | and (left right : Formula)
  | imp (antecedent consequent : Formula)
  deriving Repr, DecidableEq, BEq

namespace Formula

/-- Interpret schema atoms under an arbitrary Lean proposition valuation. -/
def evaluate (valuation : String → Prop) : Formula → Prop
  | .atom name => valuation name
  | .and left right => left.evaluate valuation ∧ right.evaluate valuation
  | .imp antecedent consequent =>
      antecedent.evaluate valuation → consequent.evaluate valuation

end Formula

/-- Proof-relevant exchange syntax over proposition codes. -/
inductive ContextPermutation : List Formula → List Formula → Type where
  | nil : ContextPermutation [] []
  | cons {formula : Formula} {source target : List Formula} :
      ContextPermutation source target →
      ContextPermutation (formula :: source) (formula :: target)
  | swap (first second : Formula) (rest : List Formula) :
      ContextPermutation (second :: first :: rest)
        (first :: second :: rest)
  | trans {first middle last : List Formula} :
      ContextPermutation first middle → ContextPermutation middle last →
      ContextPermutation first last

namespace ContextPermutation

/-- Interpret a schema exchange as executable exchange data for Lean proofs. -/
def evaluate (valuation : String → Prop) {source target : List Formula} :
    ContextPermutation source target →
      LeanProp.ContextPermutation
        (source.map (Formula.evaluate valuation))
        (target.map (Formula.evaluate valuation))
  | .nil => .nil
  | .cons permutation => .cons (permutation.evaluate valuation)
  | .swap first second rest =>
      .swap (first.evaluate valuation) (second.evaluate valuation)
        (rest.map (Formula.evaluate valuation))
  | .trans first second =>
      .trans (first.evaluate valuation) (second.evaluate valuation)

end ContextPermutation

/-- Resource-explicit derivations over first-order proposition codes. The
indices make malformed rule applications unrepresentable after checking. -/
inductive Derivation : List Formula → List Formula → Formula → Type where
  | persistentAxiom {formula : Formula} : Derivation [formula] [] formula
  | linearAxiom {formula : Formula} : Derivation [] [formula] formula
  | persistentWeaken {persistent linear : List Formula} {extra goal : Formula} :
      Derivation persistent linear goal →
      Derivation (extra :: persistent) linear goal
  | persistentContract {persistent linear : List Formula}
      {shared goal : Formula} :
      Derivation (shared :: shared :: persistent) linear goal →
      Derivation (shared :: persistent) linear goal
  | persistentExchange {source target linear : List Formula} {goal : Formula} :
      ContextPermutation source target → Derivation source linear goal →
      Derivation target linear goal
  | linearExchange {persistent source target : List Formula} {goal : Formula} :
      ContextPermutation source target → Derivation persistent source goal →
      Derivation persistent target goal
  | andIntro {persistentLeft persistentRight linearLeft linearRight :
        List Formula} {left right : Formula} :
      Derivation persistentLeft linearLeft left →
      Derivation persistentRight linearRight right →
      Derivation (persistentLeft ++ persistentRight)
        (linearLeft ++ linearRight) (.and left right)
  | andElimLeft {persistent linear : List Formula} {left right : Formula} :
      Derivation persistent linear (.and left right) →
      Derivation persistent linear left
  | andElimRight {persistent linear : List Formula} {left right : Formula} :
      Derivation persistent linear (.and left right) →
      Derivation persistent linear right
  | impIntro {persistent linear : List Formula}
      {antecedent consequent : Formula} :
      Derivation (antecedent :: persistent) linear consequent →
      Derivation persistent linear (.imp antecedent consequent)
  | impElim {persistentFunction persistentArgument linearFunction linearArgument :
        List Formula} {antecedent consequent : Formula} :
      Derivation persistentFunction linearFunction (.imp antecedent consequent) →
      Derivation persistentArgument linearArgument antecedent →
      Derivation (persistentFunction ++ persistentArgument)
        (linearFunction ++ linearArgument) consequent

namespace Derivation

/-- Instantiate a first-order schema as a typed LeanProp derivation under any
atom valuation. This is the conservative bridge from generated data to the
kernel-interpreted calculus. -/
noncomputable def instantiate (valuation : String → Prop)
    {persistent linear : List Formula} {goal : Formula}
    (derivation : Derivation persistent linear goal) :
    LeanProp.Derivation.{0}
      (persistent.map (Formula.evaluate valuation))
      (linear.map (Formula.evaluate valuation))
      (goal.evaluate valuation) := by
  induction derivation with
  | persistentAxiom => exact .persistentAxiom
  | linearAxiom => exact .linearAxiom
  | persistentWeaken _ inductionHypothesis =>
      exact .persistentWeaken inductionHypothesis
  | persistentContract _ inductionHypothesis =>
      exact .persistentContract inductionHypothesis
  | persistentExchange permutation _ inductionHypothesis =>
      exact .persistentExchange (permutation.evaluate valuation)
        inductionHypothesis
  | linearExchange permutation _ inductionHypothesis =>
      exact .linearExchange (permutation.evaluate valuation)
        inductionHypothesis
  | andIntro _ _ leftIH rightIH =>
      simpa only [List.map_append, Formula.evaluate] using
        LeanProp.Derivation.andIntro leftIH rightIH
  | andElimLeft _ inductionHypothesis =>
      exact .andElimLeft inductionHypothesis
  | andElimRight _ inductionHypothesis =>
      exact .andElimRight inductionHypothesis
  | impIntro _ inductionHypothesis =>
      exact .impIntro inductionHypothesis
  | impElim _ _ functionIH argumentIH =>
      simpa only [List.map_append] using
        LeanProp.Derivation.impElim functionIH argumentIH

end Derivation

/-- An existentially packed, named schema derivation for generated corpora. -/
structure PackedDerivation where
  name : String
  persistent : List Formula
  linear : List Formula
  goal : Formula
  derivation : Derivation persistent linear goal

namespace PackedDerivation

/-- Every packed schema reconstructs a Lean proof for every valuation and
matching pair of proof environments. -/
theorem sound (packed : PackedDerivation) (valuation : String → Prop)
    (persistentValues : LeanProp.Assumptions
      (packed.persistent.map (Formula.evaluate valuation)))
    (linearValues : LeanProp.Assumptions
      (packed.linear.map (Formula.evaluate valuation))) :
    packed.goal.evaluate valuation :=
  (packed.derivation.instantiate valuation).toProof persistentValues linearValues

end PackedDerivation

end ProofNetIR.LeanProp.Schema
