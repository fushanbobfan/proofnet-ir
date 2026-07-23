import ProofNetIR

open ProofNetIR

namespace ProofNetIRTutorialSmoke

universe u

def p : Formula := .atom "p" true
def pDual : Formula := .atom "p" false

def axiomCertificate : Certificate where
  formulas := #[p, pDual]
  links := [.axiom 0 1]
  conclusions := [0, 1]

example : axiomCertificate.check = true := by native_decide

example : axiomCertificate.DeclarativelyCorrect :=
  axiomCertificate.check_iff_declarativelyCorrect.mp (by native_decide)

def checkedAxiomCertificate : CutFreeDerivation.CheckedCertificate :=
  ⟨axiomCertificate, by native_decide⟩

example : checkedAxiomCertificate.sameProofNet? checkedAxiomCertificate = true := by
  native_decide

example : checkedAxiomCertificate.certificate.ProofNetEquivalent
    checkedAxiomCertificate.certificate :=
  CutFreeDerivation.CheckedCertificate.sameProofNet?_eq_true_iff.mp
    (by native_decide)

def parsed := Certificate.checkedFromString axiomCertificate.canonicalString

example : parsed.isOk = true := by native_decide

def reconstructed := axiomCertificate.sequentialize

example : reconstructed.isOk = true := by native_decide

example : ∃ result : ExecutableSequentializationResult axiomCertificate,
    axiomCertificate.sequentialize = .ok result :=
  axiomCertificate.sequentialize_complete (by native_decide)

def tree : CutFreeDerivation := .axiom "p" true

example : tree.infer? = some [p, pDual] := by native_decide
example : tree.desequentializeChecked?.isSome = true := by native_decide
example : tree.elaborate?.isSome = true := by native_decide

example : ∃ result : CutFreeDerivation.CheckedCertificate,
    tree.desequentializeChecked? = some result :=
  tree.desequentializeChecked?_exists_of_infer?
    (show tree.infer? = some [p, pDual] by native_decide)

example : ∃ result : CutFreeDerivation.ElaboratedCertificate,
    tree.elaborate? = some result :=
  tree.elaborate?_exists_of_infer?
    (show tree.infer? = some [p, pDual] by native_decide)

example (proposition : Prop) : proposition → proposition ∧ proposition :=
  LeanProp.Templates.duplicate_proof proposition

example (antecedent consequent : Prop)
    (functionProof : antecedent → consequent) (argumentProof : antecedent) :
    consequent :=
  LeanProp.Templates.linearModusPonens_proof antecedent consequent
    functionProof argumentProof

namespace ContextExchange

example {left right : List Prop} :
    Nonempty (LeanProp.ContextPermutation left right) ↔ left.Perm right :=
  LeanProp.ContextPermutation.nonempty_iff_listPerm

example {left right : List Prop}
    (permutation : LeanProp.ContextPermutation left right)
    (values : LeanProp.Assumptions right) :
    LeanProp.Assumptions.permute permutation
        (LeanProp.Assumptions.permute permutation.symm values) = values :=
  LeanProp.Assumptions.permute_symm_right permutation values

example {source target linear : List Prop} {goal : Prop}
    (permutation : source.Perm target)
    (derivation : LeanProp.Derivation.{u} source linear goal) :
    Nonempty (LeanProp.Derivation.{u} target linear goal) :=
  LeanProp.Derivation.persistentExchange_nonempty_of_listPerm
    permutation derivation

end ContextExchange

namespace PersistentNormalization

def redundantIdentity (proposition : Prop) :
    LeanProp.Derivation [proposition] [] proposition :=
  .persistentContract (.persistentWeaken (.persistentAxiom))

example (proposition : Prop) :
    (redundantIdentity proposition).normalizePersistentStructural =
      LeanProp.Derivation.persistentAxiom := by
  rfl

example {persistent linear : List Prop} {goal : Prop}
    (derivation : LeanProp.Derivation.{u} persistent linear goal) :
    derivation.normalizePersistentStructural.PersistentStructurallyReduced :=
  derivation.normalizePersistentStructural_reduced

example {persistent linear : List Prop} {goal : Prop}
    (derivation : LeanProp.Derivation.{u} persistent linear goal) :
    derivation.normalizePersistentStructural.normalizePersistentStructural =
      derivation.normalizePersistentStructural :=
  derivation.normalizePersistentStructural_idempotent

example {persistent linear : List Prop} {goal : Prop}
    (derivation : LeanProp.Derivation.{u} persistent linear goal) :
    derivation.normalizePersistentStructural.persistentStructuralSize ≤
      derivation.persistentStructuralSize :=
  derivation.normalizePersistentStructural_size_le

end PersistentNormalization

namespace RawSchema

open LeanProp.Schema

def proposition : LeanProp.Schema.Formula := .atom "consumer-p"

def valid : Raw.Derivation :=
  .impIntro proposition (.persistentAxiom proposition)

example : valid.infer? = .ok {
    persistent := []
    linear := []
    goal := .imp proposition proposition
  } := by rfl

def invalid : Raw.Derivation :=
  .andElimLeft (.persistentAxiom proposition)

example : invalid.infer? = .error {
    path := []
    code := .expectedConjunction
    detail := "left projection requires a conjunction premise"
  } := by rfl

example : (Raw.Derivation.checkedFromString valid.canonicalString).isOk =
    true := by native_decide

example : (Raw.Derivation.checkedFromString invalid.canonicalString).isOk =
    false := by native_decide

example (checked : Raw.CheckedDerivation) :
    checked.derivation.infer? = .ok checked.sequent :=
  checked.inferred

example (checked : Raw.CheckedDerivation) : PackedDerivation :=
  checked.toPacked "consumer-checked-wire"

example (checked : Raw.CheckedDerivation) (valuation : String → Prop)
    (persistentValues : LeanProp.Assumptions
      (checked.elaborated.persistent.map (Formula.evaluate valuation)))
    (linearValues : LeanProp.Assumptions
      (checked.elaborated.linear.map (Formula.evaluate valuation))) :
    checked.elaborated.goal.evaluate valuation :=
  checked.sound valuation persistentValues linearValues

end RawSchema

end ProofNetIRTutorialSmoke
