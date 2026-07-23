import ProofNetIR

open ProofNetIR

namespace ProofNetIRTutorialSmoke

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

end ProofNetIRTutorialSmoke
