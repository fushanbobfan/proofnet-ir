import ProofNetIR

open ProofNetIR

/-!
This file is compiled separately by the trust audit.  Its output is parsed by
`scripts/audit_axioms.py`, so adding a stronger theorem to the public logical
boundary requires an explicit update of that audit rather than a silent trust
expansion.
-/

#print axioms Certificate.check_iff_declarativelyCorrect
#print axioms CutFreeDerivation.infer?_eq_some_iff_build?_conclusions
#print axioms CutFreeDerivation.build?_structurallyWellFormed
#print axioms CutFreeDerivation.build?_switchingCorrect
#print axioms CutFreeDerivation.build?_declarativelyCorrect
#print axioms CutFreeDerivation.build?_check
#print axioms CutFreeDerivation.desequentialize?_conclusionFormulas?
#print axioms CutFreeDerivation.desequentialize?_declarativelyCorrect
#print axioms CutFreeDerivation.desequentialize?_check
#print axioms CutFreeDerivation.desequentialize?_exists_with_labels_of_infer?
#print axioms CutFreeDerivation.desequentialize?_exists_checked_of_infer?
#print axioms CutFreeDerivation.desequentializeChecked?_exists_of_infer?
#print axioms CutFreeDerivation.elaborate?_exists_of_infer?
#print axioms Certificate.sequentialization_of_check
#print axioms Certificate.generallySequentializable
#print axioms Certificate.reindexEquivalent?_eq_true_iff_of_check
#print axioms Certificate.matchingFormulaOrders_complete
#print axioms Certificate.directProofNetEquivalentWitness?_complete
#print axioms Certificate.proofNetEquivalent?_eq_true_iff
#print axioms Certificate.proofNetEquivalent_iff_canonicalFamily_of_check
#print axioms Certificate.sequentialize_complete
#print axioms ExecutableSequentializationResult.kernelDerivation
#print axioms ExecutableSequentializationResult.proofNetEquivalent
