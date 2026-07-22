import ProofNetIR

open ProofNetIR

/-!
This file is compiled separately by the trust audit.  Its output is parsed by
`scripts/audit_axioms.py`, so adding a stronger theorem to the public logical
boundary requires an explicit update of that audit rather than a silent trust
expansion.
-/

#print axioms Certificate.check_iff_declarativelyCorrect
#print axioms Certificate.sequentialization_of_check
#print axioms Certificate.generallySequentializable
#print axioms Certificate.reindexEquivalent?_eq_true_iff_of_check
#print axioms Certificate.matchingFormulaOrders_complete
#print axioms Certificate.directProofNetEquivalentWitness?_complete
#print axioms Certificate.proofNetEquivalent?_eq_true_iff
#print axioms ExecutableSequentializationResult.kernelDerivation
#print axioms ExecutableSequentializationResult.proofNetEquivalent
