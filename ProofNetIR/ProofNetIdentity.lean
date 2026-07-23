import ProofNetIR.ProofNetCanonical
import ProofNetIR.ExecutableSequentialization

namespace ProofNetIR

namespace Certificate

/-- Number of formula-compatible vertex orders that the exact proof-net
identity decision will consider after enforcing the ordered conclusion
boundary during generation.  This diagnostic exposes search pressure without
changing the exact Boolean contract. -/
def proofNetIdentityCandidateCount (left right : Certificate) : Nat :=
  (matchingFormulaOrdersForCertificates left right).length

end Certificate

namespace CutFreeDerivation.CheckedCertificate

/-- Exact pairwise proof-net identity for checker-accepted certificates.

This is the supported production identity boundary.  It quotients bounded
vertex renaming and link-list storage order, while preserving ordered
conclusions, connective premise order, formula labels, and axiom orientation.
It is deliberately not arbitrary graph isomorphism. -/
def sameProofNet? (left right : CutFreeDerivation.CheckedCertificate) : Bool :=
  Certificate.proofNetEquivalent? left.certificate right.certificate

/-- The checked identity API decides exactly `ProofNetEquivalent`; callers do
not need to recover structural premises from checker acceptance themselves. -/
theorem sameProofNet?_eq_true_iff
    {left right : CutFreeDerivation.CheckedCertificate} :
    sameProofNet? left right = true ↔
      left.certificate.ProofNetEquivalent right.certificate :=
  Certificate.proofNetEquivalent?_eq_true_iff
    (left.certificate.check_sound_declarative left.accepted).1

end CutFreeDerivation.CheckedCertificate

end ProofNetIR
