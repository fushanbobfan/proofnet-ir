import ProofNetIR

open ProofNetIR

namespace ProofNetIRV10CandidateConsumerSmoke

def certificate : Certificate :=
  canonicalCertificate "remote-v10-p" "remote-v10-q"

def reordered : Certificate :=
  { certificate with links := certificate.links.reverse }

def derivation : CutFreeDerivation :=
  .par 1 1
    (.tensor 0 0
      (.axiom "remote-v10-p" true)
      (.axiom "remote-v10-q" true))

private theorem structural : certificate.StructurallyWellFormed :=
  (certificate.check_sound_declarative (by native_decide)).1

-- The public decision is the sequential fast path and decides the reference checker.
example : certificate.unificationCheck = certificate.sequentialFastCheck :=
  certificate.unificationCheck_eq_sequentialFastCheck

example : certificate.sequentialFastCheck = certificate.check :=
  certificate.sequentialFastCheck_eq_check

example : certificate.unificationCheck = certificate.check :=
  certificate.unificationCheck_eq_check

example : certificate.unificationCheck = true := by
  native_decide

example : reordered.unificationCheck = true := by
  native_decide

-- The instrumented decision agrees with the public one and is cost-bounded.
example : certificate.sequentialDecisionWithStats.accepted = certificate.unificationCheck :=
  certificate.sequentialDecisionWithStats_accepted

example : certificate.sequentialDecisionWithStats.stats.total ≤
    152 * (certificate.formulas.size + 1) * SequentialCost.submittedSize certificate :=
  SequentialCost.decisionStats_total_le_of_structural structural

example : reordered.sequentialDecisionWithStats.stats.total ≤
    152 * SequentialCost.inputSize reordered * SequentialCost.inputSize reordered :=
  SequentialCost.decisionStats_total_le reordered

-- The supplied-derivation verifier and the intrinsic identity are unchanged.
example : ∃ result : DerivationVerificationResult certificate,
    certificate.verifyDerivation? derivation = some result := by
  apply Certificate.verifiesDerivation_eq_true_iff.mp
  native_decide

example :
    certificate.intrinsicCanonicalKey = reordered.intrinsicCanonicalKey := by
  apply (Certificate.proofNetEquivalent_iff_intrinsicCanonicalKey_eq_of_check
    (left := certificate) (right := reordered)
    (by native_decide) (by native_decide)).mp
  apply (Certificate.proofNetEquivalent?_eq_true_iff
    (certificate.check_sound_declarative (by native_decide)).1).mp
  native_decide

def run : IO Unit := do
  let instrumented := certificate.sequentialDecisionWithStats
  let bound := 152 * (certificate.formulas.size + 1) * SequentialCost.submittedSize certificate
  if certificate.unificationCheck &&
      certificate.sequentialFastCheck &&
      reordered.unificationCheck &&
      instrumented.accepted &&
      decide (instrumented.stats.total ≤ bound) &&
      decide (instrumented.stats.dispatchCalls ≤ certificate.formulas.size + 1) &&
      certificate.verifiesDerivation derivation &&
      certificate.intrinsicCanonicalKey = reordered.intrinsicCanonicalKey then
    IO.println s!"ProofNetIR pinned-v0.10 candidate consumer smoke test passed: decision operations {instrumented.stats.total} of bound {bound}"
  else
    throw <| IO.userError
      "ProofNetIR pinned-v0.10 candidate consumer smoke test failed"

end ProofNetIRV10CandidateConsumerSmoke

def main : IO Unit :=
  ProofNetIRV10CandidateConsumerSmoke.run
