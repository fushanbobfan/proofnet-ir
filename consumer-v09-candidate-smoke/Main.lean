import ProofNetIR

open ProofNetIR

namespace ProofNetIRV09ReleaseConsumerSmoke

def certificate : Certificate :=
  canonicalCertificate "remote-v09-p" "remote-v09-q"

def reordered : Certificate :=
  { certificate with links := certificate.links.reverse }

def derivation : CutFreeDerivation :=
  .par 1 1
    (.tensor 0 0
      (.axiom "remote-v09-p" true)
      (.axiom "remote-v09-q" true))

def tree : Graph where
  vertexCount := 3
  edges := [
    { first := 0, second := 1 },
    { first := 1, second := 2 }
  ]

example : tree.isAcyclic = true ↔ tree.Acyclic :=
  tree.isAcyclic_eq_true_iff

example : tree.IsTree ↔
    tree.Bounded ∧ tree.Connected ∧ tree.Acyclic :=
  tree.isTree_iff_bounded_connected_acyclic

example : tree.isTreeViaAcyclic = tree.isTree :=
  tree.isTreeViaAcyclic_eq_isTree

example : ∃ result : DerivationVerificationResult certificate,
    certificate.verifyDerivation? derivation = some result := by
  apply Certificate.verifiesDerivation_eq_true_iff.mp
  native_decide

example : ∃ result : DerivationVerificationResult certificate,
    certificate.reconstructDerivation? = some result :=
  certificate.reconstructDerivation?_complete (by native_decide)

example : certificate.unificationWorklistFastCheck = true := by
  native_decide

example :
    certificate.unificationWorklistCheck = certificate.check :=
  certificate.unificationWorklistCheck_eq_check

example : certificate.unificationCheck = certificate.check :=
  certificate.unificationCheck_eq_check

example :
    certificate.intrinsicCanonicalKey = reordered.intrinsicCanonicalKey := by
  apply (Certificate.proofNetEquivalent_iff_intrinsicCanonicalKey_eq_of_check
    (left := certificate) (right := reordered)
    (by native_decide) (by native_decide)).mp
  apply (Certificate.proofNetEquivalent?_eq_true_iff
    (certificate.check_sound_declarative (by native_decide)).1).mp
  native_decide

def run : IO Unit := do
  if tree.isAcyclic &&
      tree.isTreeViaAcyclic &&
      certificate.verifiesDerivation derivation &&
      certificate.reconstructsDerivation &&
      certificate.unificationWorklistFastCheck &&
      certificate.unificationWorklistCheck &&
      certificate.unificationCheck &&
      certificate.intrinsicCanonicalKey =
        reordered.intrinsicCanonicalKey then
    IO.println "ProofNetIR pinned-v0.9.0 consumer smoke test passed"
  else
    throw <| IO.userError
      "ProofNetIR pinned-v0.9.0 consumer smoke test failed"

end ProofNetIRV09ReleaseConsumerSmoke

def main : IO Unit :=
  ProofNetIRV09ReleaseConsumerSmoke.run
