import ProofNetIR

open ProofNetIR

def releasedCertificate : Certificate :=
  canonicalCertificate "release-p" "release-q"

example : releasedCertificate.check = true := by native_decide

example : Nonempty (SequentializationResult releasedCertificate) :=
  releasedCertificate.sequentialization_of_check (by native_decide)

example : ∃ result : ExecutableSequentializationResult releasedCertificate,
    releasedCertificate.sequentialize = .ok result :=
  releasedCertificate.sequentialize_complete (by native_decide)

def reorderedReleasedCertificate : Certificate :=
  { releasedCertificate with links := releasedCertificate.links.reverse }

example : Certificate.proofNetEquivalent? releasedCertificate
    reorderedReleasedCertificate = true := by native_decide

example : ∀ candidate,
    candidate ∈ releasedCertificate.proofNetCanonicalFamily ↔
      candidate ∈ reorderedReleasedCertificate.proofNetCanonicalFamily :=
  (Certificate.proofNetEquivalent_iff_canonicalFamily_of_check
    (left := releasedCertificate) (right := reorderedReleasedCertificate)
    (by native_decide) (by native_decide)).mp (by
      apply (Certificate.proofNetEquivalent?_eq_true_iff
        (releasedCertificate.check_sound_declarative
          (by native_decide)).1).mp
      native_decide)

def releasedTree : CutFreeDerivation :=
  CutFreeDerivation.generate 17 2

example : releasedTree.desequentializeChecked?.isSome = true := by
  native_decide

example :
    (Certificate.checkedFromString
      releasedCertificate.equivalenceCanonicalString).isOk = true := by
  native_decide

example :
    (Certificate.migrateV02StringToV03
      releasedCertificate.canonicalString).isOk = true := by
  native_decide

example :
    Certificate.reindexEquivalent? releasedCertificate releasedCertificate =
      true := by
  native_decide

def main : IO Unit := do
  if releasedCertificate.check && releasedTree.desequentializeChecked?.isSome &&
      releasedCertificate.sequentialize.isOk &&
      Certificate.proofNetEquivalent? releasedCertificate
        reorderedReleasedCertificate &&
      (Certificate.checkedFromString
        releasedCertificate.equivalenceCanonicalString).isOk &&
      Certificate.reindexEquivalent? releasedCertificate
        releasedCertificate then
    IO.println "ProofNetIR pinned-release consumer smoke test passed"
  else
    throw <| IO.userError "ProofNetIR pinned-release consumer smoke test failed"
