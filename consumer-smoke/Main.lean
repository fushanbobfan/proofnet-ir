import Tutorial

open ProofNetIR

def consumedCertificate : Certificate :=
  canonicalCertificate "consumer-p" "consumer-q"

def reorderedConsumedCertificate : Certificate :=
  { consumedCertificate with links := consumedCertificate.links.reverse }

example : consumedCertificate.check = true := by native_decide

example : consumedCertificate.DeclarativelyCorrect :=
  consumedCertificate.check_iff_declarativelyCorrect.mp (by native_decide)

def consumedTree : CutFreeDerivation :=
  CutFreeDerivation.generate 42 2

example : consumedTree.elaborate?.isSome = true := by native_decide

def consumedSequentialization :
    Except SequentializationError
      (ExecutableSequentializationResult consumedCertificate) :=
  consumedCertificate.sequentialize

example : consumedSequentialization.isOk = true := by native_decide

example : ∃ result : ExecutableSequentializationResult consumedCertificate,
    consumedCertificate.sequentialize = .ok result :=
  consumedCertificate.sequentialize_complete (by native_decide)

example : Certificate.proofNetEquivalent? consumedCertificate
    reorderedConsumedCertificate = true := by native_decide

example : consumedCertificate.ProofNetEquivalent reorderedConsumedCertificate := by
  apply (Certificate.proofNetEquivalent?_eq_true_iff
    (consumedCertificate.check_sound_declarative (by native_decide)).1).mp
  native_decide

example : ∀ candidate,
    candidate ∈ consumedCertificate.proofNetCanonicalFamily ↔
      candidate ∈ reorderedConsumedCertificate.proofNetCanonicalFamily :=
  (Certificate.proofNetEquivalent_iff_canonicalFamily_of_check
    (left := consumedCertificate) (right := reorderedConsumedCertificate)
    (by native_decide) (by native_decide)).mp (by
      apply (Certificate.proofNetEquivalent?_eq_true_iff
        (consumedCertificate.check_sound_declarative
          (by native_decide)).1).mp
      native_decide)

example (result : ExecutableSequentializationResult consumedCertificate) :
    result.output.ProofNetEquivalent consumedCertificate :=
  result.proofNetEquivalent

example :
    (Certificate.checkedFromString consumedCertificate.canonicalString).isOk =
      true := by
  native_decide

example :
    (Certificate.checkedFromString
      consumedCertificate.equivalenceCanonicalString).isOk = true := by
  native_decide

example :
    (Certificate.migrateV02StringToV03
      consumedCertificate.canonicalString).isOk = true := by
  native_decide

def main : IO Unit := do
  if consumedCertificate.check && consumedTree.elaborate?.isSome &&
      consumedSequentialization.isOk &&
      Certificate.proofNetEquivalent? consumedCertificate
        reorderedConsumedCertificate &&
      (Certificate.checkedFromString
        consumedCertificate.canonicalString).isOk &&
      (Certificate.checkedFromString
        consumedCertificate.equivalenceCanonicalString).isOk then
    IO.println "ProofNetIR downstream consumer smoke test passed"
  else
    throw <| IO.userError "ProofNetIR downstream consumer smoke test failed"
