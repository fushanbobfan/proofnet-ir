import ProofNetIR

open ProofNetIR

def consumedCertificate : Certificate :=
  canonicalCertificate "consumer-p" "consumer-q"

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
      (Certificate.checkedFromString
        consumedCertificate.canonicalString).isOk &&
      (Certificate.checkedFromString
        consumedCertificate.equivalenceCanonicalString).isOk then
    IO.println "ProofNetIR downstream consumer smoke test passed"
  else
    throw <| IO.userError "ProofNetIR downstream consumer smoke test failed"
