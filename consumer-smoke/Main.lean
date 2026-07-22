import ProofNetIR

open ProofNetIR

def consumedCertificate : Certificate :=
  canonicalCertificate "consumer-p" "consumer-q"

example : consumedCertificate.check = true := by native_decide

def consumedTree : CutFreeDerivation :=
  CutFreeDerivation.generate 42 2

example : consumedTree.elaborate?.isSome = true := by native_decide

example :
    (Certificate.checkedFromString consumedCertificate.canonicalString).isOk =
      true := by
  native_decide

def main : IO Unit := do
  if consumedCertificate.check && consumedTree.elaborate?.isSome &&
      (Certificate.checkedFromString
        consumedCertificate.canonicalString).isOk then
    IO.println "ProofNetIR downstream consumer smoke test passed"
  else
    throw <| IO.userError "ProofNetIR downstream consumer smoke test failed"
