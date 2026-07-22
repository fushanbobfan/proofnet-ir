import ProofNetIR

open ProofNetIR

def releasedCertificate : Certificate :=
  canonicalCertificate "release-p" "release-q"

example : releasedCertificate.check = true := by native_decide

def releasedTree : CutFreeDerivation :=
  CutFreeDerivation.generate 17 2

example : releasedTree.desequentializeChecked?.isSome = true := by
  native_decide

def main : IO Unit := do
  if releasedCertificate.check && releasedTree.desequentializeChecked?.isSome then
    IO.println "ProofNetIR pinned-release consumer smoke test passed"
  else
    throw <| IO.userError "ProofNetIR pinned-release consumer smoke test failed"
