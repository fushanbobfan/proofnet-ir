import ProofNetIR

open ProofNetIR

namespace ProofNetIRV06CandidateConsumerSmoke

open LeanProp.Schema

def proposition : LeanProp.Schema.Formula := .atom "remote-p"

def valid : Raw.Derivation :=
  .impIntro proposition (.persistentAxiom proposition)

def invalid : Raw.Derivation :=
  .andElimLeft (.persistentAxiom proposition)

def checkedValid := Raw.Derivation.checkedFromString valid.canonicalString

example : checkedValid.isOk = true := by native_decide

example :
    (Raw.Derivation.checkedFromString invalid.canonicalString).isOk = false := by
  native_decide

example (checked : Raw.CheckedDerivation) :
    checked.derivation.infer? = .ok checked.sequent :=
  checked.inferred

example (checked : Raw.CheckedDerivation) : PackedDerivation :=
  checked.toPacked "remote-v06-candidate"

example (checked : Raw.CheckedDerivation) (valuation : String → Prop)
    (persistentValues : LeanProp.Assumptions
      (checked.elaborated.persistent.map (Formula.evaluate valuation)))
    (linearValues : LeanProp.Assumptions
      (checked.elaborated.linear.map (Formula.evaluate valuation))) :
    checked.elaborated.goal.evaluate valuation :=
  checked.sound valuation persistentValues linearValues

def run : IO Unit := do
  if checkedValid.isOk &&
      !(Raw.Derivation.checkedFromString invalid.canonicalString).isOk then
    IO.println "ProofNetIR pinned-v0.6-candidate consumer smoke test passed"
  else
    throw <| IO.userError
      "ProofNetIR pinned-v0.6-candidate consumer smoke test failed"

end ProofNetIRV06CandidateConsumerSmoke

def main : IO Unit :=
  ProofNetIRV06CandidateConsumerSmoke.run
