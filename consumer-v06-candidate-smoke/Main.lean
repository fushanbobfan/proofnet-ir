import ProofNetIR

open ProofNetIR

namespace ProofNetIRV06CandidateConsumerSmoke

universe u

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

example {left right : List Prop} :
    Nonempty (LeanProp.ContextPermutation left right) ↔ left.Perm right :=
  LeanProp.ContextPermutation.nonempty_iff_listPerm

example {left right : List Prop}
    (permutation : LeanProp.ContextPermutation left right)
    (values : LeanProp.Assumptions right) :
    LeanProp.Assumptions.permute permutation
        (LeanProp.Assumptions.permute permutation.symm values) = values :=
  LeanProp.Assumptions.permute_symm_right permutation values

example {persistent source target : List Prop} {goal : Prop}
    (permutation : source.Perm target)
    (derivation : LeanProp.Derivation.{u} persistent source goal) :
    Nonempty (LeanProp.Derivation.{u} persistent target goal) :=
  LeanProp.Derivation.linearExchange_nonempty_of_listPerm
    permutation derivation

def redundantPersistentIdentity (proposition : Prop) :
    LeanProp.Derivation [proposition] [] proposition :=
  .persistentContract (.persistentWeaken (.persistentAxiom))

example (proposition : Prop) :
    (redundantPersistentIdentity proposition).normalizePersistentStructural =
      LeanProp.Derivation.persistentAxiom := by
  rfl

example {persistent linear : List Prop} {goal : Prop}
    (derivation : LeanProp.Derivation.{u} persistent linear goal) :
    derivation.normalizePersistentStructural.PersistentStructurallyReduced :=
  derivation.normalizePersistentStructural_reduced

example {persistent linear : List Prop} {goal : Prop}
    (derivation : LeanProp.Derivation.{u} persistent linear goal) :
    derivation.normalizePersistentStructural.normalizePersistentStructural =
      derivation.normalizePersistentStructural :=
  derivation.normalizePersistentStructural_idempotent

example {persistent linear : List Prop} {goal : Prop}
    (derivation : LeanProp.Derivation.{u} persistent linear goal) :
    derivation.normalizePersistentStructural.persistentStructuralSize ≤
      derivation.persistentStructuralSize :=
  derivation.normalizePersistentStructural_size_le

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
