import Lean

/-!
Audit the axiom dependencies of every safe declaration in the supplied modules.
Selection uses the defining module, not a declaration-name prefix, so private
helpers and declarations outside the library namespace are covered as well.
The curated, exact per-theorem boundary remains in `ProofNetIRAxiomAudit.lean`.
-/

open Lean

namespace ProofNetIRTrustAudit

private def allowedAxioms : Array Name :=
  #[``propext, ``Classical.choice, ``Quot.sound]

private def audit (modules : Array Name) : CoreM Nat := do
  let environment ← getEnv
  let mut count := 0
  let mut failures : Array String := #[]
  for (name, info) in environment.constants.toList do
    let some index := environment.getModuleIdxFor? name | continue
    let moduleName := environment.allImportedModuleNames[index.toNat]!
    if !modules.contains moduleName || info.isUnsafe then continue
    count := count + 1
    let unexpected := (← collectAxioms name).filter (!allowedAxioms.contains ·)
    unless unexpected.isEmpty do
      failures := failures.push s!"{moduleName}: {name} depends on {unexpected}"
  unless failures.isEmpty do
    let details := String.intercalate "\n" (failures.qsort (· < ·)).toList
    throwError "library trust audit rejected {failures.size} declarations:\n{details}"
  if count == 0 then
    throwError "library trust audit found no declarations in the requested modules"
  return count

end ProofNetIRTrustAudit

/-- Import the requested modules at trust zero and audit their compiled terms. -/
unsafe def main (args : List String) : IO Unit := do
  if args.isEmpty then
    throw <| IO.userError "usage: lake env lean --run ProofNetIRTrustAudit.lean MODULE ..."
  let modules := (args.map String.toName).toArray
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let environment ← Lean.importModules (modules.map fun module => { module }) {}
    (trustLevel := 0) (loadExts := true) (level := .private)
  let count ← (ProofNetIRTrustAudit.audit modules).toIO'
    { fileName := "ProofNetIRTrustAudit.lean", fileMap := default }
    { env := environment }
  IO.println s!"ProofNet-IR library trust audit passed: {count} safe declarations in {modules.size} modules; only [propext, Classical.choice, Quot.sound] permitted"
