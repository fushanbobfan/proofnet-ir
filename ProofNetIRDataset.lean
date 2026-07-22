import ProofNetIR

open Lean ProofNetIR

namespace ProofNetIRDataset

def recordJson (caseId provenance : String) (seed : Nat)
    (certificate : Certificate) : Json :=
  let normalized := certificate.canonicalize
  Json.mkObj [
    ("id", caseId),
    ("label", normalized.check),
    ("provenance", provenance),
    ("derivationSeed", seed),
    ("certificate", normalized.canonicalJson)]

def casesForCertificate (certificate : Certificate) :
    List (String × Certificate) :=
  [ ("valid-derivation", certificate),
    ("missing-link", Mutation.dropFirstLink.apply certificate),
    ("duplicated-resource", Mutation.duplicateFirstLink.apply certificate),
    ("self-axiom", (Mutation.replaceFirstAxiomRight 0).apply certificate) ]

def run : IO Unit := do
  for seed in List.range 250 do
    let tree := CutFreeDerivation.generate seed 2
    let some certificate := tree.desequentialize?
      | throw <| IO.userError s!"generator produced invalid tree at seed {seed}"
    for (provenance, candidate) in casesForCertificate certificate do
      let caseId := s!"v0.2-{seed}-{provenance}"
      IO.println (recordJson caseId provenance seed candidate).compress

end ProofNetIRDataset

def main : IO Unit := ProofNetIRDataset.run
