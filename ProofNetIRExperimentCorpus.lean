import ProofNetIR

open Lean ProofNetIR

namespace ProofNetIRExperimentCorpus

/-- Fixed before running the matched experiment. The shallow majority keeps
the full 1,000-task run practical, while the final 50 tasks exercise repeated
atom labels and substantially larger switching/search spaces. -/
def depthFor (index : Nat) : Nat :=
  if index < 700 then 2 else if index < 950 then 3 else 4

def recordJson (index depth : Nat) (sequent : List Formula)
    (certificate : Certificate) : Json :=
  Json.mkObj [
    ("id", s!"matched-{index}"),
    ("seed", index),
    ("depth", depth),
    ("sequent", .arr (sequent.toArray.map Certificate.formulaJson)),
    ("referenceCertificate", certificate.canonicalJson)]

def run : IO Unit := do
  for index in List.range 1_000 do
    let depth := depthFor index
    let tree := CutFreeDerivation.generate index depth
    let some elaborated := tree.elaborate?
      | throw <| IO.userError s!"invalid generated task at index {index}"
    IO.println <| (recordJson index depth elaborated.sequent
      elaborated.certificate).compress

end ProofNetIRExperimentCorpus

def main : IO Unit := ProofNetIRExperimentCorpus.run
