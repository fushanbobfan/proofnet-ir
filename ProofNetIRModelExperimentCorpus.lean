import ProofNetIR

open Lean ProofNetIR

namespace ProofNetIRModelExperimentCorpus

/-- The model-backed experiment uses fresh seeds disjoint from the v0.1
algorithmic corpus.  Thirty bases per depth become paired positive/negative
tasks after the Python preparation step. -/
def baseCount : Nat := 90

def seedOffset : Nat := 10_000

def depthFor (index : Nat) : Nat :=
  if index < 30 then 2 else if index < 60 then 3 else 4

def recordJson (index seed depth : Nat) (sequent : List Formula)
    (certificate : Certificate) : Json :=
  Json.mkObj [
    ("id", s!"model-base-{index}"),
    ("seed", seed),
    ("depth", depth),
    ("sequent", .arr (sequent.toArray.map Certificate.formulaJson)),
    ("referenceCertificate", certificate.canonicalJson)]

def run : IO Unit := do
  for index in List.range baseCount do
    let seed := seedOffset + index
    let depth := depthFor index
    let tree := CutFreeDerivation.generate seed depth
    let some elaborated := tree.elaborate?
      | throw <| IO.userError s!"invalid generated task at seed {seed}"
    IO.println <| (recordJson index seed depth elaborated.sequent
      elaborated.certificate).compress

end ProofNetIRModelExperimentCorpus

def main : IO Unit := ProofNetIRModelExperimentCorpus.run
