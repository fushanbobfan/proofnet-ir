import ProofNetIR

open ProofNetIR

namespace ProofNetIRReconstructionStress

def repeatedAtom : Formula := .atom "repeated-internal" true

def rightTensor : Nat → Formula
  | 0 => repeatedAtom
  | depth + 1 => .tensor (rightTensor depth) repeatedAtom

def balancedTensor : Nat → Formula
  | 0 => repeatedAtom
  | depth + 1 =>
      .tensor (balancedTensor depth) (balancedTensor depth)

def balancedPar : Nat → Formula
  | 0 => repeatedAtom
  | depth + 1 =>
      .par (balancedPar depth) (balancedPar depth)

def alternating : Bool → Nat → Formula
  | _, 0 => repeatedAtom
  | tensorNext, depth + 1 =>
      let child := alternating (!tensorNext) depth
      if tensorNext then .tensor child child else .par child child

structure StressCase where
  name : String
  formula : Formula
  reverseLinks : Bool

def cases : List StressCase := [
  ⟨"right-tensor-4", rightTensor 4, false⟩,
  ⟨"right-tensor-6", rightTensor 6, false⟩,
  ⟨"right-tensor-7", rightTensor 7, false⟩,
  ⟨"right-tensor-8", rightTensor 8, false⟩,
  ⟨"right-tensor-8-reversed", rightTensor 8, true⟩,
  ⟨"right-tensor-12", rightTensor 12, false⟩,
  ⟨"right-tensor-16-reversed", rightTensor 16, true⟩,
  ⟨"right-tensor-20-reversed", rightTensor 20, true⟩,
  ⟨"balanced-tensor-3", balancedTensor 3, false⟩,
  ⟨"balanced-tensor-4", balancedTensor 4, false⟩,
  ⟨"balanced-tensor-4-reversed", balancedTensor 4, true⟩,
  ⟨"balanced-tensor-5-reversed", balancedTensor 5, true⟩,
  ⟨"balanced-par-3", balancedPar 3, false⟩,
  ⟨"balanced-par-4", balancedPar 4, false⟩,
  ⟨"balanced-par-4-reversed", balancedPar 4, true⟩,
  ⟨"alternating-4", alternating true 4, false⟩,
  ⟨"alternating-5-reversed", alternating true 5, true⟩
]

def budgetMs : Nat := 45_000

def run (arguments : List String) : IO Unit := do
  let selected :=
    match arguments with
    | [] => cases
    | requested :: _ => cases.filter (·.name == requested)
  if selected.isEmpty then
    throw <| IO.userError "unknown reconstruction stress case"
  let start ← IO.monoMsNow
  let mut checksum := 0
  for stress in selected do
    let original := identityCertificate stress.formula
    let input :=
      if stress.reverseLinks then
        { original with links := original.links.reverse }
      else
        original
    if !input.wellFormed then
      throw <| IO.userError
        s!"stress certificate was not structurally valid: {stress.name}"
    let canonicalStart ← IO.monoMsNow
    let inputCode := input.intrinsicCanonicalCode
    let canonicalMs := (← IO.monoMsNow) - canonicalStart
    checksum := checksum + inputCode.length
    IO.println
      s!"reconstruction-stress-canonical name={stress.name} code_tokens={inputCode.length} elapsed_ms={canonicalMs}"
    (← IO.getStdout).flush
    let caseStart ← IO.monoMsNow
    let result ← match input.reconstructDerivation? with
      | none =>
          throw <| IO.userError
            s!"checker-free reconstruction failed: {stress.name}"
      | some value => pure value
    let caseMs := (← IO.monoMsNow) - caseStart
    checksum := checksum + result.output.formulas.size +
      result.output.links.length + result.sequent.length
    IO.println
      s!"reconstruction-stress-case name={stress.name} formulas={input.formulas.size} links={input.links.length} elapsed_ms={caseMs}"
  let elapsed := (← IO.monoMsNow) - start
  if elapsed > budgetMs then
    throw <| IO.userError
      s!"reconstruction stress budget exceeded: {elapsed}ms > {budgetMs}ms"
  IO.println
    s!"checker-free-reconstruction-stress-ok cases={selected.length} checksum={checksum} elapsed_ms={elapsed} budget_ms={budgetMs}"

end ProofNetIRReconstructionStress

def main (arguments : List String) : IO Unit :=
  ProofNetIRReconstructionStress.run arguments
