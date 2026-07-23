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
  peelPars : Nat := 0

def cases : List StressCase := [
  ⟨"right-tensor-4", rightTensor 4, false, 0⟩,
  ⟨"right-tensor-6", rightTensor 6, false, 0⟩,
  ⟨"right-tensor-7", rightTensor 7, false, 0⟩,
  ⟨"right-tensor-8", rightTensor 8, false, 0⟩,
  ⟨"right-tensor-8-reversed", rightTensor 8, true, 0⟩,
  ⟨"right-tensor-12", rightTensor 12, false, 0⟩,
  ⟨"right-tensor-16-reversed", rightTensor 16, true, 0⟩,
  ⟨"right-tensor-20-reversed", rightTensor 20, true, 0⟩,
  ⟨"expanded-boundary-20-reversed", rightTensor 20, true, 20⟩,
  ⟨"balanced-tensor-3", balancedTensor 3, false, 0⟩,
  ⟨"balanced-tensor-4", balancedTensor 4, false, 0⟩,
  ⟨"balanced-tensor-4-reversed", balancedTensor 4, true, 0⟩,
  ⟨"balanced-tensor-5-reversed", balancedTensor 5, true, 0⟩,
  ⟨"balanced-par-3", balancedPar 3, false, 0⟩,
  ⟨"balanced-par-4", balancedPar 4, false, 0⟩,
  ⟨"balanced-par-4-reversed", balancedPar 4, true, 0⟩,
  ⟨"alternating-4", alternating true 4, false, 0⟩,
  ⟨"alternating-5-reversed", alternating true 5, true, 0⟩
]

def budgetMs : Nat := 45_000

def peelTerminalPars : Nat → Certificate → Option Certificate
  | 0, certificate => some certificate
  | count + 1, certificate => do
      let (left, right, conclusion) ← certificate.terminalPars.head?
      let premise ←
        certificate.peelTerminalParCandidate? left right conclusion
      peelTerminalPars count premise

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
    let generated := identityCertificate stress.formula
    let original ← match peelTerminalPars stress.peelPars generated with
      | none =>
          throw <| IO.userError
            s!"stress par expansion failed: {stress.name}"
      | some value => pure value
    let input :=
      if stress.reverseLinks then
        { original with links := original.links.reverse }
      else
        original
    if !input.wellFormed then
      throw <| IO.userError
        s!"stress certificate was not structurally valid: {stress.name}"
    let unificationStart ← IO.monoMsNow
    let unification ← match input.unificationReconstructWithStats with
      | .error _ =>
          throw <| IO.userError
            s!"deterministic unification failed: {stress.name}"
      | .ok value => pure value
    let unificationMs := (← IO.monoMsNow) - unificationStart
    checksum := checksum +
      unification.verification.output.formulas.size +
      unification.verification.output.links.length +
      unification.verification.sequent.length
    IO.println
      s!"reconstruction-stress-unification name={stress.name} elapsed_ms={unificationMs} passes={unification.candidate.stats.passes} link_visits={unification.candidate.stats.linkVisits}"
    (← IO.getStdout).flush
    let worklistStart ← IO.monoMsNow
    let worklist ← match input.unificationWorklistReconstructWithStats with
      | .error _ =>
          throw <| IO.userError
            s!"worklist unification failed: {stress.name}"
      | .ok value => pure value
    let worklistMs := (← IO.monoMsNow) - worklistStart
    checksum := checksum +
      worklist.verification.output.formulas.size +
      worklist.verification.output.links.length +
      worklist.verification.sequent.length
    IO.println
      s!"reconstruction-stress-worklist name={stress.name} elapsed_ms={worklistMs} link_attempts={worklist.candidate.stats.linkAttempts} waiting_requeues={worklist.candidate.stats.waitingRequeues}"
    (← IO.getStdout).flush
    let canonicalStart ← IO.monoMsNow
    let inputCode := input.intrinsicCanonicalCode
    let canonicalMs := (← IO.monoMsNow) - canonicalStart
    checksum := checksum + inputCode.length
    IO.println
      s!"reconstruction-stress-canonical name={stress.name} code_tokens={inputCode.length} elapsed_ms={canonicalMs}"
    (← IO.getStdout).flush
    let caseStart ← IO.monoMsNow
    let result ← match input.reconstructDerivationWithinLimits with
      | .error error =>
          throw <| IO.userError
            s!"bounded checker-free reconstruction failed: {stress.name}: {error.message}"
      | .ok value => pure value
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
