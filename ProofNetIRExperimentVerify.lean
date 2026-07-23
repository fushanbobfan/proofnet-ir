import ProofNetIR

open Lean ProofNetIR

namespace ProofNetIRExperimentVerify

/-- Batch verification boundary for experiment outputs. Each input line is a
canonical certificate. Accepted candidates are also run through the public
executable sequentializer, so the report never relies on the Python oracle
alone. -/
def run : IO Unit := do
  let payload ← (← IO.getStdin).readToEnd
  let cases := payload.splitOn "\n" |>.filter fun input => !input.isEmpty
  if cases.isEmpty then
    throw <| IO.userError "experiment verifier received no cases"
  for input in cases do
    match Certificate.fromString input with
    | .error error =>
        throw <| IO.userError s!"certificate parse failed at {error.path}: {error.message}"
    | .ok certificate =>
        let accepted := certificate.check
        let sequentialized :=
          if accepted then
            match certificate.sequentialize with
            | .ok _ => true
            | .error _ => false
          else
            false
        IO.println <| (Json.mkObj [
          ("accepted", accepted),
          ("sequentialized", sequentialized)]).compress

end ProofNetIRExperimentVerify

def main : IO Unit := ProofNetIRExperimentVerify.run
