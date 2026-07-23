import ProofNetIR

open ProofNetIR

namespace ProofNetIRParserFuzz

def run : IO Unit := do
  let payload ← (← IO.getStdin).readToEnd
  let cases := payload.splitOn "\n" |>.filter fun input => !input.isEmpty
  if cases.isEmpty then
    throw <| IO.userError "parser fuzz harness received no cases"
  let mut errors := 0
  let mut accepted := 0
  for input in cases do
    match Certificate.checkedFromString input with
    | .error error =>
        if error.path.isEmpty || error.message.isEmpty then
          throw <| IO.userError "parser returned an unstructured empty error"
        errors := errors + 1
    | .ok checked =>
        if !checked.certificate.check then
          throw <| IO.userError "checked parser exposed a rejected certificate"
        accepted := accepted + 1
  IO.println s!"parser-fuzz-ok cases={cases.length} errors={errors} accepted={accepted}"

def runCanonicalKey : IO Unit := do
  let payload ← (← IO.getStdin).readToEnd
  let cases := payload.splitOn "\n" |>.filter fun input => !input.isEmpty
  if cases.isEmpty then
    throw <| IO.userError "canonical-key fuzz harness received no cases"
  let mut errors := 0
  let mut accepted := 0
  for input in cases do
    match CanonicalKey.fromString input with
    | .error error =>
        if error.path.isEmpty || error.message.isEmpty then
          throw <| IO.userError "canonical-key parser returned an empty error"
        errors := errors + 1
    | .ok key =>
        if !key.isWireAdmissible then
          throw <| IO.userError "canonical-key parser bypassed wire limits"
        accepted := accepted + 1
  IO.println s!"canonical-key-parser-fuzz-ok cases={cases.length} errors={errors} accepted={accepted}"

def runIntrinsicCanonicalKey : IO Unit := do
  let payload ← (← IO.getStdin).readToEnd
  let cases := payload.splitOn "\n" |>.filter fun input => !input.isEmpty
  if cases.isEmpty then
    throw <| IO.userError
      "intrinsic canonical-key fuzz harness received no cases"
  let mut errors := 0
  let mut accepted := 0
  for input in cases do
    match IntrinsicCanonicalKey.fromString input with
    | .error error =>
        if error.path.isEmpty || error.message.isEmpty then
          throw <| IO.userError
            "intrinsic canonical-key parser returned an empty error"
        errors := errors + 1
    | .ok key =>
        if !key.isWireAdmissible then
          throw <| IO.userError
            "intrinsic canonical-key parser bypassed wire limits"
        accepted := accepted + 1
  IO.println s!"intrinsic-canonical-key-parser-fuzz-ok cases={cases.length} errors={errors} accepted={accepted}"

end ProofNetIRParserFuzz

def main (args : List String) : IO Unit :=
  match args with
  | [] => ProofNetIRParserFuzz.run
  | ["--canonical-key"] => ProofNetIRParserFuzz.runCanonicalKey
  | ["--intrinsic-canonical-key"] =>
      ProofNetIRParserFuzz.runIntrinsicCanonicalKey
  | _ => throw <| IO.userError
      "usage: proofnet_ir_parser_fuzz [--canonical-key|--intrinsic-canonical-key]"
