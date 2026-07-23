import ProofNetIR.LeanPropSchemaWire

open ProofNetIR.LeanProp.Schema.Raw

namespace ProofNetIRLeanPropParserFuzz

def run : IO Unit := do
  let payload ← (← IO.getStdin).readToEnd
  let cases := payload.splitOn "\n" |>.filter fun input => !input.isEmpty
  if cases.isEmpty then
    throw <| IO.userError "LeanProp parser fuzz harness received no cases"
  let mut jsonErrors := 0
  let mut checkerErrors := 0
  let mut accepted := 0
  for input in cases do
    match Derivation.checkedFromString input with
    | .error (.json path message) =>
        if path.isEmpty || message.isEmpty then
          throw <| IO.userError "LeanProp parser returned an empty JSON diagnostic"
        jsonErrors := jsonErrors + 1
    | .error (.checker error) =>
        if error.detail.isEmpty then
          throw <| IO.userError "LeanProp checker returned an empty diagnostic"
        checkerErrors := checkerErrors + 1
    | .ok checked =>
        if !checked.derivation.infer?.isOk ||
            !checked.derivation.elaborate?.isOk then
          throw <| IO.userError
            "checked LeanProp parser exposed a non-elaborating schema"
        let _typed := checked.toPacked "fuzz-accepted"
        accepted := accepted + 1
  IO.println s!"leanprop-parser-fuzz-ok cases={cases.length} json-errors={jsonErrors} checker-errors={checkerErrors} accepted={accepted}"

end ProofNetIRLeanPropParserFuzz

def main : IO Unit := ProofNetIRLeanPropParserFuzz.run
