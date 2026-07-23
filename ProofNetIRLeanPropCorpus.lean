import ProofNetIR.LeanPropSchemaCorpus

open ProofNetIR.LeanProp.Schema.Corpus

def main : IO Unit := do
  let corpus := generated 100
  unless corpus.length == 600 do
    throw <| IO.userError s!"expected 600 LeanProp schemas, got {corpus.length}"
  let names := corpus.map (·.name)
  unless names.eraseDups.length == names.length do
    throw <| IO.userError "generated LeanProp schema names are not unique"
  let positives := rawPositive 100
  let positiveFailures := positives.filter fun record => !record.2.infer?.isOk
  unless positiveFailures.isEmpty do
    throw <| IO.userError
      s!"raw checker rejected {positiveFailures.length} erased positive templates"
  let negatives := rawNegative 100
  let negativeAcceptances := negatives.filter fun record =>
    record.derivation.infer?.isOk
  unless negativeAcceptances.isEmpty do
    throw <| IO.userError
      s!"raw checker accepted {negativeAcceptances.length} malformed templates"
  let diagnosticMismatches := negatives.filter fun record =>
    match record.derivation.infer? with
    | .ok _ => true
    | .error error =>
        error.code != record.expectedCode || error.path != record.expectedPath
  unless diagnosticMismatches.isEmpty do
    let names := diagnosticMismatches.map (·.name)
    throw <| IO.userError
      s!"raw checker returned {diagnosticMismatches.length} wrong diagnostics: {names}"
  IO.println s!"ProofNetIR LeanProp schema corpus passed: {corpus.length} typed/erased positives, {negatives.length} malformed negatives with exact diagnostics"
