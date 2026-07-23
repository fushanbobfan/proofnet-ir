import ProofNetIR.LeanPropSchemaCorpus

open ProofNetIR.LeanProp.Schema.Corpus

def main : IO Unit := do
  let start ← IO.monoMsNow
  let budgetMs : Nat := 10_000
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
  let positiveElaborationFailures := positives.filter fun record =>
    !record.2.elaborate?.isOk
  unless positiveElaborationFailures.isEmpty do
    throw <| IO.userError
      s!"typed elaborator rejected {positiveElaborationFailures.length} erased positive templates"
  let positiveWireFailures := positives.filter fun record =>
    match ProofNetIR.LeanProp.Schema.Raw.Derivation.checkedFromString
        record.2.canonicalString with
    | .ok checked => checked.derivation != record.2
    | .error _ => true
  unless positiveWireFailures.isEmpty do
    throw <| IO.userError
      s!"versioned wire round trip failed for {positiveWireFailures.length} positive templates"
  let negatives := rawNegative 100
  let negativeAcceptances := negatives.filter fun record =>
    record.derivation.infer?.isOk
  unless negativeAcceptances.isEmpty do
    throw <| IO.userError
      s!"raw checker accepted {negativeAcceptances.length} malformed templates"
  let negativeElaborationAcceptances := negatives.filter fun record =>
    record.derivation.elaborate?.isOk
  unless negativeElaborationAcceptances.isEmpty do
    throw <| IO.userError
      s!"typed elaborator accepted {negativeElaborationAcceptances.length} malformed templates"
  let diagnosticMismatches := negatives.filter fun record =>
    match record.derivation.infer? with
    | .ok _ => true
    | .error error =>
        error.code != record.expectedCode || error.path != record.expectedPath
  unless diagnosticMismatches.isEmpty do
    let names := diagnosticMismatches.map (·.name)
    throw <| IO.userError
      s!"raw checker returned {diagnosticMismatches.length} wrong diagnostics: {names}"
  let negativeWireMismatches := negatives.filter fun record =>
    match ProofNetIR.LeanProp.Schema.Raw.Derivation.checkedFromString
        record.derivation.canonicalString with
    | .error (.checker error) =>
        error.code != record.expectedCode || error.path != record.expectedPath
    | _ => true
  unless negativeWireMismatches.isEmpty do
    throw <| IO.userError
      s!"versioned wire checker mishandled {negativeWireMismatches.length} malformed templates"
  let malformedWireInputs := [
    "{}",
    "{\"version\":\"wrong\",\"derivation\":{\"kind\":\"persistent-axiom\",\"formula\":{\"kind\":\"atom\",\"name\":\"p\"}}}",
    "{\"version\":\"leanprop-schema-0.1\",\"derivation\":{\"kind\":\"unknown\"}}",
    "{\"version\":\"leanprop-schema-0.1\",\"extra\":true,\"derivation\":{\"kind\":\"persistent-axiom\",\"formula\":{\"kind\":\"atom\",\"name\":\"p\"}}}",
    "{\"version\":\"leanprop-schema-0.1\""
  ]
  unless (malformedWireInputs.all fun input =>
      !(ProofNetIR.LeanProp.Schema.Raw.Derivation.checkedFromString input).isOk) do
    throw <| IO.userError "malformed versioned wire input was accepted"
  let validFixture ← IO.FS.readFile
    "examples/leanprop-identity-v0.1.json"
  unless (ProofNetIR.LeanProp.Schema.Raw.Derivation.checkedFromString
      validFixture).isOk do
    throw <| IO.userError "valid LeanProp wire fixture was rejected"
  let invalidFixture ← IO.FS.readFile
    "examples/leanprop-invalid-projection-v0.1.json"
  match ProofNetIR.LeanProp.Schema.Raw.Derivation.checkedFromString
      invalidFixture with
  | .error (.checker error) =>
      unless error.code == .expectedConjunction && error.path == [] do
        throw <| IO.userError "invalid LeanProp fixture returned wrong checker diagnostic"
  | _ => throw <| IO.userError "invalid LeanProp wire fixture was not checker-rejected"
  let elapsed := (← IO.monoMsNow) - start
  if elapsed > budgetMs then
    throw <| IO.userError
      s!"LeanProp corpus performance budget exceeded: {elapsed}ms > {budgetMs}ms"
  IO.println s!"ProofNetIR LeanProp schema corpus passed: {corpus.length} typed/erased/elaborated/wire-round-tripped positives, {negatives.length} malformed negatives rejected by infer/elaborate with exact raw and wire diagnostics, elapsed_ms={elapsed}, budget_ms={budgetMs}"
