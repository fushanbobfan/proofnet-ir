import ProofNetIR.LeanPropSchemaCorpus

open ProofNetIR.LeanProp.Schema.Corpus

def main : IO Unit := do
  let corpus := generated 100
  unless corpus.length == 600 do
    throw <| IO.userError s!"expected 600 LeanProp schemas, got {corpus.length}"
  let names := corpus.map (·.name)
  unless names.eraseDups.length == names.length do
    throw <| IO.userError "generated LeanProp schema names are not unique"
  IO.println s!"ProofNetIR LeanProp schema corpus passed: {corpus.length} typed templates"
