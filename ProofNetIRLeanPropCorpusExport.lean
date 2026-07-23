import ProofNetIR.LeanPropSchemaCorpus

open ProofNetIR.LeanProp.Schema.Corpus

namespace ProofNetIRLeanPropCorpusExport

def natArrayJson (values : List Nat) : Lean.Json :=
  .arr (values.toArray.map fun value =>
    .num (Lean.JsonNumber.fromNat value))

def positiveJson (record : String × ProofNetIR.LeanProp.Schema.Raw.Derivation) :
    Lean.Json :=
  Lean.Json.mkObj [
    ("name", record.1),
    ("expected", "accepted"),
    ("schema", record.2.canonicalJson)]

def negativeJson (record : RawNegativeCase) : Lean.Json :=
  Lean.Json.mkObj [
    ("name", record.name),
    ("expected", "rejected"),
    ("error_code", reprStr record.expectedCode),
    ("error_path", natArrayJson record.expectedPath),
    ("schema", record.derivation.canonicalJson)]

def run : IO Unit := do
  for record in rawPositive 100 do
    IO.println (positiveJson record).compress
  for record in rawNegative 100 do
    IO.println (negativeJson record).compress

end ProofNetIRLeanPropCorpusExport

def main : IO Unit := ProofNetIRLeanPropCorpusExport.run
