import ProofNetIR.DerivationTree
import ProofNetIR.Serialization

namespace ProofNetIR

/-- A machine-readable location and explanation for a certificate parse
failure. Paths use the familiar JSON notation `$`, `.field`, and `[index]`. -/
structure ParseError where
  path : String
  message : String
  deriving Repr, DecidableEq, BEq

namespace ParseError

def render (error : ParseError) : String :=
  s!"{error.path}: {error.message}"

end ParseError

abbrev ParseResult (alpha : Type) := Except ParseError alpha

namespace Certificate

private def atPath (path : String) (result : Except String alpha) :
    ParseResult alpha :=
  result.mapError fun message => { path, message }

private def field (path : String) (json : Lean.Json) (name : String) :
    ParseResult Lean.Json :=
  atPath s!"{path}.{name}" (json.getObjVal? name)

private def decode (path : String) [Lean.FromJson alpha]
    (json : Lean.Json) : ParseResult alpha :=
  atPath path (Lean.fromJson? json)

private def array (path : String) (json : Lean.Json) :
    ParseResult (Array Lean.Json) :=
  atPath path json.getArr?

private def requireKeys (path : String) (json : Lean.Json)
    (expected : List String) : ParseResult Unit :=
  match json with
  | .obj fields =>
      match fields.toList.map Prod.fst |>.find? (fun key => !expected.contains key) with
      | some unexpected =>
          throw { path := s!"{path}.{unexpected}", message := "unexpected property" }
      | none => pure ()
  | _ => throw { path, message := "object expected" }

private def parseArray (path : String) (json : Lean.Json)
    (parse : String → Lean.Json → ParseResult alpha) :
    ParseResult (Array alpha) := do
  let values ← array path json
  values.zipIdx.mapM fun (value, index) =>
    parse s!"{path}[{index}]" value

private def maxFormulaDepth : Nat := 1024

private def formulaFromJsonAtFuel : Nat → String → Lean.Json →
    ParseResult Formula
  | 0, path, _ =>
      throw { path, message := s!"formula nesting exceeds {maxFormulaDepth}" }
  | fuel + 1, path, json => do
      let kindJson ← field path json "kind"
      let kind : String ← decode s!"{path}.kind" kindJson
      match kind with
      | "atom" =>
          requireKeys path json ["kind", "name", "positive"]
          let nameJson ← field path json "name"
          let name : String ← decode s!"{path}.name" nameJson
          if name.isEmpty then
            throw { path := s!"{path}.name", message := "atom name must be non-empty" }
          let positiveJson ← field path json "positive"
          let positive : Bool ← decode s!"{path}.positive" positiveJson
          pure (.atom name positive)
      | "tensor" =>
          requireKeys path json ["kind", "left", "right"]
          let leftJson ← field path json "left"
          let rightJson ← field path json "right"
          return .tensor
            (← formulaFromJsonAtFuel fuel s!"{path}.left" leftJson)
            (← formulaFromJsonAtFuel fuel s!"{path}.right" rightJson)
      | "par" =>
          requireKeys path json ["kind", "left", "right"]
          let leftJson ← field path json "left"
          let rightJson ← field path json "right"
          return .par
            (← formulaFromJsonAtFuel fuel s!"{path}.left" leftJson)
            (← formulaFromJsonAtFuel fuel s!"{path}.right" rightJson)
      | other =>
          throw { path := s!"{path}.kind", message := s!"unsupported formula kind '{other}'" }

def formulaFromJsonAt (path : String) (json : Lean.Json) :
    ParseResult Formula :=
  formulaFromJsonAtFuel maxFormulaDepth path json

def formulaFromJson (json : Lean.Json) : ParseResult Formula :=
  formulaFromJsonAt "$" json

private def vertexField (path : String) (json : Lean.Json)
    (name : String) : ParseResult Vertex := do
  let value ← field path json name
  decode s!"{path}.{name}" value

def linkFromJsonAt (path : String) (json : Lean.Json) : ParseResult Link := do
  let kindJson ← field path json "kind"
  let kind : String ← decode s!"{path}.kind" kindJson
  match kind with
  | "axiom" =>
      requireKeys path json ["kind", "left", "right"]
      return .axiom
        (← vertexField path json "left")
        (← vertexField path json "right")
  | "tensor" =>
      requireKeys path json ["kind", "left", "right", "conclusion"]
      return .tensor
        (← vertexField path json "left")
        (← vertexField path json "right")
        (← vertexField path json "conclusion")
  | "par" =>
      requireKeys path json ["kind", "left", "right", "conclusion"]
      return .par
        (← vertexField path json "left")
        (← vertexField path json "right")
        (← vertexField path json "conclusion")
  | other =>
      throw { path := s!"{path}.kind", message := s!"unsupported link kind '{other}'" }

def linkFromJson (json : Lean.Json) : ParseResult Link :=
  linkFromJsonAt "$" json

/-- Decode the canonical v0.2 wire format. Besides decoding field types, this
checks the version marker and verifies that the claimed canonical ordering is
actually canonical. Logical proof-net validity is deliberately a separate
step, provided by `checkedFromJson`. -/
def fromJson (json : Lean.Json) : ParseResult Certificate := do
  requireKeys "$" json
    ["version", "canonical", "formulas", "links", "conclusions"]
  let versionJson ← field "$" json "version"
  let version : String ← decode "$.version" versionJson
  if version != "0.2" then
    throw { path := "$.version", message := s!"unsupported certificate version '{version}'" }
  let canonicalJson ← field "$" json "canonical"
  let claimedCanonical : Bool ← decode "$.canonical" canonicalJson
  if !claimedCanonical then
    throw { path := "$.canonical", message := "v0.2 input must declare canonical=true" }
  let formulasJson ← field "$" json "formulas"
  let formulas ← parseArray "$.formulas" formulasJson formulaFromJsonAt
  if formulas.isEmpty then
    throw { path := "$.formulas", message := "at least one formula is required" }
  let linksJson ← field "$" json "links"
  let links ← parseArray "$.links" linksJson linkFromJsonAt
  let conclusionsJson ← field "$" json "conclusions"
  let conclusions ← parseArray "$.conclusions" conclusionsJson fun path value =>
    decode path value
  if conclusions.isEmpty then
    throw { path := "$.conclusions", message := "at least one conclusion is required" }
  if conclusions.toList.eraseDups.length != conclusions.size then
    throw { path := "$.conclusions", message := "conclusions must be unique" }
  let certificate : Certificate := {
    formulas
    links := links.toList
    conclusions := conclusions.toList }
  if certificate.canonicalize == certificate then
    pure certificate
  else
    throw { path := "$", message := "certificate claims canonical=true but is not normalized" }

def fromString (input : String) : ParseResult Certificate := do
  let json ← atPath "$" (Lean.Json.parse input)
  fromJson json

/-- Decode v0.2 JSON and expose a certificate only when the kernel-executable
checker accepts it. This is the safe boundary for untrusted external input. -/
def checkedFromJson (json : Lean.Json) :
    ParseResult CutFreeDerivation.CheckedCertificate := do
  let certificate ← fromJson json
  if accepted : certificate.check = true then
    pure ⟨certificate, accepted⟩
  else
    throw { path := "$", message := "proof-net checker rejected certificate" }

def checkedFromString (input : String) :
    ParseResult CutFreeDerivation.CheckedCertificate := do
  let json ← atPath "$" (Lean.Json.parse input)
  checkedFromJson json

end Certificate

end ProofNetIR
