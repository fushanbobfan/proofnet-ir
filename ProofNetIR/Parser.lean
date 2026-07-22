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

/-- Parser result with a structured JSON path and diagnostic on failure. -/
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

private def payloadFromJson (json : Lean.Json) : ParseResult Certificate := do
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
  pure certificate

/-- Decode the fixed-numbering canonical v0.2 wire format. -/
def fromJsonV02 (json : Lean.Json) : ParseResult Certificate := do
  requireKeys "$" json
    ["version", "canonical", "formulas", "links", "conclusions"]
  let versionJson ← field "$" json "version"
  let version : String ← decode "$.version" versionJson
  if version != "0.2" then
    throw { path := "$.version", message := "v0.2 input required" }
  let canonicalJson ← field "$" json "canonical"
  let claimedCanonical : Bool ← decode "$.canonical" canonicalJson
  if !claimedCanonical then
    throw { path := "$.canonical", message := "v0.2 input must declare canonical=true" }
  let certificate ← payloadFromJson json
  if certificate.canonicalize == certificate then
    pure certificate
  else
    throw { path := "$", message := "certificate claims canonical=true but is not normalized" }

/-- Decode the reindexing-invariant v0.3 wire format. The canonicalization
algorithm is named in the payload so later algorithms can be versioned without
silently changing proof identity. -/
def fromJsonV03 (json : Lean.Json) : ParseResult Certificate := do
  requireKeys "$" json
    ["version", "canonical", "canonicalization", "formulas", "links",
      "conclusions"]
  let versionJson ← field "$" json "version"
  let version : String ← decode "$.version" versionJson
  if version != "0.3" then
    throw { path := "$.version", message := "v0.3 input required" }
  let canonicalJson ← field "$" json "canonical"
  let claimedCanonical : Bool ← decode "$.canonical" canonicalJson
  if !claimedCanonical then
    throw { path := "$.canonical", message := "v0.3 input must declare canonical=true" }
  let algorithmJson ← field "$" json "canonicalization"
  let algorithm : String ← decode "$.canonicalization" algorithmJson
  if algorithm != "reindex-v1" then
    throw { path := "$.canonicalization", message := s!"unsupported canonicalization '{algorithm}'" }
  let certificate ← payloadFromJson json
  if certificate.equivalenceCanonicalize == certificate then
    pure certificate
  else
    throw { path := "$", message := "v0.3 certificate is not reindex-v1 canonical" }

/-- Dispatch between every supported certificate wire version. Logical
proof-net validity remains a separate checker-gated step. -/
def fromJson (json : Lean.Json) : ParseResult Certificate := do
  let versionJson ← field "$" json "version"
  let version : String ← decode "$.version" versionJson
  match version with
  | "0.2" => fromJsonV02 json
  | "0.3" => fromJsonV03 json
  | other =>
      throw { path := "$.version", message := s!"unsupported certificate version '{other}'" }

/-- Parse canonical v0.2 or v0.3 JSON without asserting proof-net correctness. -/
def fromString (input : String) : ParseResult Certificate := do
  let json ← atPath "$" (Lean.Json.parse input)
  fromJson json

/-- Parse a v0.2 certificate and emit its deterministic v0.3
`reindex-v1` representation. -/
def migrateV02StringToV03 (input : String) : ParseResult String := do
  let json ← atPath "$" (Lean.Json.parse input)
  let certificate ← fromJsonV02 json
  pure certificate.equivalenceCanonicalString

/-- Decode supported JSON and expose a certificate only when the
kernel-executable checker accepts it. This is the safe boundary for untrusted
external input. -/
def checkedFromJson (json : Lean.Json) :
    ParseResult CutFreeDerivation.CheckedCertificate := do
  let certificate ← fromJson json
  if accepted : certificate.check = true then
    pure ⟨certificate, accepted⟩
  else
    throw { path := "$", message := "proof-net checker rejected certificate" }

/-- Parse untrusted canonical JSON and return a certificate only after the
reference checker accepts it. -/
def checkedFromString (input : String) :
    ParseResult CutFreeDerivation.CheckedCertificate := do
  let json ← atPath "$" (Lean.Json.parse input)
  checkedFromJson json

end Certificate

end ProofNetIR
