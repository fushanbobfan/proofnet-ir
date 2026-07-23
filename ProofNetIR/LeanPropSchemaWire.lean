import Lean.Data.Json
import ProofNetIR.LeanPropElaboration

namespace ProofNetIR.LeanProp.Schema.Raw

/-!
# Versioned LeanProp schema wire format

The wire format is deliberately distinct from the MLL certificate formats.
Parsing reconstructs only raw syntax; `checkedFromString` additionally runs the
resource-aware elaborator and returns a kernel-typed indexed derivation.
-/

/-- Structured failures at either the JSON boundary or the schema checker. -/
inductive InputError where
  | json (path message : String)
  | checker (error : Error)
  deriving Repr, DecidableEq

namespace InputError

/-- Render a wire error without discarding checker categories or child paths. -/
def render : InputError → String
  | .json path message => s!"{path}: {message}"
  | .checker error =>
      let path := error.path.foldl
        (fun value index => s!"{value}/{index}") "$.derivation"
      s!"{path}: {repr error.code}: {error.detail}"

end InputError

/-- Versioned schema parsing/checking result. -/
abbrev InputResult (alpha : Type) := Except InputError alpha

/-- A raw schema accompanied by the indexed derivation built by the checker. -/
structure CheckedDerivation where
  derivation : Derivation
  elaborated : ElaboratedDerivation
  accepted : derivation.elaborate? = .ok elaborated

namespace CheckedDerivation

/-- The exact persistent, linear, and goal boundary reconstructed by checking. -/
def sequent (checked : CheckedDerivation) : Sequent :=
  checked.elaborated.sequent

/-- Package checked external input for valuation-independent soundness. -/
def toPacked (name : String) (checked : CheckedDerivation) :
    Schema.PackedDerivation :=
  checked.elaborated.toPacked name

/-- The independent formula-only checker returns the same accepted boundary. -/
theorem inferred (checked : CheckedDerivation) :
    checked.derivation.infer? = .ok checked.sequent := by
  rw [Derivation.infer?, Derivation.inferAt_eq_elaborateAt]
  change Derivation.sequentResult checked.derivation.elaborate? =
    .ok checked.sequent
  rw [checked.accepted]
  rfl

/-- Every checked external schema reconstructs a Lean proof for every valuation
and matching persistent/linear proof environment. -/
theorem sound (checked : CheckedDerivation) (valuation : String → Prop)
    (persistentValues : LeanProp.Assumptions
      (checked.elaborated.persistent.map (Formula.evaluate valuation)))
    (linearValues : LeanProp.Assumptions
      (checked.elaborated.linear.map (Formula.evaluate valuation))) :
    checked.elaborated.goal.evaluate valuation :=
  (checked.toPacked "checked-wire-input").sound valuation
    persistentValues linearValues

end CheckedDerivation

private def atPath (path : String) (result : Except String alpha) :
    InputResult alpha :=
  result.mapError fun message => .json path message

private def field (path : String) (json : Lean.Json) (name : String) :
    InputResult Lean.Json :=
  atPath s!"{path}.{name}" (json.getObjVal? name)

private def decode (path : String) [Lean.FromJson alpha]
    (json : Lean.Json) : InputResult alpha :=
  atPath path (Lean.fromJson? json)

private def array (path : String) (json : Lean.Json) :
    InputResult (Array Lean.Json) :=
  atPath path json.getArr?

private def requireKeys (path : String) (json : Lean.Json)
    (expected : List String) : InputResult Unit :=
  match json with
  | .obj fields =>
      match fields.toList.map Prod.fst |>.find? (fun key =>
          !expected.contains key) with
      | some unexpected =>
          .error (.json s!"{path}.{unexpected}" "unexpected property")
      | none => .ok ()
  | _ => .error (.json path "object expected")

private def parseList (path : String) (json : Lean.Json)
    (parse : String → Lean.Json → InputResult alpha) :
    InputResult (List alpha) := do
  let values ← array path json
  let parsed ← values.zipIdx.mapM fun (value, index) =>
    parse s!"{path}[{index}]" value
  pure parsed.toList

private def maxDepth : Nat := 2048

namespace FormulaWire

/-- Deterministic JSON representation of a first-order schema formula. -/
def toJson : Formula → Lean.Json
  | .atom name => Lean.Json.mkObj [
      ("kind", "atom"), ("name", name)]
  | .and left right => Lean.Json.mkObj [
      ("kind", "and"), ("left", toJson left), ("right", toJson right)]
  | .imp antecedent consequent => Lean.Json.mkObj [
      ("kind", "imp"), ("antecedent", toJson antecedent),
      ("consequent", toJson consequent)]

private def fromJsonAtFuel : Nat → String → Lean.Json → InputResult Formula
  | 0, path, _ => .error (.json path s!"formula nesting exceeds {maxDepth}")
  | fuel + 1, path, json => do
      let kind : String ← decode s!"{path}.kind" (← field path json "kind")
      match kind with
      | "atom" =>
          requireKeys path json ["kind", "name"]
          return .atom (← decode s!"{path}.name" (← field path json "name"))
      | "and" =>
          requireKeys path json ["kind", "left", "right"]
          return .and
            (← fromJsonAtFuel fuel s!"{path}.left" (← field path json "left"))
            (← fromJsonAtFuel fuel s!"{path}.right" (← field path json "right"))
      | "imp" =>
          requireKeys path json ["kind", "antecedent", "consequent"]
          return .imp
            (← fromJsonAtFuel fuel s!"{path}.antecedent"
              (← field path json "antecedent"))
            (← fromJsonAtFuel fuel s!"{path}.consequent"
              (← field path json "consequent"))
      | other => .error (.json s!"{path}.kind"
          s!"unsupported formula kind '{other}'")

/-- Parse a formula at a supplied JSON path. -/
def fromJsonAt (path : String) (json : Lean.Json) : InputResult Formula :=
  fromJsonAtFuel maxDepth path json

end FormulaWire

namespace Permutation

/-- Deterministic JSON representation of raw exchange data. -/
def toJson : Permutation → Lean.Json
  | .nil => Lean.Json.mkObj [("kind", "nil")]
  | .cons formula tail => Lean.Json.mkObj [
      ("kind", "cons"), ("formula", FormulaWire.toJson formula),
      ("tail", toJson tail)]
  | .swap first second rest => Lean.Json.mkObj [
      ("kind", "swap"), ("first", FormulaWire.toJson first),
      ("second", FormulaWire.toJson second),
      ("rest", .arr (rest.toArray.map FormulaWire.toJson))]
  | .trans first second => Lean.Json.mkObj [
      ("kind", "trans"), ("first", toJson first),
      ("second", toJson second)]

private def fromJsonAtFuel : Nat → String → Lean.Json →
    InputResult Permutation
  | 0, path, _ =>
      .error (.json path s!"permutation nesting exceeds {maxDepth}")
  | fuel + 1, path, json => do
      let kind : String ← decode s!"{path}.kind" (← field path json "kind")
      match kind with
      | "nil" =>
          requireKeys path json ["kind"]
          return .nil
      | "cons" =>
          requireKeys path json ["kind", "formula", "tail"]
          return .cons
            (← FormulaWire.fromJsonAt s!"{path}.formula"
              (← field path json "formula"))
            (← fromJsonAtFuel fuel s!"{path}.tail"
              (← field path json "tail"))
      | "swap" =>
          requireKeys path json ["kind", "first", "second", "rest"]
          return .swap
            (← FormulaWire.fromJsonAt s!"{path}.first"
              (← field path json "first"))
            (← FormulaWire.fromJsonAt s!"{path}.second"
              (← field path json "second"))
            (← parseList s!"{path}.rest" (← field path json "rest")
              FormulaWire.fromJsonAt)
      | "trans" =>
          requireKeys path json ["kind", "first", "second"]
          return .trans
            (← fromJsonAtFuel fuel s!"{path}.first"
              (← field path json "first"))
            (← fromJsonAtFuel fuel s!"{path}.second"
              (← field path json "second"))
      | other => .error (.json s!"{path}.kind"
          s!"unsupported permutation kind '{other}'")

/-- Parse raw exchange data at a supplied JSON path. -/
def fromJsonAt (path : String) (json : Lean.Json) : InputResult Permutation :=
  fromJsonAtFuel maxDepth path json

end Permutation

namespace Derivation

private def formulaField (path : String) (json : Lean.Json) (name : String) :
    InputResult Formula := do
  FormulaWire.fromJsonAt s!"{path}.{name}" (← field path json name)

/-- Deterministic JSON representation of an unindexed proof schema. -/
def toJson : Derivation → Lean.Json
  | .persistentAxiom formula => Lean.Json.mkObj [
      ("kind", "persistent-axiom"),
      ("formula", FormulaWire.toJson formula)]
  | .linearAxiom formula => Lean.Json.mkObj [
      ("kind", "linear-axiom"), ("formula", FormulaWire.toJson formula)]
  | .persistentWeaken extra premise => Lean.Json.mkObj [
      ("kind", "persistent-weaken"),
      ("extra", FormulaWire.toJson extra),
      ("premise", toJson premise)]
  | .persistentContract shared premise => Lean.Json.mkObj [
      ("kind", "persistent-contract"),
      ("shared", FormulaWire.toJson shared),
      ("premise", toJson premise)]
  | .persistentExchange permutation premise => Lean.Json.mkObj [
      ("kind", "persistent-exchange"),
      ("permutation", permutation.toJson), ("premise", toJson premise)]
  | .linearExchange permutation premise => Lean.Json.mkObj [
      ("kind", "linear-exchange"),
      ("permutation", permutation.toJson), ("premise", toJson premise)]
  | .andIntro left right => Lean.Json.mkObj [
      ("kind", "and-intro"), ("left", toJson left),
      ("right", toJson right)]
  | .andElimLeft premise => Lean.Json.mkObj [
      ("kind", "and-elim-left"), ("premise", toJson premise)]
  | .andElimRight premise => Lean.Json.mkObj [
      ("kind", "and-elim-right"), ("premise", toJson premise)]
  | .impIntro antecedent premise => Lean.Json.mkObj [
      ("kind", "imp-intro"),
      ("antecedent", FormulaWire.toJson antecedent),
      ("premise", toJson premise)]
  | .impElim function argument => Lean.Json.mkObj [
      ("kind", "imp-elim"), ("function", toJson function),
      ("argument", toJson argument)]

private def fromJsonAtFuel : Nat → String → Lean.Json →
    InputResult Derivation
  | 0, path, _ =>
      .error (.json path s!"derivation nesting exceeds {maxDepth}")
  | fuel + 1, path, json => do
      let kind : String ← decode s!"{path}.kind" (← field path json "kind")
      match kind with
      | "persistent-axiom" =>
          requireKeys path json ["kind", "formula"]
          return .persistentAxiom (← formulaField path json "formula")
      | "linear-axiom" =>
          requireKeys path json ["kind", "formula"]
          return .linearAxiom (← formulaField path json "formula")
      | "persistent-weaken" =>
          requireKeys path json ["kind", "extra", "premise"]
          return .persistentWeaken (← formulaField path json "extra")
            (← fromJsonAtFuel fuel s!"{path}.premise"
              (← field path json "premise"))
      | "persistent-contract" =>
          requireKeys path json ["kind", "shared", "premise"]
          return .persistentContract (← formulaField path json "shared")
            (← fromJsonAtFuel fuel s!"{path}.premise"
              (← field path json "premise"))
      | "persistent-exchange" =>
          requireKeys path json ["kind", "permutation", "premise"]
          return .persistentExchange
            (← Permutation.fromJsonAt s!"{path}.permutation"
              (← field path json "permutation"))
            (← fromJsonAtFuel fuel s!"{path}.premise"
              (← field path json "premise"))
      | "linear-exchange" =>
          requireKeys path json ["kind", "permutation", "premise"]
          return .linearExchange
            (← Permutation.fromJsonAt s!"{path}.permutation"
              (← field path json "permutation"))
            (← fromJsonAtFuel fuel s!"{path}.premise"
              (← field path json "premise"))
      | "and-intro" =>
          requireKeys path json ["kind", "left", "right"]
          return .andIntro
            (← fromJsonAtFuel fuel s!"{path}.left"
              (← field path json "left"))
            (← fromJsonAtFuel fuel s!"{path}.right"
              (← field path json "right"))
      | "and-elim-left" =>
          requireKeys path json ["kind", "premise"]
          return .andElimLeft
            (← fromJsonAtFuel fuel s!"{path}.premise"
              (← field path json "premise"))
      | "and-elim-right" =>
          requireKeys path json ["kind", "premise"]
          return .andElimRight
            (← fromJsonAtFuel fuel s!"{path}.premise"
              (← field path json "premise"))
      | "imp-intro" =>
          requireKeys path json ["kind", "antecedent", "premise"]
          return .impIntro (← formulaField path json "antecedent")
            (← fromJsonAtFuel fuel s!"{path}.premise"
              (← field path json "premise"))
      | "imp-elim" =>
          requireKeys path json ["kind", "function", "argument"]
          return .impElim
            (← fromJsonAtFuel fuel s!"{path}.function"
              (← field path json "function"))
            (← fromJsonAtFuel fuel s!"{path}.argument"
              (← field path json "argument"))
      | other => .error (.json s!"{path}.kind"
          s!"unsupported derivation kind '{other}'")

/-- Parse a raw proof schema at a supplied JSON path. -/
def fromJsonAt (path : String) (json : Lean.Json) : InputResult Derivation :=
  fromJsonAtFuel maxDepth path json

/-- Versioned deterministic JSON value for an unindexed LeanProp schema. -/
def canonicalJson (derivation : Derivation) : Lean.Json :=
  Lean.Json.mkObj [
    ("version", "leanprop-schema-0.1"),
    ("derivation", derivation.toJson)]

/-- Compact canonical LeanProp schema JSON. -/
def canonicalString (derivation : Derivation) : String :=
  derivation.canonicalJson.compress

/-- Decode the first LeanProp schema wire version without asserting that its
rule applications are valid. -/
def fromJson (json : Lean.Json) : InputResult Derivation := do
  requireKeys "$" json ["version", "derivation"]
  let version : String ← decode "$.version" (← field "$" json "version")
  if version != "leanprop-schema-0.1" then
    .error (.json "$.version" s!"unsupported LeanProp schema version '{version}'")
  else
    fromJsonAt "$.derivation" (← field "$" json "derivation")

/-- Parse versioned schema JSON into untrusted raw syntax. -/
def fromString (input : String) : InputResult Derivation := do
  let json ← atPath "$" (Lean.Json.parse input)
  fromJson json

/-- Check parsed raw syntax and retain its kernel-typed indexed derivation. -/
def check (derivation : Derivation) : InputResult CheckedDerivation :=
  match equation : derivation.elaborate? with
  | .ok elaborated => .ok ⟨derivation, elaborated, equation⟩
  | .error error => .error (.checker error)

/-- Decode JSON and expose a schema only after resource-aware inference
succeeds. -/
def checkedFromJson (json : Lean.Json) : InputResult CheckedDerivation := do
  check (← fromJson json)

/-- Safe entry point for untrusted LeanProp schema strings. -/
def checkedFromString (input : String) : InputResult CheckedDerivation := do
  check (← fromString input)

end Derivation

end ProofNetIR.LeanProp.Schema.Raw
