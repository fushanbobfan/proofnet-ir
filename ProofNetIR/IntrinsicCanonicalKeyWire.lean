import ProofNetIR.CanonicalKeyWire
import ProofNetIR.IntrinsicCanonical

namespace ProofNetIR

/-!
# Non-factorial exact canonical-key wire

This is a new wire type rather than a reinterpretation of
`proofnet-canonical-key-0.1`.  Its payload is the injective structural code of
the intrinsic canonical form proved exact in `IntrinsicCanonical.lean`.
-/

/-- Opaque equality-comparable payload for the non-factorial canonical key. -/
structure IntrinsicCanonicalKey where
  tokens : List String
  deriving Repr, DecidableEq, BEq

namespace IntrinsicCanonicalKey

/-- Wire version for the non-factorial exact canonical key. -/
def wireVersion : String := "proofnet-canonical-key-0.2"

/-- Named semantic algorithm implemented by this key. -/
def canonicalization : String := "proofnet-equivalent-intrinsic-v1"

/-- Defensive token-count limit for untrusted intrinsic-key JSON. -/
def maxTokens : Nat := CanonicalKey.maxTokens

/-- Defensive aggregate character-count limit for untrusted intrinsic-key
JSON. -/
def maxCharacters : Nat := CanonicalKey.maxCharacters

/-- The supported intrinsic-key wire envelope.  The limit is independent of
the number of links and is checked after polynomial key generation. -/
def WireAdmissible (key : IntrinsicCanonicalKey) : Prop :=
  key.tokens ≠ [] ∧
    key.tokens.length ≤ maxTokens ∧
    key.tokens.foldl (fun total token => total + token.length) 0 ≤
      maxCharacters

instance (key : IntrinsicCanonicalKey) : Decidable key.WireAdmissible := by
  unfold WireAdmissible
  infer_instance

/-- Executable supported-wire predicate. -/
def isWireAdmissible (key : IntrinsicCanonicalKey) : Bool :=
  decide key.WireAdmissible

/-- Deterministic JSON representation of an intrinsic canonical key. -/
def toJson (key : IntrinsicCanonicalKey) : Lean.Json :=
  Lean.Json.mkObj [
    ("version", wireVersion),
    ("canonicalization", canonicalization),
    ("tokens", .arr (key.tokens.toArray.map Lean.toJson))]

/-- Compact intrinsic canonical-key JSON string. -/
def toString (key : IntrinsicCanonicalKey) : String :=
  key.toJson.compress

private def atPath (path : String) (result : Except String alpha) :
    ParseResult alpha :=
  result.mapError fun message => { path, message }

private def field (path : String) (json : Lean.Json) (name : String) :
    ParseResult Lean.Json :=
  atPath s!"{path}.{name}" (json.getObjVal? name)

private def decode (path : String) [Lean.FromJson alpha]
    (json : Lean.Json) : ParseResult alpha :=
  atPath path (Lean.fromJson? json)

private def requireKeys (path : String) (json : Lean.Json)
    (expected : List String) : ParseResult Unit :=
  match json with
  | .obj fields =>
      match fields.toList.map Prod.fst |>.find? (fun key =>
          !expected.contains key) with
      | some unexpected =>
          throw {
            path := s!"{path}.{unexpected}"
            message := "unexpected property" }
      | none => pure ()
  | _ => throw { path, message := "object expected" }

/-- Decode the intrinsic-key envelope and enforce resource bounds.  Parsing
does not assert that arbitrary tokens came from a proof net. -/
def fromJson (json : Lean.Json) : ParseResult IntrinsicCanonicalKey := do
  requireKeys "$" json ["version", "canonicalization", "tokens"]
  let version : String ← decode "$.version" (← field "$" json "version")
  if version != wireVersion then
    throw {
      path := "$.version"
      message := s!"unsupported intrinsic canonical-key version '{version}'" }
  let algorithm : String ←
    decode "$.canonicalization" (← field "$" json "canonicalization")
  if algorithm != canonicalization then
    throw {
      path := "$.canonicalization"
      message := s!"unsupported intrinsic canonicalization '{algorithm}'" }
  let tokensJson ← field "$" json "tokens"
  let tokenValues ← atPath "$.tokens" tokensJson.getArr?
  if tokenValues.size > maxTokens then
    throw {
      path := "$.tokens"
      message := s!"intrinsic canonical key exceeds {maxTokens} tokens" }
  let tokens ← tokenValues.zipIdx.mapM fun (value, index) =>
    decode s!"$.tokens[{index}]" value
  if tokens.isEmpty then
    throw {
      path := "$.tokens"
      message := "intrinsic canonical key must contain at least one token" }
  let characterCount := tokens.foldl (fun total token =>
    total + token.length) 0
  if characterCount > maxCharacters then
    throw {
      path := "$.tokens"
      message :=
        s!"intrinsic canonical key exceeds {maxCharacters} characters" }
  pure ⟨tokens.toList⟩

/-- Parse an untrusted intrinsic canonical-key string with structured
diagnostics. -/
def fromString (input : String) : ParseResult IntrinsicCanonicalKey := do
  let json ← atPath "$" (Lean.Json.parse input)
  fromJson json

end IntrinsicCanonicalKey

namespace Certificate

/-- Total non-factorial exact key payload.  Reverse exactness requires the
same structural premise as `intrinsicCanonicalize`. -/
def intrinsicCanonicalKey (certificate : Certificate) :
    IntrinsicCanonicalKey :=
  ⟨certificate.intrinsicCanonicalCode⟩

/-- Exact proof-net equivalence preserves the typed intrinsic key. -/
theorem ProofNetEquivalent.intrinsicCanonicalKey_eq
    {left right : Certificate}
    (equivalent : left.ProofNetEquivalent right) :
    left.intrinsicCanonicalKey = right.intrinsicCanonicalKey := by
  simp [intrinsicCanonicalKey,
    equivalent.intrinsicCanonicalCode_eq]

/-- On structurally well-formed certificates, typed intrinsic-key equality is
equivalent to exactly `ProofNetEquivalent`. -/
theorem proofNetEquivalent_iff_intrinsicCanonicalKey_eq
    {left right : Certificate}
    (leftStructural : left.StructurallyWellFormed)
    (rightStructural : right.StructurallyWellFormed) :
    left.ProofNetEquivalent right ↔
      left.intrinsicCanonicalKey = right.intrinsicCanonicalKey := by
  rw [proofNetEquivalent_iff_intrinsicCanonicalCode_eq
    leftStructural rightStructural]
  constructor
  · intro sameCode
    simp [intrinsicCanonicalKey, sameCode]
  · intro sameKey
    injection sameKey

/-- Checker acceptance supplies the structural premises for exact typed
intrinsic-key comparison. -/
theorem proofNetEquivalent_iff_intrinsicCanonicalKey_eq_of_check
    {left right : Certificate}
    (leftAccepted : left.check = true)
    (rightAccepted : right.check = true) :
    left.ProofNetEquivalent right ↔
      left.intrinsicCanonicalKey = right.intrinsicCanonicalKey :=
  proofNetEquivalent_iff_intrinsicCanonicalKey_eq
    (left.check_sound_declarative leftAccepted).1
    (right.check_sound_declarative rightAccepted).1

/-- Wire generation is available for every structurally valid certificate and
has no link-count ceiling.  The independent token/character envelope still
fails closed. -/
def intrinsicCanonicalKeyJson? (certificate : Certificate) :
    Option Lean.Json :=
  if certificate.wellFormed then
    let key := certificate.intrinsicCanonicalKey
    if key.isWireAdmissible then some key.toJson else none
  else
    none

/-- Deterministic intrinsic canonical-key wire string, when the structurally
valid certificate fits the independent wire envelope. -/
def intrinsicCanonicalKeyString? (certificate : Certificate) :
    Option String :=
  certificate.intrinsicCanonicalKeyJson?.map Lean.Json.compress

/-- Safe comparison of an untrusted parsed key with a locally generated
structurally validated key. -/
def matchesIntrinsicCanonicalKey (certificate : Certificate)
    (key : IntrinsicCanonicalKey) : Bool :=
  certificate.wellFormed &&
    key.isWireAdmissible &&
    decide (certificate.intrinsicCanonicalKey = key)

/-- Two structurally validated local certificates matching the same
wire-admissible key are proof-net equivalent. -/
theorem proofNetEquivalent_of_matchesIntrinsicCanonicalKey
    {left right : Certificate} {key : IntrinsicCanonicalKey}
    (leftMatches : left.matchesIntrinsicCanonicalKey key = true)
    (rightMatches : right.matchesIntrinsicCanonicalKey key = true) :
    left.ProofNetEquivalent right := by
  have leftData :
      (left.wellFormed = true ∧
        key.isWireAdmissible = true) ∧
          left.intrinsicCanonicalKey = key := by
    simpa [matchesIntrinsicCanonicalKey] using leftMatches
  have rightData :
      (right.wellFormed = true ∧
        key.isWireAdmissible = true) ∧
          right.intrinsicCanonicalKey = key := by
    simpa [matchesIntrinsicCanonicalKey] using rightMatches
  apply (proofNetEquivalent_iff_intrinsicCanonicalKey_eq
    (left.wellFormed_iff_structurallyWellFormed.mp leftData.1.1)
    (right.wellFormed_iff_structurallyWellFormed.mp rightData.1.1)).mpr
  exact leftData.2.trans rightData.2.symm

/-- Semantic migration from a checker-accepted v0.3 certificate.  A bare v0.1
canonical key cannot be migrated without its source certificate because the
new deterministic representative need not be the old factorial minimum. -/
def migrateV03StringToIntrinsicCanonicalKey (input : String) :
    ParseResult String := do
  let json ← (Lean.Json.parse input).mapError fun message =>
    ({ path := "$", message } : ParseError)
  let certificate ← Certificate.fromJsonV03 json
  if _accepted : certificate.check = true then
    match certificate.intrinsicCanonicalKeyString? with
    | some output => pure output
    | none =>
        throw {
          path := "$"
          message := "intrinsic canonical key exceeds the wire envelope" }
  else
    throw {
      path := "$"
      message := "proof-net checker rejected certificate" }

end Certificate

end ProofNetIR
