import ProofNetIR.Parser
import ProofNetIR.ProofNetCanonical

namespace ProofNetIR

/-!
# Versioned wire wrapper for the exact proof-net canonical key

The equality-reflecting payload is the typed token code proved exact in
`ProofNetCanonical.lean`.  This module gives that payload a distinct JSON
contract.  It does not reinterpret the certificate v0.2/v0.3 formats.

Parsing a key only validates its wire shape.  The safe untrusted-input
operation is to compare the parsed key with a locally computed key from a
checker-accepted certificate.
-/

/-- Opaque, equality-comparable canonical key payload.  Values produced by
`Certificate.proofNetCanonicalKey?` carry the exact `ProofNetEquivalent`
semantics; arbitrary parsed values must be matched against such a local key. -/
structure CanonicalKey where
  tokens : List String
  deriving Repr, DecidableEq, BEq

namespace CanonicalKey

/-- Wire version for the first exact proof-net canonical key. -/
def wireVersion : String := "proofnet-canonical-key-0.1"

/-- Named semantic relation implemented by the key. -/
def canonicalization : String := "proofnet-equivalent-v1"

/-- Defensive token-count limit for untrusted key JSON. -/
def maxTokens : Nat := 100000

/-- Defensive aggregate character-count limit for untrusted key JSON. -/
def maxCharacters : Nat := 1000000

/-- The supported wire envelope is deliberately bounded even though the typed
canonical key remains total for every finite certificate. -/
def WireAdmissible (key : CanonicalKey) : Prop :=
  key.tokens ≠ [] ∧
    key.tokens.length ≤ maxTokens ∧
    key.tokens.foldl (fun total token => total + token.length) 0 ≤
      maxCharacters

instance (key : CanonicalKey) : Decidable key.WireAdmissible :=
  by
    unfold WireAdmissible
    infer_instance

/-- Executable supported-wire predicate. -/
def isWireAdmissible (key : CanonicalKey) : Bool :=
  decide key.WireAdmissible

/-- Deterministic JSON representation of a canonical key. -/
def toJson (key : CanonicalKey) : Lean.Json :=
  Lean.Json.mkObj [
    ("version", wireVersion),
    ("canonicalization", canonicalization),
    ("tokens", .arr (key.tokens.toArray.map Lean.toJson))]

/-- Compact canonical-key JSON string. -/
def toString (key : CanonicalKey) : String :=
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

/-- Decode the first canonical-key wire version.  This validates the envelope
and resource bounds but does not claim that arbitrary tokens came from a proof
net. -/
def fromJson (json : Lean.Json) : ParseResult CanonicalKey := do
  requireKeys "$" json ["version", "canonicalization", "tokens"]
  let version : String ← decode "$.version" (← field "$" json "version")
  if version != wireVersion then
    throw {
      path := "$.version"
      message := s!"unsupported canonical-key version '{version}'" }
  let algorithm : String ←
    decode "$.canonicalization" (← field "$" json "canonicalization")
  if algorithm != canonicalization then
    throw {
      path := "$.canonicalization"
      message := s!"unsupported canonicalization '{algorithm}'" }
  let tokensJson ← field "$" json "tokens"
  let tokenValues ← atPath "$.tokens" tokensJson.getArr?
  if tokenValues.size > maxTokens then
    throw {
      path := "$.tokens"
      message := s!"canonical key exceeds {maxTokens} tokens" }
  let tokens ← tokenValues.zipIdx.mapM fun (value, index) =>
    decode s!"$.tokens[{index}]" value
  if tokens.isEmpty then
    throw {
      path := "$.tokens"
      message := "canonical key must contain at least one token" }
  let characterCount := tokens.foldl (fun total token =>
    total + token.length) 0
  if characterCount > maxCharacters then
    throw {
      path := "$.tokens"
      message := s!"canonical key exceeds {maxCharacters} characters" }
  pure ⟨tokens.toList⟩

/-- Parse an untrusted canonical-key string with structured diagnostics. -/
def fromString (input : String) : ParseResult CanonicalKey := do
  let json ← atPath "$" (Lean.Json.parse input)
  fromJson json

end CanonicalKey

namespace Certificate

/-- Exact typed canonical key for the generated `ProofNetEquivalent` relation.
The option is total by `proofNetCanonicalKey?_exists`. -/
def proofNetCanonicalKey? (certificate : Certificate) :
    Option CanonicalKey :=
  certificate.proofNetCanonicalCode?.map CanonicalKey.mk

/-- Deterministic JSON wire value for the exact typed canonical key. -/
def proofNetCanonicalKeyJson? (certificate : Certificate) :
    Option Lean.Json :=
  certificate.proofNetCanonicalKey?.bind fun key =>
    if key.isWireAdmissible then some key.toJson else none

/-- Deterministic JSON wire string for the exact typed canonical key. -/
def proofNetCanonicalKeyString? (certificate : Certificate) :
    Option String :=
  certificate.proofNetCanonicalKey?.bind fun key =>
    if key.isWireAdmissible then some key.toString else none

/-- Every certificate has a typed canonical key. -/
theorem proofNetCanonicalKey?_exists (certificate : Certificate) :
    ∃ key, certificate.proofNetCanonicalKey? = some key := by
  rcases certificate.proofNetCanonicalCode?_exists with ⟨code, equation⟩
  exact ⟨⟨code⟩, by simp [proofNetCanonicalKey?, equation]⟩

/-- Generated proof-net equivalence preserves the typed wire key. -/
theorem ProofNetEquivalent.proofNetCanonicalKey?_eq
    {left right : Certificate}
    (equivalent : left.ProofNetEquivalent right) :
    left.proofNetCanonicalKey? = right.proofNetCanonicalKey? := by
  simp [proofNetCanonicalKey?, equivalent.proofNetCanonicalCode?_eq]

/-- On structurally well-formed certificates, typed wire-key equality is
equivalent to exactly `ProofNetEquivalent`. -/
theorem proofNetEquivalent_iff_canonicalKey
    {left right : Certificate}
    (leftStructural : left.StructurallyWellFormed)
    (rightStructural : right.StructurallyWellFormed) :
    left.ProofNetEquivalent right ↔
      left.proofNetCanonicalKey? = right.proofNetCanonicalKey? := by
  rw [proofNetEquivalent_iff_canonicalCode leftStructural rightStructural]
  constructor
  · intro sameCode
    simp [proofNetCanonicalKey?, sameCode]
  · intro sameKey
    cases leftEquation : left.proofNetCanonicalCode? with
    | none =>
        cases rightEquation : right.proofNetCanonicalCode? with
        | none => rfl
        | some rightCode =>
            simp [proofNetCanonicalKey?, leftEquation, rightEquation] at sameKey
    | some leftCode =>
        cases rightEquation : right.proofNetCanonicalCode? with
        | none =>
            simp [proofNetCanonicalKey?, leftEquation, rightEquation] at sameKey
        | some rightCode =>
            simp [proofNetCanonicalKey?, leftEquation, rightEquation] at sameKey
            simp [sameKey]

/-- Checker acceptance supplies the premises for exact typed wire-key
comparison. -/
theorem proofNetEquivalent_iff_canonicalKey_of_check
    {left right : Certificate}
    (leftAccepted : left.check = true)
    (rightAccepted : right.check = true) :
    left.ProofNetEquivalent right ↔
      left.proofNetCanonicalKey? = right.proofNetCanonicalKey? :=
  proofNetEquivalent_iff_canonicalKey
    (left.check_sound_declarative leftAccepted).1
    (right.check_sound_declarative rightAccepted).1

/-- Compare a locally computed key with a parsed opaque key. -/
def matchesCanonicalKey (certificate : Certificate)
    (key : CanonicalKey) : Bool :=
  decide (certificate.proofNetCanonicalKey? = some key)

/-- A parsed key shared by two accepted certificates is sufficient to prove
that the certificates are `ProofNetEquivalent`. -/
theorem proofNetEquivalent_of_matchesCanonicalKey
    {left right : Certificate} {key : CanonicalKey}
    (leftAccepted : left.check = true)
    (rightAccepted : right.check = true)
    (leftMatches : left.matchesCanonicalKey key = true)
    (rightMatches : right.matchesCanonicalKey key = true) :
    left.ProofNetEquivalent right := by
  have leftEquation :
      left.proofNetCanonicalKey? = some key := by
    exact of_decide_eq_true leftMatches
  have rightEquation :
      right.proofNetCanonicalKey? = some key := by
    exact of_decide_eq_true rightMatches
  apply (proofNetEquivalent_iff_canonicalKey_of_check
    leftAccepted rightAccepted).mpr
  exact leftEquation.trans rightEquation.symm

/-- Parse a checker-accepted v0.3 certificate and emit the new exact
`proofnet-equivalent-v1` key.  This is a semantic migration to a separate wire
type; it does not reinterpret the input certificate bytes. -/
def migrateV03StringToCanonicalKey (input : String) :
    ParseResult String := do
  let json ← (Lean.Json.parse input).mapError fun message =>
    ({ path := "$", message } : ParseError)
  let certificate ← Certificate.fromJsonV03 json
  if _accepted : certificate.check = true then
    match certificate.proofNetCanonicalKeyString? with
    | some output => pure output
    | none =>
        throw {
          path := "$"
          message := "internal canonical-key construction returned none" }
  else
    throw {
      path := "$"
      message := "proof-net checker rejected certificate" }

end Certificate

end ProofNetIR
