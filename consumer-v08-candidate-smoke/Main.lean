import ProofNetIR

open ProofNetIR

namespace ProofNetIRV08CandidateConsumerSmoke

def rightNestedFormula : Nat → Formula
  | 0 => .atom "remote-intrinsic-base" true
  | depth + 1 =>
      .tensor (rightNestedFormula depth)
        (.atom s!"remote-intrinsic-right-{depth}" true)

def certificate : Certificate :=
  identityCertificate (rightNestedFormula 8)

def reordered : Certificate :=
  { certificate with links := certificate.links.reverse }

def generatedKey : IntrinsicCanonicalKey :=
  certificate.intrinsicCanonicalKey

example : certificate.check = true := by native_decide

example : certificate.links.length > CanonicalKey.maxGenerationLinks := by
  native_decide

example : certificate.proofNetCanonicalKeyString? = none := by
  native_decide

example : certificate.intrinsicCanonicalKeyString?.isSome = true := by
  native_decide

example :
    certificate.ProofNetEquivalent reordered ↔
      certificate.intrinsicCanonicalKey =
        reordered.intrinsicCanonicalKey :=
  Certificate.proofNetEquivalent_iff_intrinsicCanonicalKey_eq_of_check
    (by native_decide) (by native_decide)

example : certificate.matchesIntrinsicCanonicalKey generatedKey = true := by
  native_decide

example : reordered.matchesIntrinsicCanonicalKey generatedKey = true := by
  native_decide

example : certificate.ProofNetEquivalent reordered :=
  Certificate.proofNetEquivalent_of_matchesIntrinsicCanonicalKey
    (key := generatedKey)
    (by native_decide) (by native_decide)

def parsedKey : ParseResult IntrinsicCanonicalKey :=
  IntrinsicCanonicalKey.fromString generatedKey.toString

example : parsedKey.isOk = true := by native_decide

def migratedKey : ParseResult String :=
  Certificate.migrateV03StringToIntrinsicCanonicalKey
    certificate.equivalenceCanonicalString

example : migratedKey.isOk = true := by native_decide

def run : IO Unit := do
  if certificate.check &&
      certificate.proofNetCanonicalKeyString?.isNone &&
      certificate.intrinsicCanonicalKeyString?.isSome &&
      certificate.matchesIntrinsicCanonicalKey generatedKey &&
      reordered.matchesIntrinsicCanonicalKey generatedKey &&
      parsedKey.isOk &&
      migratedKey.isOk then
    IO.println "ProofNetIR pinned-v0.8 candidate consumer smoke test passed"
  else
    throw <| IO.userError
      "ProofNetIR pinned-v0.8 candidate consumer smoke test failed"

end ProofNetIRV08CandidateConsumerSmoke

def main : IO Unit :=
  ProofNetIRV08CandidateConsumerSmoke.run
