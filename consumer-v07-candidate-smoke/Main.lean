import ProofNetIR

open ProofNetIR

namespace ProofNetIRV07CandidateConsumerSmoke

def certificate : Certificate :=
  identityCertificate (.tensor (.atom "remote-p" true) (.atom "remote-q" true))

def reordered : Certificate :=
  { certificate with links := certificate.links.reverse }

def generatedKey : CanonicalKey :=
  certificate.proofNetCanonicalKeyWithinLimit?.get (by native_decide)

example : certificate.check = true := by native_decide

example : certificate.links.length ≤ CanonicalKey.maxGenerationLinks := by
  native_decide

example :
    certificate.ProofNetEquivalent reordered ↔
      certificate.proofNetCanonicalKeyWithinLimit? =
        reordered.proofNetCanonicalKeyWithinLimit? :=
  Certificate.proofNetEquivalent_iff_canonicalKeyWithinLimit_of_check
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)

example : certificate.matchesCanonicalKey generatedKey = true := by
  native_decide

example : reordered.matchesCanonicalKey generatedKey = true := by
  native_decide

example : certificate.ProofNetEquivalent reordered :=
  Certificate.proofNetEquivalent_of_matchesCanonicalKey
    (key := generatedKey)
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)

def parsedKey : ParseResult CanonicalKey :=
  CanonicalKey.fromString generatedKey.toString

example : parsedKey.isOk = true := by native_decide

def overLimit : Certificate :=
  { certificate with links := List.replicate 8 (.axiom 0 1) }

example : overLimit.proofNetCanonicalKeyWithinLimit?.isNone = true := by
  native_decide

example : overLimit.matchesCanonicalKey generatedKey = false := by
  native_decide

example : ∃ result, certificate.sequentialize = .ok result :=
  certificate.sequentialize_complete (by native_decide)

def run : IO Unit := do
  if certificate.check &&
      certificate.matchesCanonicalKey generatedKey &&
      reordered.matchesCanonicalKey generatedKey &&
      parsedKey.isOk &&
      overLimit.proofNetCanonicalKeyWithinLimit?.isNone then
    IO.println "ProofNetIR pinned-v0.7-candidate consumer smoke test passed"
  else
    throw <| IO.userError
      "ProofNetIR pinned-v0.7-candidate consumer smoke test failed"

end ProofNetIRV07CandidateConsumerSmoke

def main : IO Unit :=
  ProofNetIRV07CandidateConsumerSmoke.run
