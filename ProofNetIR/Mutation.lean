import ProofNetIR.Certificate

namespace ProofNetIR

/-- Labeled, deterministic certificate corruptions used to build negative
fixtures from known-valid proof nets. A mutation is not claimed to invalidate
every possible input; each generated fixture must still be checked. -/
inductive Mutation where
  | dropFirstLink
  | duplicateFirstLink
  | replaceFirstAxiomRight (right : Vertex)
  deriving Repr, DecidableEq, BEq

namespace Mutation

def apply : Mutation → Certificate → Certificate
  | .dropFirstLink, certificate =>
      { certificate with links := certificate.links.drop 1 }
  | .duplicateFirstLink, certificate =>
      match certificate.links with
      | [] => certificate
      | first :: _ => { certificate with links := first :: certificate.links }
  | .replaceFirstAxiomRight right, certificate =>
      match certificate.links with
      | .axiom left _ :: rest =>
          { certificate with links := .axiom left right :: rest }
      | _ => certificate

end Mutation
end ProofNetIR
