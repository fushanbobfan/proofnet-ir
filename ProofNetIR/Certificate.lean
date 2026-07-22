import ProofNetIR.Formula

namespace ProofNetIR

abbrev Vertex := Nat

/-- Local proof-net links. Formula occurrences are addressed by array index. -/
inductive Link where
  | axiom (left right : Vertex)
  | tensor (left right conclusion : Vertex)
  | par (left right conclusion : Vertex)
  deriving Repr, DecidableEq, BEq

namespace Link

def vertices : Link → List Vertex
  | .axiom left right => [left, right]
  | .tensor left right conclusion => [left, right, conclusion]
  | .par left right conclusion => [left, right, conclusion]

def premises : Link → List Vertex
  | .axiom _ _ => []
  | .tensor left right _ => [left, right]
  | .par left right _ => [left, right]

def produces (vertex : Vertex) : Link → Bool
  | .axiom _ _ => false
  | .tensor _ _ conclusion => conclusion == vertex
  | .par _ _ conclusion => conclusion == vertex

def containsAxiomEndpoint (vertex : Vertex) : Link → Bool
  | .axiom left right => left == vertex || right == vertex
  | _ => false

def usesAsPremise (vertex : Vertex) (link : Link) : Bool :=
  link.premises.contains vertex

end Link

/-- A cut-free proof-net certificate over an explicit formula-occurrence array. -/
structure Certificate where
  formulas : Array Formula
  links : List Link
  conclusions : List Vertex
  deriving Repr, DecidableEq, BEq

namespace Certificate

def formula? (certificate : Certificate) (vertex : Vertex) : Option Formula :=
  certificate.formulas[vertex]?

def inBounds (certificate : Certificate) (vertex : Vertex) : Bool :=
  vertex < certificate.formulas.size

def linkLocallyWellFormed (certificate : Certificate) : Link → Bool
  | .axiom left right =>
      left != right &&
      certificate.inBounds left && certificate.inBounds right &&
      match certificate.formula? left, certificate.formula? right with
      | some leftFormula, some rightFormula =>
          leftFormula.isAtom && rightFormula == leftFormula.dual
      | _, _ => false
  | .tensor left right conclusion =>
      left != right && left != conclusion && right != conclusion &&
      certificate.inBounds left && certificate.inBounds right &&
      certificate.inBounds conclusion &&
      match certificate.formula? left, certificate.formula? right,
          certificate.formula? conclusion with
      | some leftFormula, some rightFormula, some conclusionFormula =>
          conclusionFormula == .tensor leftFormula rightFormula
      | _, _, _ => false
  | .par left right conclusion =>
      left != right && left != conclusion && right != conclusion &&
      certificate.inBounds left && certificate.inBounds right &&
      certificate.inBounds conclusion &&
      match certificate.formula? left, certificate.formula? right,
          certificate.formula? conclusion with
      | some leftFormula, some rightFormula, some conclusionFormula =>
          conclusionFormula == .par leftFormula rightFormula
      | _, _, _ => false

def axiomCount (certificate : Certificate) (vertex : Vertex) : Nat :=
  (certificate.links.filter (·.containsAxiomEndpoint vertex)).length

def producerCount (certificate : Certificate) (vertex : Vertex) : Nat :=
  (certificate.links.filter (·.produces vertex)).length

def parentUseCount (certificate : Certificate) (vertex : Vertex) : Nat :=
  (certificate.links.filter (·.usesAsPremise vertex)).length

def nodeWellFormed (certificate : Certificate) (vertex : Vertex) : Bool :=
  let sourceOK :=
    match certificate.formula? vertex with
    | some (.atom _ _) => certificate.axiomCount vertex == 1
    | some (.tensor _ _) => certificate.producerCount vertex == 1
    | some (.par _ _) => certificate.producerCount vertex == 1
    | none => false
  let boundaryOK :=
    if certificate.conclusions.contains vertex then
      certificate.parentUseCount vertex == 0
    else
      certificate.parentUseCount vertex == 1
  sourceOK && boundaryOK

/-- Executable structural validation before the switching criterion is run. -/
def wellFormed (certificate : Certificate) : Bool :=
  certificate.formulas.size > 0 &&
  certificate.conclusions.length > 0 &&
  certificate.conclusions.all certificate.inBounds &&
  certificate.conclusions.eraseDups.length == certificate.conclusions.length &&
  certificate.links.all certificate.linkLocallyWellFormed &&
  (List.range certificate.formulas.size).all certificate.nodeWellFormed

end Certificate
end ProofNetIR
