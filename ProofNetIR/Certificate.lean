import ProofNetIR.Formula

namespace ProofNetIR

abbrev Vertex := Nat

/-- Local proof-net links. Formula occurrences are addressed by array index. -/
inductive Link where
  | axiom (left right : Vertex)
  | tensor (left right conclusion : Vertex)
  | par (left right conclusion : Vertex)
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

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

def isConnective : Link → Bool
  | .axiom _ _ => false
  | .tensor _ _ _ => true
  | .par _ _ _ => true

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

/-- Ordered formula labels on the public conclusion boundary. This belongs to
the certificate API rather than to any particular sequentializer. -/
def conclusionFormulas? (certificate : Certificate) :
    Option (List Formula) :=
  certificate.conclusions.mapM certificate.formula?

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

/-- Proposition-level meaning of local link well-formedness. This definition
does not call the executable Boolean checker. -/
def LinkWellFormed (certificate : Certificate) : Link → Prop
  | .axiom left right =>
      left ≠ right ∧
      left < certificate.formulas.size ∧
      right < certificate.formulas.size ∧
      match certificate.formula? left, certificate.formula? right with
      | some (.atom name positive), some rightFormula =>
          rightFormula = (Formula.atom name positive).dual
      | _, _ => False
  | .tensor left right conclusion =>
      left ≠ right ∧ left ≠ conclusion ∧ right ≠ conclusion ∧
      left < certificate.formulas.size ∧
      right < certificate.formulas.size ∧
      conclusion < certificate.formulas.size ∧
      match certificate.formula? left, certificate.formula? right,
          certificate.formula? conclusion with
      | some leftFormula, some rightFormula, some conclusionFormula =>
          conclusionFormula = .tensor leftFormula rightFormula
      | _, _, _ => False
  | .par left right conclusion =>
      left ≠ right ∧ left ≠ conclusion ∧ right ≠ conclusion ∧
      left < certificate.formulas.size ∧
      right < certificate.formulas.size ∧
      conclusion < certificate.formulas.size ∧
      match certificate.formula? left, certificate.formula? right,
          certificate.formula? conclusion with
      | some leftFormula, some rightFormula, some conclusionFormula =>
          conclusionFormula = .par leftFormula rightFormula
      | _, _, _ => False

theorem linkLocallyWellFormed_iff (certificate : Certificate) (link : Link) :
    certificate.linkLocallyWellFormed link = true ↔
      certificate.LinkWellFormed link := by
  cases link with
  | «axiom» left right =>
      cases leftFormula : certificate.formula? left with
      | none =>
          simp [linkLocallyWellFormed, LinkWellFormed, inBounds,
            leftFormula]
      | some leftValue =>
          cases rightFormula : certificate.formula? right with
          | none =>
              simp [linkLocallyWellFormed, LinkWellFormed, inBounds,
                leftFormula, rightFormula]
          | some rightValue =>
              cases leftValue <;>
                simp [linkLocallyWellFormed, LinkWellFormed, inBounds,
                  leftFormula, rightFormula, Formula.isAtom, and_assoc]
  | tensor left right conclusion =>
      cases leftFormula : certificate.formula? left <;>
      cases rightFormula : certificate.formula? right <;>
      cases conclusionFormula : certificate.formula? conclusion <;>
        simp [linkLocallyWellFormed, LinkWellFormed, inBounds,
          leftFormula, rightFormula, conclusionFormula, and_assoc]
  | par left right conclusion =>
      cases leftFormula : certificate.formula? left <;>
      cases rightFormula : certificate.formula? right <;>
      cases conclusionFormula : certificate.formula? conclusion <;>
        simp [linkLocallyWellFormed, LinkWellFormed, inBounds,
          leftFormula, rightFormula, conclusionFormula, and_assoc]

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

/-- Proposition-level node ownership and boundary discipline. -/
def NodeWellFormed (certificate : Certificate) (vertex : Vertex) : Prop :=
  (match certificate.formula? vertex with
    | some (.atom _ _) => certificate.axiomCount vertex = 1
    | some (.tensor _ _) => certificate.producerCount vertex = 1
    | some (.par _ _) => certificate.producerCount vertex = 1
    | none => False) ∧
  (if vertex ∈ certificate.conclusions then
      certificate.parentUseCount vertex = 0
    else
      certificate.parentUseCount vertex = 1)

theorem nodeWellFormed_iff (certificate : Certificate) (vertex : Vertex) :
    certificate.nodeWellFormed vertex = true ↔
      certificate.NodeWellFormed vertex := by
  cases formula : certificate.formula? vertex with
  | none => simp [nodeWellFormed, NodeWellFormed, formula]
  | some value =>
      cases value <;>
      by_cases boundary : vertex ∈ certificate.conclusions <;>
        simp [nodeWellFormed, NodeWellFormed, formula, boundary]

/-- Executable structural validation before the switching criterion is run. -/
def wellFormed (certificate : Certificate) : Bool :=
  certificate.formulas.size > 0 &&
  certificate.conclusions.length > 0 &&
  certificate.conclusions.all certificate.inBounds &&
  certificate.conclusions.eraseDups.length == certificate.conclusions.length &&
  certificate.links.all certificate.linkLocallyWellFormed &&
  (List.range certificate.formulas.size).all certificate.nodeWellFormed

/-- A Boolean-free structural specification for proof structures. The only
equalities here are mathematical cardinality/ownership conditions. -/
def StructurallyWellFormed (certificate : Certificate) : Prop :=
  0 < certificate.formulas.size ∧
  0 < certificate.conclusions.length ∧
  (∀ vertex ∈ certificate.conclusions,
    vertex < certificate.formulas.size) ∧
  certificate.conclusions.eraseDups.length = certificate.conclusions.length ∧
  (∀ link ∈ certificate.links, certificate.LinkWellFormed link) ∧
  ∀ vertex, vertex < certificate.formulas.size →
    certificate.NodeWellFormed vertex

theorem wellFormed_iff_structurallyWellFormed (certificate : Certificate) :
    certificate.wellFormed = true ↔ certificate.StructurallyWellFormed := by
  simp only [wellFormed, Bool.and_eq_true, decide_eq_true_eq]
  simp [StructurallyWellFormed, inBounds, linkLocallyWellFormed_iff,
    nodeWellFormed_iff, and_assoc]

end Certificate
end ProofNetIR
