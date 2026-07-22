import ProofNetIR.Certificate

namespace ProofNetIR

namespace Formula

/-- Enumerate a finite, intentionally redundant formula corpus of depth at
most `depth`. Keeping duplicates makes the construction transparent; dataset
canonicalization is a separate versioned step. -/
def enumerate (atomNames : List String) : Nat → List Formula
  | 0 => atomNames.flatMap fun name => [.atom name true, .atom name false]
  | depth + 1 =>
      let prior := enumerate atomNames depth
      prior ++ prior.flatMap fun left =>
        prior.flatMap fun right => [.tensor left right, .par left right]

end Formula

namespace Link

/-- Reindex every occurrence of a link by a fixed array offset. -/
def shift (offset : Nat) : Link → Link
  | .axiom left right => .axiom (left + offset) (right + offset)
  | .tensor left right conclusion =>
      .tensor (left + offset) (right + offset) (conclusion + offset)
  | .par left right conclusion =>
      .par (left + offset) (right + offset) (conclusion + offset)

end Link

/-- A generated identity-net fragment with roots for `formula` and its dual. -/
structure IdentityFragment where
  formulas : Array Formula
  links : List Link
  positiveRoot : Vertex
  negativeRoot : Vertex
  deriving Repr, DecidableEq, BEq

namespace IdentityFragment

/-- Derivation-first canonical proof-structure generation for `A, A-dual`.
The construction mirrors `Derivation.identity`: atomic leaves become axiom
links, while each connective and its De Morgan dual are added together. -/
def ofFormula : Formula → IdentityFragment
  | formula@(.atom _ _) =>
      { formulas := #[formula, formula.dual]
        links := [.axiom 0 1]
        positiveRoot := 0
        negativeRoot := 1 }
  | formula@(.tensor left right) =>
      let leftFragment := ofFormula left
      let rightFragment := ofFormula right
      let offset := leftFragment.formulas.size
      let combined := leftFragment.formulas ++ rightFragment.formulas
      let positiveRoot := combined.size
      let negativeRoot := positiveRoot + 1
      let links := leftFragment.links ++
        rightFragment.links.map (·.shift offset) ++ [
          .tensor leftFragment.positiveRoot
            (rightFragment.positiveRoot + offset) positiveRoot,
          .par leftFragment.negativeRoot
            (rightFragment.negativeRoot + offset) negativeRoot
        ]
      { formulas := (combined.push formula).push formula.dual
        links
        positiveRoot
        negativeRoot }
  | formula@(.par left right) =>
      let leftFragment := ofFormula left
      let rightFragment := ofFormula right
      let offset := leftFragment.formulas.size
      let combined := leftFragment.formulas ++ rightFragment.formulas
      let positiveRoot := combined.size
      let negativeRoot := positiveRoot + 1
      let links := leftFragment.links ++
        rightFragment.links.map (·.shift offset) ++ [
          .par leftFragment.positiveRoot
            (rightFragment.positiveRoot + offset) positiveRoot,
          .tensor leftFragment.negativeRoot
            (rightFragment.negativeRoot + offset) negativeRoot
        ]
      { formulas := (combined.push formula).push formula.dual
        links
        positiveRoot
        negativeRoot }

def toCertificate (fragment : IdentityFragment) : Certificate :=
  { formulas := fragment.formulas
    links := fragment.links
    conclusions := [fragment.positiveRoot, fragment.negativeRoot] }

end IdentityFragment

/-- Generate the canonical identity proof structure for any unit-free MLL
formula. The executable checker remains authoritative for every output. -/
def identityCertificate (formula : Formula) : Certificate :=
  (IdentityFragment.ofFormula formula).toCertificate

end ProofNetIR
