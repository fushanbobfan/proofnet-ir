import Lean.Data.Json
import ProofNetIR.Checker

namespace ProofNetIR

namespace Link

/-- Canonicalize the symmetric endpoints of an axiom link. Tensor and par
premise order remains significant in the formula syntax. -/
def canonicalize : Link → Link
  | .axiom left right =>
      if left ≤ right then .axiom left right else .axiom right left
  | link => link

def sortKey : Link → List Nat
  | .axiom left right => [0, left, right]
  | .tensor left right conclusion => [1, conclusion, left, right]
  | .par left right conclusion => [2, conclusion, left, right]

end Link

namespace Certificate

def natListLess : List Nat → List Nat → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | left :: leftRest, right :: rightRest =>
      if left < right then true
      else if right < left then false
      else natListLess leftRest rightRest

def insertLink (link : Link) : List Link → List Link
  | [] => [link]
  | head :: tail =>
      if natListLess link.sortKey head.sortKey then
        link :: head :: tail
      else
        head :: insertLink link tail

def sortLinks (links : List Link) : List Link :=
  links.foldr insertLink []

def insertNat (value : Nat) : List Nat → List Nat
  | [] => [value]
  | head :: tail =>
      if value < head then value :: head :: tail
      else head :: insertNat value tail

def sortNats (values : List Nat) : List Nat :=
  values.foldr insertNat []

/-- Canonical v0.2 normalization. Vertex numbers remain the formula-array
indices by contract; link order, conclusion order, and axiom orientation are
normalized. This is intentionally not graph-isomorphism canonicalization. -/
def canonicalize (certificate : Certificate) : Certificate :=
  { formulas := certificate.formulas
    links := certificate.links.map Link.canonicalize |> sortLinks
    conclusions := certificate.conclusions |> sortNats }

def formulaJson : Formula → Lean.Json
  | .atom name positive => Lean.Json.mkObj [
      ("kind", "atom"), ("name", name), ("positive", positive)]
  | .tensor left right => Lean.Json.mkObj [
      ("kind", "tensor"), ("left", formulaJson left),
      ("right", formulaJson right)]
  | .par left right => Lean.Json.mkObj [
      ("kind", "par"), ("left", formulaJson left),
      ("right", formulaJson right)]

def linkJson : Link → Lean.Json
  | .axiom left right => Lean.Json.mkObj [
      ("kind", "axiom"), ("left", left), ("right", right)]
  | .tensor left right conclusion => Lean.Json.mkObj [
      ("kind", "tensor"), ("left", left), ("right", right),
      ("conclusion", conclusion)]
  | .par left right conclusion => Lean.Json.mkObj [
      ("kind", "par"), ("left", left), ("right", right),
      ("conclusion", conclusion)]

/-- Versioned deterministic JSON value for a canonically normalized
certificate. -/
def canonicalJson (certificate : Certificate) : Lean.Json :=
  let normalized := certificate.canonicalize
  Lean.Json.mkObj [
    ("version", "0.2"),
    ("canonical", true),
    ("formulas", .arr (normalized.formulas.map formulaJson)),
    ("links", .arr (normalized.links.toArray.map linkJson)),
    ("conclusions", .arr (normalized.conclusions.toArray.map
      (fun value : Vertex => .num (Lean.JsonNumber.fromNat value))))]

def canonicalString (certificate : Certificate) : String :=
  certificate.canonicalJson.compress

end Certificate

end ProofNetIR
