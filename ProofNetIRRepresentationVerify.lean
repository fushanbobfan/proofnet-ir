import ProofNetIR

open Lean ProofNetIR

namespace ProofNetIRRepresentationVerify

/-! Lean verification of model proposals in two representations.

Every input line is a JSON object with an `id`, a `sequent`, a `kind`
(`proof` or `net`), and a `proposal`. A `proof` proposal is a top-down
sequent-calculus proof tree over the sequent: `{"rule":"axiom"}` closes a
sequent of two dual atoms; `{"rule":"par","at":i,"premise":P}` replaces the
par at position `i` by its two subformulas in place; `{"rule":"tensor","at":i,
"left":[j,...],"leftPremise":P1,"rightPremise":P2}` sends the listed context
positions with the left subformula and the rest with the right one, each
premise keeping the original order with the subformula first. A `net` proposal
is `{"pairs":[[a,b],...]}` over the atom occurrences of the sequent numbered in
reading order. A proof is valid when it converts to a `CutFreeDerivation` whose
`infer?` is exactly the sequent; a net is valid when the certificate it
completes passes `Certificate.check`. Both answers come from the library, not
from this file. -/

instance : Inhabited Formula := ⟨.atom "" true⟩

private def jsonNat (json : Json) : Except String Nat := do
  match json.getNat? with
  | .ok value => pure value
  | .error message => throw message

/-- Position of `target` in `sequent`, first occurrence. -/
private def indexOf (sequent : List Formula) (target : Formula) : Option Nat :=
  sequent.findIdx? (· == target)

/-- Reorder a derivation so that `infer?` returns exactly `goal`, when the
inferred sequent is a permutation of it with the same multiset. -/
private def realign (tree : CutFreeDerivation) (goal : List Formula) : Option CutFreeDerivation := do
  let inferred ← tree.infer?
  if inferred == goal then
    return tree
  -- order[k] = position in `inferred` of goal[k], using each position once
  let mut used : List Nat := []
  let mut order : List Nat := []
  for formula in goal do
    let candidates := (List.range inferred.length).filter fun index =>
      inferred[index]! == formula && !used.contains index
    match candidates.head? with
    | none => none
    | some index =>
        used := used ++ [index]
        order := order ++ [index]
  let realigned := CutFreeDerivation.exchange order tree
  if realigned.infer? == some goal then some realigned else none

/-- Converts a top-down proof over `sequent` into a derivation inferring exactly
`sequent`; every rule application is checked against the library's inference. -/
partial def build (sequent : List Formula) (proof : Json) : Except String CutFreeDerivation := do
  let rule ← (proof.getObjVal? "rule") >>= Json.getStr?
  match rule with
  | "axiom" =>
      match sequent with
      | [.atom name positive, other] =>
          if other == (Formula.atom name positive).dual then
            let tree := CutFreeDerivation.axiom name positive
            match realign tree sequent with
            | some aligned => pure aligned
            | none => throw "axiom does not infer the sequent"
          else throw "axiom on non-dual atoms"
      | _ => throw "axiom on a sequent that is not two dual atoms"
  | "par" =>
      let position ← (proof.getObjVal? "at") >>= jsonNat
      match sequent[position]? with
      | some (.par left right) =>
          let premiseSequent := sequent.take position ++ [left, right] ++ sequent.drop (position + 1)
          let premise ← build premiseSequent (← proof.getObjVal? "premise")
          -- infer? of the premise is exactly premiseSequent; pick left then right
          let leftFocus := position
          let rightFocus := position
          let tree := CutFreeDerivation.par leftFocus rightFocus premise
          match realign tree sequent with
          | some aligned => pure aligned
          | none => throw "par does not infer the sequent"
      | _ => throw "par position does not hold a par"
  | "tensor" =>
      let position ← (proof.getObjVal? "at") >>= jsonNat
      let leftJson ← (proof.getObjVal? "left") >>= Json.getArr?
      let leftPositions ← leftJson.toList.mapM jsonNat
      match sequent[position]? with
      | some (.tensor left right) =>
          let context := (List.range sequent.length).filter (· != position)
          if leftPositions.any (fun p => !context.contains p) then
            throw "left context position out of range"
          if leftPositions.eraseDups.length != leftPositions.length then
            throw "duplicate left context position"
          let leftContext := context.filter leftPositions.contains
          let rightContext := context.filter fun p => !leftPositions.contains p
          let leftSequent := left :: leftContext.map fun p => sequent[p]!
          let rightSequent := right :: rightContext.map fun p => sequent[p]!
          let leftPremise ← build leftSequent (← proof.getObjVal? "leftPremise")
          let rightPremise ← build rightSequent (← proof.getObjVal? "rightPremise")
          let tree := CutFreeDerivation.tensor 0 0 leftPremise rightPremise
          match realign tree sequent with
          | some aligned => pure aligned
          | none => throw "tensor does not infer the sequent"
      | _ => throw "tensor position does not hold a tensor"
  | other => throw s!"unknown rule {other}"

private partial def addSkeleton (formulas : Array Formula) (links : List Link) : Formula →
    Array Formula × List Link × Vertex
  | .atom name positive => (formulas.push (.atom name positive), links, formulas.size)
  | .tensor left right =>
      let id := formulas.size
      let formulas := formulas.push (.tensor left right)
      let (formulas, links, leftId) := addSkeleton formulas links left
      let (formulas, links, rightId) := addSkeleton formulas links right
      (formulas, links ++ [Link.tensor leftId rightId id], id)
  | .par left right =>
      let id := formulas.size
      let formulas := formulas.push (.par left right)
      let (formulas, links, leftId) := addSkeleton formulas links left
      let (formulas, links, rightId) := addSkeleton formulas links right
      (formulas, links ++ [Link.par leftId rightId id], id)

/-- The net proposal completed into a certificate and decided by `check`. -/
def netValid (sequent : List Formula) (proposal : Json) : Except String Bool := do
  let pairsJson ← (proposal.getObjVal? "pairs") >>= Json.getArr?
  let mut formulas : Array Formula := #[]
  let mut links : List Link := []
  let mut conclusions : List Vertex := []
  for formula in sequent do
    let (next, nextLinks, id) := addSkeleton formulas links formula
    formulas := next
    links := nextLinks
    conclusions := conclusions ++ [id]
  let atoms := (List.range formulas.size).filter fun id => formulas[id]!.isAtom
  let mut axioms : List Link := []
  for pair in pairsJson.toList do
    let entries ← pair.getArr?
    match entries.toList with
    | [a, b] =>
        let a ← jsonNat a
        let b ← jsonNat b
        match atoms[a]?, atoms[b]? with
        | some va, some vb => axioms := axioms ++ [Link.axiom va vb]
        | _, _ => throw "atom occurrence out of range"
    | _ => throw "pair is not two occurrences"
  let certificate : Certificate := { formulas, links := links ++ axioms, conclusions }
  return certificate.check

def run : IO Unit := do
  let payload ← (← IO.getStdin).readToEnd
  for line in payload.splitOn "\n" do
    if line.trimAscii.isEmpty then continue
    let result : Except String (String × Bool × String) := do
      let json ← Json.parse line
      let id ← (json.getObjVal? "id") >>= Json.getStr?
      let kind ← (json.getObjVal? "kind") >>= Json.getStr?
      let sequentJson ← (json.getObjVal? "sequent") >>= Json.getArr?
      let sequent ← sequentJson.toList.mapM fun value =>
        match Certificate.formulaFromJson value with
        | .ok formula => pure formula
        | .error error => throw s!"{error.path}: {error.message}"
      let proposal ← json.getObjVal? "proposal"
      match kind with
      | "proof" =>
          match build sequent proposal with
          | .ok tree => pure (id, tree.infer? == some sequent, "")
          | .error reason => pure (id, false, reason)
      | "net" =>
          match netValid sequent proposal with
          | .ok valid => pure (id, valid, "")
          | .error reason => pure (id, false, reason)
      | other => throw s!"unknown kind {other}"
    match result with
    | .ok (id, valid, reason) =>
        IO.println (Json.mkObj [("id", id), ("valid", valid), ("reason", reason)]).compress
    | .error message => throw <| IO.userError s!"verification input failed: {message}"

end ProofNetIRRepresentationVerify

def main : IO Unit := ProofNetIRRepresentationVerify.run
