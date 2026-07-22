import ProofNetIR.Sequentialization

namespace ProofNetIR

/-- Structured failure returned by the executable proof-net sequentializer.
The stage is stable enough for callers to classify failures; the message is
intended for humans. -/
structure SequentializationError where
  stage : String
  message : String
  formulaCount : Nat
  linkCount : Nat
  deriving Repr, DecidableEq, BEq

namespace SequentializationError

def render (error : SequentializationError) : String :=
  s!"{error.stage}: {error.message} " ++
    s!"(formulas={error.formulaCount}, links={error.linkCount})"

end SequentializationError

/-- Runtime result for an accepted certificate.  Unlike the proposition-level
`SequentializationResult`, this value is produced by an executable search and
can be inspected by downstream programs.  It already carries the exact input
boundary, independent inference, desequentialization, output-check, and exact
order-preserving reindex-equivalence facts. -/
structure ExecutableSequentializationResult (input : Certificate) where
  tree : CutFreeDerivation
  sequent : List Formula
  output : Certificate
  inferred : tree.infer? = some sequent
  inputLabels : input.conclusionFormulas? = some sequent
  desequentialized : tree.desequentialize? = some output
  outputAccepted : output.check = true
  equivalent : output.ProofNetEquivalent input

namespace ExecutableSequentializationResult

/-- Every successful executable result contains a kernel-typed derivation of
the exact ordered input boundary. -/
theorem kernelDerivation {input : Certificate}
    (result : ExecutableSequentializationResult input) :
    Nonempty (Derivation result.sequent) :=
  result.tree.infer?_sound result.inferred

theorem proofNetEquivalent {input : Certificate}
    (result : ExecutableSequentializationResult input) :
    result.output.ProofNetEquivalent input :=
  result.equivalent

end ExecutableSequentializationResult

namespace Certificate

private def sequentializationError (certificate : Certificate)
    (stage message : String) : SequentializationError := {
  stage
  message
  formulaCount := certificate.formulas.size
  linkCount := certificate.links.length }

private def firstSome (function : α → Option β) : List α → Option β
  | [] => none
  | head :: tail =>
      match function head with
      | some value => some value
      | none => firstSome function tail

/-- Enumerate every explicit occurrence permutation from `source` to `target`.
The search branches only between still-unused occurrences carrying the required
formula, rather than over all factorial permutations.  This is essential for
completeness when a boundary contains repeated formula labels. -/
def matchingFormulaOrders (source target : List Formula) : List (List Nat) :=
  if source.length != target.length then
    []
  else
    let rec visit (used : List Nat) : List Formula → List (List Nat)
      | [] => [[]]
      | formula :: rest =>
          (List.range source.length).filter (fun index =>
            !used.contains index && source[index]? == some formula) |>.flatMap
              fun index =>
                (visit (index :: used) rest).map fun suffix => index :: suffix
    visit [] target

/-- Deterministic first matching occurrence permutation.  The executable
sequentializer itself tries the complete list until reindex-equivalence holds. -/
def matchingFormulaOrder? (source target : List Formula) : Option (List Nat) :=
  (matchingFormulaOrders source target).head?

/-- A computational witness for the flattened proof-net equivalence relation. -/
structure DirectEquivalenceWitness (left right : Certificate) where
  vertexMap : VertexRenaming left.formulas.size
  linkPermutation :
    (left.reindex vertexMap).LinkPermutationEquivalent right

namespace DirectEquivalenceWitness

theorem proofNetEquivalent {left right : Certificate}
    (witness : DirectEquivalenceWitness left right) :
    left.ProofNetEquivalent right :=
  (show left.DirectProofNetEquivalent right from
    ⟨witness.vertexMap, witness.linkPermutation⟩).toProofNetEquivalent

end DirectEquivalenceWitness

private def renamingOfOrder? (bound : Nat) (order : List Vertex) :
    Option (VertexRenaming bound) :=
  if permutation : order.Perm (List.range bound) then
    let lengthEquation : order.length = bound := by
      simpa using permutation.length_eq
    let nodup : order.Nodup :=
      permutation.nodup_iff.mpr List.nodup_range
    let complete : ∀ vertex, vertex < bound ↔ vertex ∈ order := by
      intro vertex
      rw [permutation.mem_iff]
      simp
    some (VertexRenaming.ofOrder bound order lengthEquation nodup complete)
  else
    none

/-- Decide the exact v0.4 proof-net identity relation by enumerating only
formula-compatible vertex bijections, then checking link multiset equality and
the ordered conclusion boundary.  Unlike `reindexEquivalent?`, this decision
is intentionally insensitive to link-list storage order. -/
def directProofNetEquivalentWitness? (left right : Certificate) :
    Option (DirectEquivalenceWitness left right) :=
  firstSome (fun order => do
    let vertexMap ← renamingOfOrder? left.formulas.size order
    let reindexed := left.reindex vertexMap
    if formulas : reindexed.formulas = right.formulas then
      if links : reindexed.links.Perm right.links then
        if conclusions : reindexed.conclusions = right.conclusions then
          some {
            vertexMap
            linkPermutation := ⟨formulas, links, conclusions⟩ }
        else
          none
      else
        none
    else
      none) (matchingFormulaOrders left.formulas.toList right.formulas.toList)

private def alignTree? (input : Certificate) (tree : CutFreeDerivation)
    (target : List Formula) : Option CutFreeDerivation := do
  let source ← tree.infer?
  firstSome (fun order =>
    let aligned := CutFreeDerivation.exchange order tree
    if aligned.infer? != some target then
      none
    else
      match aligned.desequentializeChecked? with
      | some checked =>
          match directProofNetEquivalentWitness? checked.certificate input with
          | some _ => some aligned
          | none => none
      | none => none) (matchingFormulaOrders source target)

private def axiomTree? (certificate : Certificate)
    (target : List Formula) : Option CutFreeDerivation :=
  if certificate.links.any (fun link => link.isConnective) then
    none
  else
    firstSome (fun formula =>
      match formula with
      | .atom name positive =>
          alignTree? certificate (.axiom name positive) target
      | _ => none) certificate.formulas.toList

private def rebuildParTree? (input : Certificate)
    (premiseTree : CutFreeDerivation)
    (target : List Formula) : Option CutFreeDerivation := do
  let premiseSequent ← premiseTree.infer?
  if premiseSequent.length < 2 then
    none
  else
    let focus := premiseSequent.length - 2
    alignTree? input (.par focus focus premiseTree) target

private def rebuildTensorTree? (input : Certificate)
    (leftTree rightTree : CutFreeDerivation)
    (target : List Formula) : Option CutFreeDerivation := do
  let leftSequent ← leftTree.infer?
  let rightSequent ← rightTree.infer?
  if leftSequent.isEmpty || rightSequent.isEmpty then
    none
  else
    alignTree? input (.tensor (leftSequent.length - 1)
      (rightSequent.length - 1) leftTree rightTree) target

/-- Fuel-bounded executable inverse-rule search.  Every recursive premise is
independently checker-gated.  Fuel is exposed only for diagnostics and tests;
`sequentialize` supplies one more than the number of formula occurrences. -/
def executableTreeWithFuel : Nat → Certificate →
    Except SequentializationError CutFreeDerivation
  | 0, certificate =>
      .error (sequentializationError certificate "fuel"
        "inverse-rule search exhausted its occurrence bound")
  | fuel + 1, certificate =>
      if certificate.check != true then
        .error (sequentializationError certificate "input"
          "certificate was rejected by the proof-net checker")
      else
        match certificate.conclusionFormulas? with
        | none =>
            .error (sequentializationError certificate "boundary"
              "accepted certificate had unreadable conclusion labels")
        | some target =>
            match axiomTree? certificate target with
            | some tree => .ok tree
            | none =>
                let parTree := firstSome (fun candidate =>
                  let (left, right, conclusion) := candidate
                  match certificate.peelTerminalParChecked?
                      left right conclusion with
                  | none => none
                  | some premise =>
                      match executableTreeWithFuel fuel premise.certificate with
                      | .error _ => none
                      | .ok premiseTree =>
                          rebuildParTree? certificate premiseTree target)
                    certificate.terminalPars
                match parTree with
                | some tree => .ok tree
                | none =>
                    let tensorTree := firstSome (fun candidate =>
                      let (left, right, conclusion) := candidate
                      match certificate.splitTerminalTensorChecked?
                          left right conclusion with
                      | none => none
                      | some premises =>
                          match executableTreeWithFuel fuel
                              premises.leftPremise.certificate with
                          | .error _ => none
                          | .ok leftTree =>
                              match executableTreeWithFuel fuel
                                  premises.rightPremise.certificate with
                              | .error _ => none
                              | .ok rightTree =>
                                  rebuildTensorTree? certificate leftTree
                                    rightTree target)
                        certificate.terminalTensors
                    match tensorTree with
                    | some tree => .ok tree
                    | none =>
                        .error (sequentializationError certificate "search"
                          "no checker-preserving inverse rule reconstructed a derivation")

/-- Executable certificate-to-derivation API.  Successful results are
proof-bearing values, while failures retain a stable stage and certificate
size instead of collapsing to `none`. -/
def sequentialize (certificate : Certificate) :
    Except SequentializationError
      (ExecutableSequentializationResult certificate) := do
  if _inputAccepted : certificate.check = true then
    let tree ← certificate.executableTreeWithFuel
      (certificate.formulas.size + 1)
    match labels : certificate.conclusionFormulas? with
    | none =>
        throw (sequentializationError certificate "boundary"
          "could not read the input conclusion labels")
    | some sequent =>
        if inferred : tree.infer? = some sequent then
          match desequentialized : tree.desequentialize? with
          | none =>
              throw (sequentializationError certificate "output"
                "reconstructed tree did not desequentialize")
          | some output =>
              if outputAccepted : output.check = true then
                match directProofNetEquivalentWitness? output certificate with
                | some witness =>
                  have equivalent : output.ProofNetEquivalent certificate :=
                    witness.proofNetEquivalent
                  pure {
                    tree
                    sequent
                    output
                    inferred
                    inputLabels := labels
                    desequentialized
                    outputAccepted
                    equivalent }
                | none =>
                  throw (sequentializationError certificate "equivalence"
                    "reconstructed output was not proof-net-equivalent to the input")
              else
                throw (sequentializationError certificate "output"
                  "desequentialized tree was rejected by the proof-net checker")
        else
          throw (sequentializationError certificate "inference"
            "reconstructed tree did not infer the exact input boundary")
  else
    throw (sequentializationError certificate "input"
      "certificate was rejected by the proof-net checker")

end Certificate

end ProofNetIR
