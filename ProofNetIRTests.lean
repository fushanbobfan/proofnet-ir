import ProofNetIR

open ProofNetIR

namespace ProofNetIRTests

def p : Formula := .atom "p" true
def pDual : Formula := p.dual
def q : Formula := .atom "q" true
def qDual : Formula := q.dual

example : p.dual.dual = p := by simp

def mixedFormula : Formula := .par (.tensor p q) (.atom "r" true)

example : Derivation [mixedFormula, mixedFormula.dual] :=
  Derivation.identity mixedFormula

example : identityCertificate (.tensor p q) = canonicalCertificate "p" "q" := by
  native_decide

example : (identityCertificate mixedFormula).wellFormed = true := by
  native_decide

example : (identityCertificate mixedFormula).switchingGraphs.length = 4 := by
  native_decide

example : (identityCertificate mixedFormula).check = true := by
  native_decide

example : (identityCertificate mixedFormula).FuelCorrect :=
  (identityCertificate mixedFormula).check_iff_fuelCorrect.mp (by native_decide)

example :
    (reconstructIdentity? (identityCertificate mixedFormula) mixedFormula).isSome =
      true := by
  native_decide

example :
    (reconstructIdentity?
      (Mutation.dropFirstLink.apply (identityCertificate mixedFormula))
      mixedFormula).isSome = false := by
  native_decide

def generatedDepthTwo : List Formula := Formula.enumerate ["p"] 2

example : generatedDepthTwo.length = 210 := by native_decide
example : generatedDepthTwo.all (fun formula =>
    (identityCertificate formula).check) = true := by
  native_decide

def generatedDerivationTrees : List CutFreeDerivation :=
  (List.range 250).map fun seed => CutFreeDerivation.generate seed 2

example : generatedDerivationTrees.all (fun tree => tree.infer?.isSome) = true := by
  native_decide

example : generatedDerivationTrees.all (fun tree =>
    tree.desequentializeChecked?.isSome) = true := by
  native_decide

example : generatedDerivationTrees.all (fun tree => tree.elaborate?.isSome) = true := by
  native_decide

def generatedJsonRoundTrips : Bool :=
  generatedDerivationTrees.all fun tree =>
    match tree.desequentialize? with
    | none => false
    | some certificate =>
        match Certificate.checkedFromString certificate.canonicalString with
        | .error _ => false
        | .ok checked => checked.certificate == certificate.canonicalize

example : generatedJsonRoundTrips = true := by native_decide

example : generatedDerivationTrees.all (fun tree =>
    match tree.desequentialize? with
    | some certificate => certificate.check
    | none => false) = true := by
  native_decide

/-- The canonical net for `⊢ p ⊗ q, p⊥ ⅋ q⊥`. -/
def canonical : Certificate where
  formulas := #[p, pDual, q, qDual, .tensor p q, .par pDual qDual]
  links := [
    .axiom 0 1,
    .axiom 2 3,
    .tensor 0 2 4,
    .par 1 3 5
  ]
  conclusions := [4, 5]

example : canonical.wellFormed = true := by native_decide
example : canonical.StructurallyWellFormed :=
  canonical.wellFormed_iff_structurallyWellFormed.mp (by native_decide)
example : canonical.switchingGraphs.length = 2 := by native_decide
example : canonical.check = true := by native_decide
example : canonical.Correct := canonical.check_sound (by native_decide)
example : canonical.check = true ↔ canonical.Correct :=
  canonical.check_iff_correct
example : canonical.DeclarativelyCorrect :=
  canonical.check_sound_declarative (by native_decide)
example : canonical.check = true ↔ canonical.DeclarativelyCorrect :=
  canonical.check_iff_declarativelyCorrect
example : canonical.FuelCorrect :=
  canonical.check_iff_fuelCorrect.mp (by native_decide)
example : canonical.Correct ↔ canonical.FuelCorrect :=
  canonical.correct_iff_fuelCorrect
example : canonical.FuelDeclarativelyCorrect :=
  canonical.check_iff_fuelDeclarativelyCorrect.mp (by native_decide)
example : canonical.DeclarativelyCorrect ↔
    canonical.FuelDeclarativelyCorrect :=
  canonical.declarativelyCorrect_iff_fuelDeclarativelyCorrect

example : canonical = canonicalCertificate "p" "q" := by native_decide

def scrambledCanonical : Certificate :=
  { canonical with
    links := canonical.links.reverse
    conclusions := canonical.conclusions.reverse }

example : scrambledCanonical.canonicalize.check = true := by native_decide
example : scrambledCanonical.canonicalString = canonical.canonicalString := by
  native_decide

def parsedCanonicalMatches : Bool :=
  match Certificate.fromString canonical.canonicalString with
  | .ok certificate => certificate == canonical
  | .error _ => false

example : parsedCanonicalMatches = true := by native_decide

example :
    (Certificate.checkedFromString canonical.canonicalString).isOk = true := by
  native_decide

def rejectedCanonicalJson : Lean.Json :=
  Mutation.dropFirstLink.apply canonical |>.canonicalJson

def rejectedCertificateStillParses : Bool :=
  match Certificate.fromJson rejectedCanonicalJson with
  | .ok certificate =>
      certificate == (Mutation.dropFirstLink.apply canonical |>.canonicalize)
  | .error _ => false

example : rejectedCertificateStillParses = true := by native_decide

example : (Certificate.checkedFromJson rejectedCanonicalJson).isOk = false := by
  native_decide

def missingAtomName : Lean.Json := Lean.Json.mkObj [
  ("kind", "atom"), ("positive", true)]

def missingAtomNameDiagnosticMatches : Bool :=
  match Certificate.formulaFromJson missingAtomName with
  | .error error =>
      error == { path := "$.name", message := "property not found: name" }
  | .ok _ => false

example : missingAtomNameDiagnosticMatches = true := by native_decide

def nonCanonicalJson : Lean.Json :=
  Lean.Json.mkObj [
    ("version", "0.2"),
    ("canonical", true),
    ("formulas", .arr (canonical.formulas.map Certificate.formulaJson)),
    ("links", .arr
      (scrambledCanonical.links.toArray.map Certificate.linkJson)),
    ("conclusions", .arr (scrambledCanonical.conclusions.toArray.map
      (fun value : Vertex => .num (Lean.JsonNumber.fromNat value))))]

example : (Certificate.fromJson nonCanonicalJson).isOk = false := by
  native_decide

def malformedExchange : CutFreeDerivation :=
  .exchange [0, 0] (.axiom "p" true)

example : malformedExchange.desequentialize?.isNone = true := by native_decide

example : (reconstructCanonical? canonical "p" "q").isSome = true := by
  native_decide

example :
    Derivation [
      .tensor (.atom "p" true) (.atom "q" true),
      .par (.atom "p" false) (.atom "q" false)
    ] := reconstructCanonical "p" "q"

def wrongAxiom : Certificate :=
  { canonical with links := [
      .axiom 0 3,
      .axiom 2 1,
      .tensor 0 2 4,
      .par 1 3 5
    ] }

example : wrongAxiom.wellFormed = false := by native_decide
example : wrongAxiom.check = false := by native_decide
example : ¬wrongAxiom.FuelCorrect := by
  intro semantic
  have accepted := wrongAxiom.check_iff_fuelCorrect.mpr semantic
  exact (by native_decide : wrongAxiom.check ≠ true) accepted
example : ¬wrongAxiom.FuelDeclarativelyCorrect := by
  intro semantic
  have accepted := wrongAxiom.check_iff_fuelDeclarativelyCorrect.mpr semantic
  exact (by native_decide : wrongAxiom.check ≠ true) accepted
example : (reconstructCanonical? wrongAxiom "p" "q").isSome = false := by
  native_decide

def canonicalThree : Certificate := canonicalThreeCertificate "p" "q" "r"

example : canonicalThree.wellFormed = true := by native_decide
example : canonicalThree.switchingGraphs.length = 4 := by native_decide
example : canonicalThree.check = true := by native_decide
example : canonicalThree.Correct :=
  canonicalThree.check_sound (by native_decide)

example :
    Derivation [
      .tensor
        (.tensor (.atom "p" true) (.atom "q" true))
        (.atom "r" true),
      .par
        (.atom "p" false)
        (.par (.atom "q" false) (.atom "r" false))
    ] := Derivation.canonicalThree "p" "q" "r"

def droppedLink : Certificate := Mutation.dropFirstLink.apply canonical
def duplicatedLink : Certificate := Mutation.duplicateFirstLink.apply canonical
def rewiredAxiom : Certificate :=
  (Mutation.replaceFirstAxiomRight 3).apply canonical

example : droppedLink.check = false := by native_decide
example : duplicatedLink.check = false := by native_decide
example : rewiredAxiom.check = false := by native_decide

def disconnected : Certificate where
  formulas := #[p, pDual, q, qDual]
  links := [.axiom 0 1, .axiom 2 3]
  conclusions := [0, 1, 2, 3]

example : disconnected.wellFormed = true := by native_decide
example : disconnected.check = false := by native_decide

def axiomOnly : Certificate where
  formulas := #[p, pDual]
  links := [.axiom 0 1]
  conclusions := [0, 1]

example : axiomOnly.wellFormed = true := by native_decide
example : axiomOnly.check = true := by native_decide

def duplicateConclusion : Certificate :=
  { axiomOnly with conclusions := [0, 0, 1] }

example : duplicateConclusion.wellFormed = false := by native_decide
example : duplicateConclusion.check = false := by native_decide

def outOfBounds : Certificate :=
  { axiomOnly with links := [.axiom 0 8] }

example : outOfBounds.wellFormed = false := by native_decide

def duplicateAxiom : Certificate :=
  { axiomOnly with links := [.axiom 0 1, .axiom 0 1] }

example : duplicateAxiom.wellFormed = false := by native_decide

def wrongTensorLabel : Certificate :=
  { canonical with formulas := #[p, pDual, q, qDual, .par p q, .par pDual qDual] }

example : wrongTensorLabel.wellFormed = false := by native_decide

def missingConclusion : Certificate :=
  { axiomOnly with conclusions := [] }

example : missingConclusion.wellFormed = false := by native_decide

def cyclicGraph : Graph where
  vertexCount := 3
  edges := [
    { first := 0, second := 1 },
    { first := 1, second := 2 },
    { first := 2, second := 0 }
  ]

example : cyclicGraph.connected = true := by native_decide
example : cyclicGraph.isTree = false := by native_decide
example : ¬cyclicGraph.FuelTree := by
  intro semantic
  have accepted := cyclicGraph.isTree_iff_fuelTree.mpr semantic
  exact (by native_decide : cyclicGraph.isTree ≠ true) accepted

def treeGraph : Graph where
  vertexCount := 4
  edges := [
    { first := 0, second := 1 },
    { first := 1, second := 2 },
    { first := 1, second := 3 }
  ]

example : treeGraph.isTree = true := by native_decide
example : treeGraph.IsTree := treeGraph.isTree_sound (by native_decide)
example : treeGraph.isTree = true ↔ treeGraph.IsTree :=
  treeGraph.isTree_iff_isTree
example : treeGraph.FuelTree :=
  treeGraph.isTree_iff_fuelTree.mp (by native_decide)
example : treeGraph.Walk 0 3 :=
  (treeGraph.isTree_sound (by native_decide)).2.1.2 3 (by decide)

theorem treeEdge01 : treeGraph.Adjacent 0 1 :=
  ⟨{ first := 0, second := 1 }, by simp [treeGraph], .inl ⟨rfl, rfl⟩⟩

theorem treeEdge13 : treeGraph.Adjacent 1 3 :=
  ⟨{ first := 1, second := 3 }, by simp [treeGraph], .inl ⟨rfl, rfl⟩⟩

theorem treeWalk03 : treeGraph.Walk 0 3 :=
  .step (.step (.refl 0) treeEdge01) treeEdge13

theorem treeWalkN03 : treeGraph.WalkN 0 2 3 :=
  .step (.step .refl treeEdge01) treeEdge13

example : ∃ steps visited, treeGraph.SimpleWalk 0 steps visited 3 :=
  treeWalk03.toSimple

example : treeGraph.FuelConnected :=
  (treeGraph.isTree_sound (by native_decide)).2.1.toFuelConnected
    (treeGraph.isTree_sound (by native_decide)).1

example : 3 ∈ treeGraph.closureN 2 [0] := by native_decide
example : 3 ∈ treeGraph.closureN 2 [0] :=
  treeGraph.walkN_mem_closureN
    (treeGraph.isTree_sound (by native_decide)).1 treeWalkN03
example :
    3 ∈ treeGraph.closureN 2 [0] ↔ treeGraph.WalkWithin 0 2 3 :=
  treeGraph.mem_closureN_iff_walkWithin
    (treeGraph.isTree_sound (by native_decide)).1 0 3 2 (by decide)
example : ∃ fuel, 3 ∈ treeGraph.closureN fuel [0] := by
  exact treeGraph.walk_mem_some_closureN
    (treeGraph.isTree_sound (by native_decide)).1
    treeWalk03

def singletonGraph : Graph where
  vertexCount := 1
  edges := []

example : singletonGraph.isTree = true := by native_decide

def emptyGraph : Graph where
  vertexCount := 0
  edges := []

example : emptyGraph.isTree = false := by native_decide

def selfLoopGraph : Graph where
  vertexCount := 1
  edges := [{ first := 0, second := 0 }]

example : selfLoopGraph.boundedEdges = false := by native_decide
example : selfLoopGraph.isTree = false := by native_decide

def parallelEdgeGraph : Graph where
  vertexCount := 2
  edges := [
    { first := 0, second := 1 },
    { first := 0, second := 1 }
  ]

example : parallelEdgeGraph.connected = true := by native_decide
example : parallelEdgeGraph.isTree = false := by native_decide

def unboundedGraph : Graph where
  vertexCount := 2
  edges := [{ first := 0, second := 2 }]

example : unboundedGraph.boundedEdges = false := by native_decide
example : unboundedGraph.isTree = false := by native_decide

/-- The unbounded walk semantics can cross an out-of-bounds bridge that the
finite checker intentionally filters. This witnesses why the `Bounded`
hypothesis of `connected_iff_connected` is necessary. -/
def unboundedBridgeGraph : Graph where
  vertexCount := 2
  edges := [
    { first := 0, second := 2 },
    { first := 2, second := 1 }
  ]

theorem unboundedBridgeEdge02 : unboundedBridgeGraph.Adjacent 0 2 :=
  ⟨{ first := 0, second := 2 }, by simp [unboundedBridgeGraph],
    .inl ⟨rfl, rfl⟩⟩

theorem unboundedBridgeEdge21 : unboundedBridgeGraph.Adjacent 2 1 :=
  ⟨{ first := 2, second := 1 }, by simp [unboundedBridgeGraph],
    .inl ⟨rfl, rfl⟩⟩

example : unboundedBridgeGraph.Connected := by
  refine ⟨by decide, ?_⟩
  intro vertex inBounds
  simp [unboundedBridgeGraph] at inBounds
  have cases : vertex = 0 ∨ vertex = 1 := by omega
  rcases cases with rfl | rfl
  · exact .refl 0
  · exact .step (.step (.refl 0) unboundedBridgeEdge02)
      unboundedBridgeEdge21

example : unboundedBridgeGraph.Bounded → False := by
  intro bounded
  have edgeBounds := bounded { first := 0, second := 2 }
    (by simp [unboundedBridgeGraph])
  have impossible : 2 < 2 := by
    simpa [unboundedBridgeGraph] using edgeBounds.2.1
  omega

example : unboundedBridgeGraph.connected = false := by native_decide

def run : IO Unit := do
  if canonical.check then
    IO.println "ProofNetIR: all compile-time certificate checks passed"
  else
    throw <| IO.userError "canonical proof net was unexpectedly rejected"

end ProofNetIRTests

def main : IO Unit := ProofNetIRTests.run
