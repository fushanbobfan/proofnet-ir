import ProofNetIR

open ProofNetIR

namespace ProofNetIRTests

def p : Formula := .atom "p" true
def pDual : Formula := p.dual
def q : Formula := .atom "q" true
def qDual : Formula := q.dual

example : p.dual.dual = p := by simp

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
example : canonical.switchingGraphs.length = 2 := by native_decide
example : canonical.check = true := by native_decide
example : canonical.Correct := canonical.check_sound (by native_decide)

example : canonical = canonicalCertificate "p" "q" := by native_decide

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

def treeGraph : Graph where
  vertexCount := 4
  edges := [
    { first := 0, second := 1 },
    { first := 1, second := 2 },
    { first := 1, second := 3 }
  ]

example : treeGraph.isTree = true := by native_decide
example : treeGraph.IsTree := treeGraph.isTree_sound (by native_decide)
example : treeGraph.Walk 0 3 :=
  (treeGraph.isTree_sound (by native_decide)).2.1.2 3 (by decide)

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

def unboundedGraph : Graph where
  vertexCount := 2
  edges := [{ first := 0, second := 2 }]

example : unboundedGraph.boundedEdges = false := by native_decide
example : unboundedGraph.isTree = false := by native_decide

def run : IO Unit := do
  if canonical.check then
    IO.println "ProofNetIR: all compile-time certificate checks passed"
  else
    throw <| IO.userError "canonical proof net was unexpectedly rejected"

end ProofNetIRTests

def main : IO Unit := ProofNetIRTests.run
