import ProofNetIR.LeanPropSchema
import ProofNetIR.LeanPropRaw

namespace ProofNetIR.LeanProp.Schema.Corpus

open Formula

def duplicate (name : String) : PackedDerivation :=
  let proposition := Formula.atom name
  {
    name := s!"duplicate/{name}"
    persistent := []
    linear := []
    goal := .imp proposition (.and proposition proposition)
    derivation := .impIntro (.persistentContract (.andIntro
      (.persistentAxiom (formula := proposition))
      (.persistentAxiom (formula := proposition))))
  }

def discard (leftName rightName : String) : PackedDerivation :=
  let left := Formula.atom leftName
  let right := Formula.atom rightName
  {
    name := s!"discard/{leftName}/{rightName}"
    persistent := []
    linear := []
    goal := .imp left (.imp right left)
    derivation := .impIntro (.impIntro (.persistentWeaken
      (.persistentAxiom (formula := left))))
  }

def linearPair (leftName rightName : String) : PackedDerivation :=
  let left := Formula.atom leftName
  let right := Formula.atom rightName
  {
    name := s!"linear-pair/{leftName}/{rightName}"
    persistent := []
    linear := [left, right]
    goal := .and left right
    derivation := .andIntro (.linearAxiom (formula := left))
      (.linearAxiom (formula := right))
  }

def swappedLinearPair (leftName rightName : String) : PackedDerivation :=
  let left := Formula.atom leftName
  let right := Formula.atom rightName
  {
    name := s!"swapped-linear-pair/{leftName}/{rightName}"
    persistent := []
    linear := [left, right]
    goal := .and right left
    derivation := .linearExchange (.swap left right [])
      (.andIntro (.linearAxiom (formula := right))
        (.linearAxiom (formula := left)))
  }

def linearModusPonens (antecedentName consequentName : String) :
    PackedDerivation :=
  let antecedent := Formula.atom antecedentName
  let consequent := Formula.atom consequentName
  {
    name := s!"linear-mp/{antecedentName}/{consequentName}"
    persistent := []
    linear := [.imp antecedent consequent, antecedent]
    goal := consequent
    derivation := .impElim
      (.linearAxiom (formula := .imp antecedent consequent))
      (.linearAxiom (formula := antecedent))
  }

def projectLeft (leftName rightName : String) : PackedDerivation :=
  let left := Formula.atom leftName
  let right := Formula.atom rightName
  {
    name := s!"project-left/{leftName}/{rightName}"
    persistent := []
    linear := []
    goal := .imp (.and left right) left
    derivation := .impIntro (.andElimLeft
      (.persistentAxiom (formula := .and left right)))
  }

/-- Six rule strata per index, with disjoint atom names across indices. -/
def generated (count : Nat) : List PackedDerivation :=
  (List.range count).flatMap fun index =>
    let left := s!"p{index}"
    let right := s!"q{index}"
    [duplicate left, discard left right, linearPair left right,
      swappedLinearPair left right, linearModusPonens left right,
      projectLeft left right]

example : (generated 100).length = 600 := by native_decide

def rawPositive (count : Nat) : List (String × Raw.Derivation) :=
  (generated count).map fun packed =>
    (packed.name, Raw.Derivation.ofIndexed packed.derivation)

/-- A malformed raw template paired with its exact expected diagnostic. -/
structure RawNegativeCase where
  name : String
  derivation : Raw.Derivation
  expectedCode : Raw.ErrorCode
  expectedPath : List Nat := []

/-- Ten malformed strata per index. Together they exercise every stable error
code and a nested path-propagation case. -/
def rawNegative (count : Nat) : List RawNegativeCase :=
  (List.range count).flatMap fun index =>
    let p := Formula.atom s!"p{index}"
    let q := Formula.atom s!"q{index}"
    let r := Formula.atom s!"r{index}"
    [
      {
        name := s!"invalid-permutation/{index}"
        derivation := .persistentExchange
          (.trans (.swap p q []) (.swap p r [])) (.persistentAxiom p)
        expectedCode := .invalidPermutation
      },
      {
        name := s!"exchange-source-mismatch/{index}"
        derivation := .persistentExchange (.swap p q [])
          (.persistentAxiom p)
        expectedCode := .exchangeSourceMismatch
      },
      {
        name := s!"contraction-too-short/{index}"
        derivation := .persistentContract p (.persistentAxiom p)
        expectedCode := .contractionContextTooShort
      },
      {
        name := s!"contraction-formula-mismatch/{index}"
        derivation := .persistentContract q
          (.andIntro (.persistentAxiom p) (.persistentAxiom p))
        expectedCode := .contractionFormulaMismatch
      },
      {
        name := s!"expected-conjunction/{index}"
        derivation := .andElimLeft (.persistentAxiom p)
        expectedCode := .expectedConjunction
      },
      {
        name := s!"implication-context-missing/{index}"
        derivation := .impIntro p (.linearAxiom q)
        expectedCode := .implicationContextMissing
      },
      {
        name := s!"implication-context-mismatch/{index}"
        derivation := .impIntro q (.persistentAxiom p)
        expectedCode := .implicationContextMismatch
      },
      {
        name := s!"expected-implication/{index}"
        derivation := .impElim (.linearAxiom p) (.linearAxiom q)
        expectedCode := .expectedImplication
      },
      {
        name := s!"implication-argument-mismatch/{index}"
        derivation := .impElim
          (.linearAxiom (.imp p q)) (.linearAxiom r)
        expectedCode := .implicationArgumentMismatch
      },
      {
        name := s!"nested-path/{index}"
        derivation := .persistentWeaken r
          (.andElimLeft (.persistentAxiom p))
        expectedCode := .expectedConjunction
        expectedPath := [0]
      }
    ]

example : (rawPositive 100).length = 600 := by native_decide
example : (rawNegative 100).length = 1000 := by native_decide

end ProofNetIR.LeanProp.Schema.Corpus
