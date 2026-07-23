import ProofNetIR.LeanPropSchema

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

end ProofNetIR.LeanProp.Schema.Corpus
