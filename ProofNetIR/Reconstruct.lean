import ProofNetIR.Checker

namespace ProofNetIR

/-- A small, kernel-checked one-sided sequent calculus for unit-free MLL.

The rules are deliberately syntax-directed. `parTail` is the supported
right-boundary par rule in v0.1; exchange and general sequentialization are
tracked as later proof obligations rather than hidden in an untrusted script.
-/
inductive Derivation : List Formula → Type where
  | axiom (name : String) (positive : Bool) :
      Derivation [.atom name positive, .atom name (!positive)]
  | tensor {left right : Formula} {leftContext rightContext : List Formula} :
      Derivation (left :: leftContext) →
      Derivation (right :: rightContext) →
      Derivation (.tensor left right :: (leftContext ++ rightContext))
  | parTail {left right : Formula} {context : List Formula} :
      Derivation (context ++ [left, right]) →
      Derivation (context ++ [.par left right])

namespace Derivation

/-- A supported sequential reconstruction of the canonical two-axiom MLL net. -/
def canonical (leftName rightName : String) :
    Derivation [
      .tensor (.atom leftName true) (.atom rightName true),
      .par (.atom leftName false) (.atom rightName false)
    ] := by
  let leftProof : Derivation [
      .atom leftName true, .atom leftName false] :=
    .axiom leftName true
  let rightProof : Derivation [
      .atom rightName true, .atom rightName false] :=
    .axiom rightName true
  let combined : Derivation [
      .tensor (.atom leftName true) (.atom rightName true),
      .atom leftName false,
      .atom rightName false] := by
    simpa using Derivation.tensor leftProof rightProof
  simpa using Derivation.parTail
    (context := [.tensor (.atom leftName true) (.atom rightName true)])
    combined

/-- A second supported family, with three axiom links and nested tensor/par
links. This exercises nontrivial composition without claiming a general
sequentialization algorithm. -/
def canonicalThree (firstName secondName thirdName : String) :
    Derivation [
      .tensor
        (.tensor (.atom firstName true) (.atom secondName true))
        (.atom thirdName true),
      .par
        (.atom firstName false)
        (.par (.atom secondName false) (.atom thirdName false))
    ] := by
  let firstTwo : Derivation [
      .tensor (.atom firstName true) (.atom secondName true),
      .atom firstName false,
      .atom secondName false] := by
    simpa using Derivation.tensor
      (Derivation.axiom firstName true)
      (Derivation.axiom secondName true)
  let withThird : Derivation [
      .tensor
        (.tensor (.atom firstName true) (.atom secondName true))
        (.atom thirdName true),
      .atom firstName false,
      .atom secondName false,
      .atom thirdName false] := by
    simpa using Derivation.tensor firstTwo (Derivation.axiom thirdName true)
  let innerPar : Derivation [
      .tensor
        (.tensor (.atom firstName true) (.atom secondName true))
        (.atom thirdName true),
      .atom firstName false,
      .par (.atom secondName false) (.atom thirdName false)] := by
    simpa using Derivation.parTail
      (context := [
        .tensor
          (.tensor (.atom firstName true) (.atom secondName true))
          (.atom thirdName true),
        .atom firstName false])
      withThird
  simpa using Derivation.parTail
    (context := [
      .tensor
        (.tensor (.atom firstName true) (.atom secondName true))
        (.atom thirdName true)])
    innerPar

end Derivation

/-- Construct the certificate corresponding to `Derivation.canonical`. -/
def canonicalCertificate (leftName rightName : String) : Certificate :=
  let left : Formula := .atom leftName true
  let right : Formula := .atom rightName true
  { formulas := #[
      left, left.dual, right, right.dual,
      .tensor left right, .par left.dual right.dual
    ]
    links := [
      .axiom 0 1,
      .axiom 2 3,
      .tensor 0 2 4,
      .par 1 3 5
    ]
    conclusions := [4, 5] }

/-- Construct the certificate corresponding to `Derivation.canonicalThree`. -/
def canonicalThreeCertificate
    (firstName secondName thirdName : String) : Certificate :=
  let first : Formula := .atom firstName true
  let second : Formula := .atom secondName true
  let third : Formula := .atom thirdName true
  let firstTwo : Formula := .tensor first second
  let allThree : Formula := .tensor firstTwo third
  let lastTwoDual : Formula := .par second.dual third.dual
  { formulas := #[
      first, first.dual,
      second, second.dual,
      third, third.dual,
      firstTwo, allThree, lastTwoDual,
      .par first.dual lastTwoDual
    ]
    links := [
      .axiom 0 1,
      .axiom 2 3,
      .axiom 4 5,
      .tensor 0 2 6,
      .tensor 6 4 7,
      .par 3 5 8,
      .par 1 8 9
    ]
    conclusions := [7, 9] }

/-- The first sequentializer entry point. It is intentionally explicit about
the fragment it supports instead of pretending to sequentialize every correct
net before that theorem has been formalized. -/
def reconstructCanonical (leftName rightName : String) :
    Derivation [
      .tensor (.atom leftName true) (.atom rightName true),
      .par (.atom leftName false) (.atom rightName false)
    ] :=
  Derivation.canonical leftName rightName

/-- A certificate-gated entry point for the currently supported two-axiom
family. Returning a derivation is possible only after exact certificate
matching; arbitrary input is never silently ignored. -/
def reconstructCanonical? (certificate : Certificate)
    (leftName rightName : String) : Option (Derivation [
      .tensor (.atom leftName true) (.atom rightName true),
      .par (.atom leftName false) (.atom rightName false)
    ]) :=
  if certificate = canonicalCertificate leftName rightName then
    some (Derivation.canonical leftName rightName)
  else
    none

theorem reconstructCanonical?_isSome_iff (certificate : Certificate)
    (leftName rightName : String) :
    (reconstructCanonical? certificate leftName rightName).isSome = true ↔
      certificate = canonicalCertificate leftName rightName := by
  simp [reconstructCanonical?]

end ProofNetIR
