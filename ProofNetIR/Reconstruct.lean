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

/-- The first sequentializer entry point. It is intentionally explicit about
the fragment it supports instead of pretending to sequentialize every correct
net before that theorem has been formalized. -/
def reconstructCanonical (leftName rightName : String) :
    Derivation [
      .tensor (.atom leftName true) (.atom rightName true),
      .par (.atom leftName false) (.atom rightName false)
    ] :=
  Derivation.canonical leftName rightName

end ProofNetIR
