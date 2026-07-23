import ProofNetIR.DesequentializationSoundness
import ProofNetIR.IntrinsicCanonical

namespace ProofNetIR

/-- Proof-bearing result of checking a proposed cut-free derivation against a
certificate.

Unlike `Certificate.check`, this verifier does not enumerate switching graphs.
It validates the submitted certificate structurally, independently infers and
desequentializes the derivation, and compares the two proof nets through the
proved non-factorial intrinsic canonical code. -/
structure DerivationVerificationResult (input : Certificate) where
  tree : CutFreeDerivation
  sequent : List Formula
  output : Certificate
  inputStructural : input.StructurallyWellFormed
  inputLabels : input.conclusionFormulas? = some sequent
  inferred : tree.infer? = some sequent
  desequentialized : tree.desequentialize? = some output
  outputAccepted : output.check = true
  equivalent : output.ProofNetEquivalent input

namespace DerivationVerificationResult

/-- A successfully verified derivation is accepted by the independent
formula-level inference relation. -/
theorem inferAccepted {input : Certificate}
    (result : DerivationVerificationResult input) :
    ∃ sequent, result.tree.infer? = some sequent :=
  ⟨result.sequent, result.inferred⟩

/-- A successfully verified derivation denotes a checker-accepted proof net. -/
theorem outputCheck {input : Certificate}
    (result : DerivationVerificationResult input) :
    result.output.check = true :=
  result.outputAccepted

/-- The verified output is exactly the submitted proof net up to the public
`ProofNetEquivalent` relation. -/
theorem outputEquivalent {input : Certificate}
    (result : DerivationVerificationResult input) :
    result.output.ProofNetEquivalent input :=
  result.equivalent

end DerivationVerificationResult

namespace Certificate

/-- Verify a proposed derivation without evaluating the exponential
all-switchings checker on the input.

The only Boolean gate on the input is `wellFormed`; proof-net identity is
decided by the polynomial intrinsic canonical code.  The acceptance proof for
the derivation-produced output is supplied by
`CutFreeDerivation.desequentialize?_check` and is erased at runtime. -/
def verifyDerivation? (input : Certificate) (tree : CutFreeDerivation) :
    Option (DerivationVerificationResult input) :=
  if inputWellFormed : input.wellFormed = true then
    match input.conclusionFormulas? with
    | none => none
    | some sequent =>
        if inputLabels :
            input.conclusionFormulas? = some sequent then
          if inferred : tree.infer? = some sequent then
            match tree.desequentialize? with
            | none => none
            | some output =>
                if desequentialized :
                    tree.desequentialize? = some output then
                  if sameCode :
                      output.intrinsicCanonicalCode =
                        input.intrinsicCanonicalCode then
                    let inputStructural :
                        input.StructurallyWellFormed :=
                      input.wellFormed_iff_structurallyWellFormed.mp
                        inputWellFormed
                    let outputAccepted : output.check = true :=
                      CutFreeDerivation.desequentialize?_check
                        desequentialized
                    let outputStructural :
                        output.StructurallyWellFormed :=
                      (output.check_sound_declarative outputAccepted).1
                    let equivalent : output.ProofNetEquivalent input :=
                      (proofNetEquivalent_iff_intrinsicCanonicalCode_eq
                        outputStructural inputStructural).mpr sameCode
                    some {
                      tree
                      sequent
                      output
                      inputStructural
                      inputLabels
                      inferred
                      desequentialized
                      outputAccepted
                      equivalent }
                  else
                    none
                else
                  none
          else
            none
        else
          none
  else
    none

/-- Successful verification exposes the complete proof-bearing contract
without requiring clients to unfold the executable verifier. -/
theorem verifyDerivation?_sound
    {input : Certificate} {tree : CutFreeDerivation}
    {result : DerivationVerificationResult input}
    (_equation : input.verifyDerivation? tree = some result) :
    input.StructurallyWellFormed ∧
      input.conclusionFormulas? = some result.sequent ∧
      result.tree.infer? = some result.sequent ∧
      result.tree.desequentialize? = some result.output ∧
      result.output.check = true ∧
      result.output.ProofNetEquivalent input :=
  ⟨result.inputStructural, result.inputLabels, result.inferred,
    result.desequentialized, result.outputAccepted, result.equivalent⟩

/-- The verifier is complete for every structurally well-formed input and
proposed derivation whose desequentialization is proof-net-equivalent to that
input. -/
theorem verifyDerivation?_complete
    {input output : Certificate} {tree : CutFreeDerivation}
    {sequent : List Formula}
    (inputStructural : input.StructurallyWellFormed)
    (inputLabels : input.conclusionFormulas? = some sequent)
    (inferred : tree.infer? = some sequent)
    (desequentialized : tree.desequentialize? = some output)
    (equivalent : output.ProofNetEquivalent input) :
    ∃ result : DerivationVerificationResult input,
      input.verifyDerivation? tree = some result := by
  have inputWellFormed : input.wellFormed = true :=
    input.wellFormed_iff_structurallyWellFormed.mpr inputStructural
  have sameCode :
      output.intrinsicCanonicalCode = input.intrinsicCanonicalCode :=
    equivalent.intrinsicCanonicalCode_eq
  simp [verifyDerivation?, inputWellFormed, inputLabels, inferred,
    desequentialized, sameCode]

/-- Boolean convenience wrapper for callers that only need acceptance. -/
def verifiesDerivation (input : Certificate)
    (tree : CutFreeDerivation) : Bool :=
  (input.verifyDerivation? tree).isSome

/-- Boolean acceptance is exactly the existence of a proof-bearing verifier
result. -/
theorem verifiesDerivation_eq_true_iff
    {input : Certificate} {tree : CutFreeDerivation} :
    input.verifiesDerivation tree = true ↔
      ∃ result : DerivationVerificationResult input,
        input.verifyDerivation? tree = some result := by
  unfold verifiesDerivation
  cases equation : input.verifyDerivation? tree with
  | none => simp
  | some result => simp

end Certificate

end ProofNetIR
