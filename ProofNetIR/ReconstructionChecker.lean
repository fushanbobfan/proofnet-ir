import ProofNetIR.DerivationVerifier
import ProofNetIR.ExecutableSequentialization

namespace ProofNetIR

namespace Certificate

private def firstVerification
    (verify : α → Option β) : List α → Option β
  | [] => none
  | candidate :: rest =>
      match verify candidate with
      | some result => some result
      | none => firstVerification verify rest

private theorem firstVerification_isSome_of_mem
    (verify : α → Option β) (candidates : List α)
    (candidate : α) (membership : candidate ∈ candidates)
    (success : (verify candidate).isSome = true) :
    (firstVerification verify candidates).isSome = true := by
  induction candidates with
  | nil => simp at membership
  | cons head tail ih =>
      simp only [List.mem_cons] at membership
      rcases membership with same | membership
      · subst head
        cases equation : verify candidate with
        | none => simp [equation] at success
        | some result => simp [firstVerification, equation]
      · cases equation : verify head with
        | none =>
            simpa [firstVerification, equation] using ih membership
        | some result => simp [firstVerification, equation]

/-- Try every formula-compatible boundary occurrence order and return the first
cut-free derivation that the non-switching verifier proves equivalent to the
input certificate. -/
private def alignAndVerify? (input : Certificate)
    (tree : CutFreeDerivation) (target : List Formula) :
    Option (DerivationVerificationResult input) :=
  match tree.infer? with
  | none => none
  | some source =>
      firstVerification
        (fun order =>
          input.verifyDerivation?
            (CutFreeDerivation.exchange order tree))
        (matchingFormulaOrders source target)

private theorem alignAndVerify?_complete_of_sequentialization
    {input : Certificate} (inputStructural : input.StructurallyWellFormed)
    (result : SequentializationResult input)
    {rawTree : CutFreeDerivation} {order : List Nat}
    (treeShape :
      result.tree = CutFreeDerivation.exchange order rawTree) :
    (alignAndVerify? input rawTree result.sequent).isSome = true := by
  cases sourceEquation : rawTree.infer? with
  | none =>
      have impossible : result.tree.infer? = none := by
        simp [treeShape, CutFreeDerivation.infer?, sourceEquation]
      rw [result.inferred] at impossible
      contradiction
  | some source =>
      have alignedInference :
          (CutFreeDerivation.exchange order rawTree).infer? =
            some result.sequent := by
        simpa [← treeShape] using result.inferred
      have reordered :
          CutFreeDerivation.reorder? source order =
            some result.sequent := by
        simpa [CutFreeDerivation.infer?, sourceEquation] using
          alignedInference
      have orderMembership :
          order ∈ matchingFormulaOrders source result.sequent :=
        matchingFormulaOrders_complete_of_reorder? reordered
      rcases input.verifyDerivation?_complete inputStructural
          result.inputLabels result.inferred result.desequentialized
          result.equivalent with
        ⟨verified, verifiedEquation⟩
      have candidateSuccess :
          (input.verifyDerivation?
            (CutFreeDerivation.exchange order rawTree)).isSome = true := by
        rw [← treeShape]
        simp [verifiedEquation]
      unfold alignAndVerify?
      simp only [sourceEquation]
      exact firstVerification_isSome_of_mem _ _ order orderMembership
        candidateSuccess

private def axiomReconstruction? (input : Certificate)
    (target : List Formula) :
    Option (DerivationVerificationResult input) :=
  firstVerification
    (fun formula =>
      match formula with
      | .atom name positive =>
          alignAndVerify? input (.axiom name positive) target
      | _ => none)
    input.formulas.toList

private theorem axiomReconstruction?_of_atom
    {input : Certificate} {target : List Formula}
    {name : String} {positive : Bool}
    (formulaMembership :
      Formula.atom name positive ∈ input.formulas.toList)
    (aligned :
      (alignAndVerify? input (.axiom name positive) target).isSome =
        true) :
    (axiomReconstruction? input target).isSome = true := by
  unfold axiomReconstruction?
  apply firstVerification_isSome_of_mem _ _ (.atom name positive)
    formulaMembership
  exact aligned

private theorem axiomReconstruction?_complete
    {input : Certificate} (accepted : input.check = true)
    {target : List Formula}
    (labels : input.conclusionFormulas? = some target)
    (noConnective : ¬ ∃ link ∈ input.links,
      link.isConnective = true) :
    (axiomReconstruction? input target).isSome = true := by
  have correct := input.check_sound_declarative accepted
  have inputStructural := correct.1
  rcases correct.axiomOnly_certificate_cases noConnective with
    ⟨name, positive, shape⟩
  rcases shape with shape | shape | shape | shape
  · subst input
    simp [Certificate.conclusionFormulas?, Certificate.formula?] at labels
    subst target
    apply axiomReconstruction?_of_atom (name := name)
      (positive := positive) (by simp)
    let result : SequentializationResult
        ({ formulas := #[.atom name positive, .atom name (!positive)]
           links := [.axiom 0 1]
           conclusions := [0, 1] } : Certificate) := {
      tree := .exchange [0, 1] (.axiom name positive)
      sequent := [.atom name positive, .atom name (!positive)]
      output := {
        formulas := #[.atom name positive, .atom name (!positive)]
        links := [.axiom 0 1]
        conclusions := [0, 1] }
      inferred := axiomExchangeIdentity_infer name positive
      desequentialized :=
        axiomExchangeIdentity_desequentialize name positive
      outputLabels := rfl
      equivalent := .refl _ }
    exact alignAndVerify?_complete_of_sequentialization
      inputStructural result rfl
  · subst input
    simp [Certificate.conclusionFormulas?, Certificate.formula?] at labels
    subst target
    apply axiomReconstruction?_of_atom (name := name)
      (positive := positive) (by simp)
    let result : SequentializationResult
        ({ formulas := #[.atom name positive, .atom name (!positive)]
           links := [.axiom 0 1]
           conclusions := [1, 0] } : Certificate) := {
      tree := .exchange [1, 0] (.axiom name positive)
      sequent := [.atom name (!positive), .atom name positive]
      output := {
        formulas := #[.atom name positive, .atom name (!positive)]
        links := [.axiom 0 1]
        conclusions := [1, 0] }
      inferred := axiomExchangeSwap_infer name positive
      desequentialized :=
        axiomExchangeSwap_desequentialize name positive
      outputLabels := rfl
      equivalent := .refl _ }
    exact alignAndVerify?_complete_of_sequentialization
      inputStructural result rfl
  · subst input
    simp [Certificate.conclusionFormulas?, Certificate.formula?] at labels
    subst target
    apply axiomReconstruction?_of_atom (name := name)
      (positive := positive) (by simp)
    let result : SequentializationResult
        ({ formulas := #[.atom name (!positive), .atom name positive]
           links := [.axiom 1 0]
           conclusions := [0, 1] } : Certificate) := {
      tree := .exchange [1, 0] (.axiom name positive)
      sequent := [.atom name (!positive), .atom name positive]
      output := {
        formulas := #[.atom name positive, .atom name (!positive)]
        links := [.axiom 0 1]
        conclusions := [1, 0] }
      inferred := axiomExchangeSwap_infer name positive
      desequentialized :=
        axiomExchangeSwap_desequentialize name positive
      outputLabels := rfl
      equivalent := (axiomDirectSwap name positive [1, 0]).toProofNetEquivalent }
    exact alignAndVerify?_complete_of_sequentialization
      inputStructural result rfl
  · subst input
    simp [Certificate.conclusionFormulas?, Certificate.formula?] at labels
    subst target
    apply axiomReconstruction?_of_atom (name := name)
      (positive := positive) (by simp)
    let result : SequentializationResult
        ({ formulas := #[.atom name (!positive), .atom name positive]
           links := [.axiom 1 0]
           conclusions := [1, 0] } : Certificate) := {
      tree := .exchange [0, 1] (.axiom name positive)
      sequent := [.atom name positive, .atom name (!positive)]
      output := {
        formulas := #[.atom name positive, .atom name (!positive)]
        links := [.axiom 0 1]
        conclusions := [0, 1] }
      inferred := axiomExchangeIdentity_infer name positive
      desequentialized :=
        axiomExchangeIdentity_desequentialize name positive
      outputLabels := rfl
      equivalent := (axiomDirectSwap name positive [0, 1]).toProofNetEquivalent }
    exact alignAndVerify?_complete_of_sequentialization
      inputStructural result rfl

private def parReconstruction?
    (recurse : (premise : Certificate) →
      Option (DerivationVerificationResult premise))
    (input : Certificate) (target : List Formula) :
    Option (DerivationVerificationResult input) :=
  firstVerification
    (fun candidate =>
      let (left, right, conclusion) := candidate
      match input.peelTerminalParCandidate? left right conclusion with
      | none => none
      | some premise =>
          match recurse premise with
          | none => none
          | some premiseResult =>
              if premiseResult.sequent.length < 2 then
                none
              else
                let focus := premiseResult.sequent.length - 2
                alignAndVerify? input
                  (.par focus focus premiseResult.tree) target)
    input.terminalPars

private theorem parReconstruction?_complete_of_candidate
    (recurse : (premise : Certificate) →
      Option (DerivationVerificationResult premise))
    {input premise : Certificate} {target : List Formula}
    {left right conclusion : Vertex}
    (membership : (left, right, conclusion) ∈ input.terminalPars)
    (premiseEquation :
      input.peelTerminalParCandidate? left right conclusion =
        some premise)
    (premiseResult : DerivationVerificationResult premise)
    (recursiveEquation : recurse premise = some premiseResult)
    (premiseLength : 2 ≤ premiseResult.sequent.length)
    (aligned :
      (alignAndVerify? input
        (.par (premiseResult.sequent.length - 2)
          (premiseResult.sequent.length - 2) premiseResult.tree)
        target).isSome = true) :
    (parReconstruction? recurse input target).isSome = true := by
  unfold parReconstruction?
  apply firstVerification_isSome_of_mem _ _
    (left, right, conclusion) membership
  have notShort : ¬ premiseResult.sequent.length < 2 :=
    Nat.not_lt.mpr premiseLength
  simp [premiseEquation, recursiveEquation, notShort, aligned]

private def tensorReconstruction?
    (recurse : (premise : Certificate) →
      Option (DerivationVerificationResult premise))
    (input : Certificate) (target : List Formula) :
    Option (DerivationVerificationResult input) :=
  firstVerification
    (fun candidate =>
      let (left, right, conclusion) := candidate
      match input.splitTerminalTensorCandidate? left right conclusion with
      | none => none
      | some (leftPremise, rightPremise) =>
          match recurse leftPremise with
          | none => none
          | some leftResult =>
              match recurse rightPremise with
              | none => none
              | some rightResult =>
                  if leftResult.sequent.isEmpty ||
                      rightResult.sequent.isEmpty then
                    none
                  else
                    alignAndVerify? input
                      (.tensor (leftResult.sequent.length - 1)
                        (rightResult.sequent.length - 1)
                        leftResult.tree rightResult.tree)
                      target)
    input.terminalTensors

private theorem tensorReconstruction?_complete_of_candidate
    (recurse : (premise : Certificate) →
      Option (DerivationVerificationResult premise))
    {input leftPremise rightPremise : Certificate}
    {target : List Formula} {left right conclusion : Vertex}
    (membership :
      (left, right, conclusion) ∈ input.terminalTensors)
    (splitEquation :
      input.splitTerminalTensorCandidate? left right conclusion =
        some (leftPremise, rightPremise))
    (leftResult : DerivationVerificationResult leftPremise)
    (rightResult : DerivationVerificationResult rightPremise)
    (leftRecursive : recurse leftPremise = some leftResult)
    (rightRecursive : recurse rightPremise = some rightResult)
    (leftLength : 1 ≤ leftResult.sequent.length)
    (rightLength : 1 ≤ rightResult.sequent.length)
    (aligned :
      (alignAndVerify? input
        (.tensor (leftResult.sequent.length - 1)
          (rightResult.sequent.length - 1)
          leftResult.tree rightResult.tree)
        target).isSome = true) :
    (tensorReconstruction? recurse input target).isSome = true := by
  unfold tensorReconstruction?
  apply firstVerification_isSome_of_mem _ _
    (left, right, conclusion) membership
  have leftNonempty : leftResult.sequent.isEmpty = false := by
    cases equation : leftResult.sequent with
    | nil =>
        have zero : leftResult.sequent.length = 0 := by simp [equation]
        omega
    | cons head tail => rfl
  have rightNonempty : rightResult.sequent.isEmpty = false := by
    cases equation : rightResult.sequent with
    | nil =>
        have zero : rightResult.sequent.length = 0 := by simp [equation]
        omega
    | cons head tail => rfl
  simp [splitEquation, leftRecursive, rightRecursive, leftNonempty,
    rightNonempty, aligned]

/-- Fuel-bounded inverse-rule reconstruction that never evaluates
`Certificate.check` or enumerates switching graphs.

Every returned candidate has already passed `verifyDerivation?`, so the result
contains an exact `ProofNetEquivalent` proof. Fuel bounds recursive formula
occurrence removal; the public wrapper supplies one more than the input
formula count. -/
def reconstructDerivationWithFuel? : Nat → (input : Certificate) →
    Option (DerivationVerificationResult input)
  | 0, _ => none
  | fuel + 1, input =>
      match input.conclusionFormulas? with
      | none => none
      | some target =>
          match axiomReconstruction? input target with
          | some result => some result
          | none =>
              match parReconstruction?
                  (reconstructDerivationWithFuel? fuel) input target with
              | some result => some result
              | none =>
                  tensorReconstruction?
                    (reconstructDerivationWithFuel? fuel) input target

private theorem exists_some_of_isSome
    {value : Option α} (success : value.isSome = true) :
    ∃ result, value = some result := by
  cases equation : value with
  | none => simp [equation] at success
  | some result => exact ⟨result, rfl⟩

/-- Universal completeness of the checker-free inverse-rule search at every
fuel bound strictly above the input occurrence count. The theorem uses the
reference checker only as its mathematical premise; the executable function
itself has no checker call. -/
theorem reconstructDerivationWithFuel?_complete
    (fuel : Nat) (input : Certificate)
    (accepted : input.check = true)
    (fuelBound : input.formulas.size < fuel) :
    ∃ result : DerivationVerificationResult input,
      input.reconstructDerivationWithFuel? fuel = some result := by
  induction fuel generalizing input with
  | zero => omega
  | succ fuel ih =>
      have correct : input.DeclarativelyCorrect :=
        input.check_iff_declarativelyCorrect.mp accepted
      have structural : input.StructurallyWellFormed := correct.1
      rcases input.sequentialization_of_check accepted with
        ⟨existenceResult⟩
      let target := existenceResult.sequent
      have labels : input.conclusionFormulas? = some target := by
        simpa [target] using existenceResult.inputLabels
      by_cases connectiveExists : ∃ link ∈ input.links,
          link.isConnective = true
      · rcases correct.terminalPar_or_splittingTensor_exists
          connectiveExists with
        ⟨left, right, conclusion, terminal | splitting⟩
        · let premise :=
            input.peelTerminalPar left right conclusion
          have premiseAccepted : premise.check = true :=
            input.peelTerminalPar_check_of_check structural terminal
              accepted
          have premiseSmaller :
              premise.formulas.size < input.formulas.size :=
            input.peelTerminalPar_formulas_size_lt structural terminal
          have premiseFuel : premise.formulas.size < fuel := by
            omega
          rcases ih premise premiseAccepted premiseFuel with
            ⟨premiseResult, recursiveEquation⟩
          have premiseCandidate :
              input.peelTerminalParCandidate? left right conclusion =
                some premise := by
            simpa [premise] using
              input.peelTerminalParCandidate?_eq_some structural terminal
          let premiseSequentialization :=
            premiseResult.toSequentializationResult
          rcases TerminalPar.sequentializationResultShaped structural
              terminal premiseAccepted premiseSequentialization with
            ⟨composed, order, treeShape, premiseLength⟩
          have aligned :
              (alignAndVerify? input
                (.par (premiseResult.sequent.length - 2)
                  (premiseResult.sequent.length - 2)
                  premiseResult.tree)
                target).isSome = true := by
            have shaped :
                composed.tree =
                  CutFreeDerivation.exchange order
                    (.par (premiseResult.sequent.length - 2)
                      (premiseResult.sequent.length - 2)
                      premiseResult.tree) := by
              simpa [premiseSequentialization,
                DerivationVerificationResult.toSequentializationResult]
                using treeShape
            have sameTarget : composed.sequent = target := by
              exact Option.some.inj
                (composed.inputLabels.symm.trans labels)
            rw [← sameTarget]
            exact alignAndVerify?_complete_of_sequentialization
              structural composed shaped
          have membership :
              (left, right, conclusion) ∈ input.terminalPars :=
            (input.mem_terminalPars_iff left right conclusion).mpr
              terminal
          have parFound :=
            parReconstruction?_complete_of_candidate
              (reconstructDerivationWithFuel? fuel)
              membership premiseCandidate premiseResult
              recursiveEquation
              (by
                simpa [premiseSequentialization,
                  DerivationVerificationResult.toSequentializationResult]
                  using premiseLength)
              aligned
          rcases exists_some_of_isSome parFound with
            ⟨parResult, parEquation⟩
          unfold reconstructDerivationWithFuel?
          rw [labels]
          cases axiomEquation :
              axiomReconstruction? input target with
          | some axiomResult =>
              exact ⟨axiomResult, by simp [axiomEquation]⟩
          | none =>
              exact ⟨parResult, by simp [axiomEquation, parEquation]⟩
        · rcases input.splitTerminalTensorCandidate?_eq_some_exists
              structural splitting with
            ⟨leftPremise, rightPremise, splitEquation⟩
          rcases input.splitTerminalTensorCandidate?_check_of_check
              structural splitting splitEquation accepted with
            ⟨leftAccepted, rightAccepted⟩
          have leftSmaller :
              leftPremise.formulas.size < input.formulas.size :=
            input.splitTerminalTensorCandidate?_left_formulas_size_lt
              structural splitting splitEquation
          have rightSmaller :
              rightPremise.formulas.size < input.formulas.size :=
            input.splitTerminalTensorCandidate?_right_formulas_size_lt
              structural splitting splitEquation
          have leftFuel : leftPremise.formulas.size < fuel := by omega
          have rightFuel : rightPremise.formulas.size < fuel := by omega
          rcases ih leftPremise leftAccepted leftFuel with
            ⟨leftResult, leftRecursive⟩
          rcases ih rightPremise rightAccepted rightFuel with
            ⟨rightResult, rightRecursive⟩
          let leftSequentialization :=
            leftResult.toSequentializationResult
          let rightSequentialization :=
            rightResult.toSequentializationResult
          rcases TerminalTensor.sequentializationResultShaped structural
              splitting splitEquation leftAccepted rightAccepted
              leftSequentialization rightSequentialization with
            ⟨composed, order, treeShape, leftLength, rightLength⟩
          have aligned :
              (alignAndVerify? input
                (.tensor (leftResult.sequent.length - 1)
                  (rightResult.sequent.length - 1)
                  leftResult.tree rightResult.tree)
                target).isSome = true := by
            have shaped :
                composed.tree =
                  CutFreeDerivation.exchange order
                    (.tensor (leftResult.sequent.length - 1)
                      (rightResult.sequent.length - 1)
                      leftResult.tree rightResult.tree) := by
              simpa [leftSequentialization, rightSequentialization,
                DerivationVerificationResult.toSequentializationResult]
                using treeShape
            have sameTarget : composed.sequent = target := by
              exact Option.some.inj
                (composed.inputLabels.symm.trans labels)
            rw [← sameTarget]
            exact alignAndVerify?_complete_of_sequentialization
              structural composed shaped
          have membership :
              (left, right, conclusion) ∈ input.terminalTensors :=
            (input.mem_terminalTensors_iff left right conclusion).mpr
              splitting.1
          have tensorFound :=
            tensorReconstruction?_complete_of_candidate
              (reconstructDerivationWithFuel? fuel)
              membership splitEquation leftResult rightResult
              leftRecursive rightRecursive
              (by
                simpa [leftSequentialization,
                  DerivationVerificationResult.toSequentializationResult]
                  using leftLength)
              (by
                simpa [rightSequentialization,
                  DerivationVerificationResult.toSequentializationResult]
                  using rightLength)
              aligned
          rcases exists_some_of_isSome tensorFound with
            ⟨tensorResult, tensorEquation⟩
          unfold reconstructDerivationWithFuel?
          rw [labels]
          cases axiomEquation :
              axiomReconstruction? input target with
          | some axiomResult =>
              exact ⟨axiomResult, by simp [axiomEquation]⟩
          | none =>
              cases parEquation : parReconstruction?
                  (reconstructDerivationWithFuel? fuel) input target with
              | some parResult =>
                  exact ⟨parResult, by
                    simp [axiomEquation, parEquation]⟩
              | none =>
                  exact ⟨tensorResult, by
                    simp [axiomEquation, parEquation, tensorEquation]⟩
      · have axiomFound :=
          axiomReconstruction?_complete accepted labels
            connectiveExists
        rcases exists_some_of_isSome axiomFound with
          ⟨axiomResult, axiomEquation⟩
        unfold reconstructDerivationWithFuel?
        rw [labels]
        exact ⟨axiomResult, by simp [axiomEquation]⟩

/-- Attempt to reconstruct and verify a cut-free derivation from a bare
certificate without calling the all-switchings checker. -/
def reconstructDerivation? (input : Certificate) :
    Option (DerivationVerificationResult input) :=
  input.reconstructDerivationWithFuel? (input.formulas.size + 1)

/-- Every certificate accepted by the reference all-switchings semantics is
accepted by the executable checker-free reconstruction path. -/
theorem reconstructDerivation?_complete
    (input : Certificate) (accepted : input.check = true) :
    ∃ result : DerivationVerificationResult input,
      input.reconstructDerivation? = some result := by
  exact input.reconstructDerivationWithFuel?_complete
    (input.formulas.size + 1) accepted (by omega)

/-- Soundness is carried directly by the dependent result: a successful
checker-free reconstruction has a formula-valid cut-free derivation whose
desequentialization is accepted and exactly proof-net-equivalent to the
input. -/
theorem reconstructDerivation?_sound
    {input : Certificate} {result : DerivationVerificationResult input}
    (_equation : input.reconstructDerivation? = some result) :
    input.StructurallyWellFormed ∧
      input.conclusionFormulas? = some result.sequent ∧
      result.tree.infer? = some result.sequent ∧
      result.tree.desequentialize? = some result.output ∧
      result.output.check = true ∧
      result.output.ProofNetEquivalent input :=
  ⟨result.inputStructural, result.inputLabels, result.inferred,
    result.desequentialized, result.outputAccepted, result.equivalent⟩

/-- A successful checker-free reconstruction is accepted by the reference
proof-net checker. This is a theorem about the returned proof evidence; the
runtime reconstruction function does not evaluate the reference checker. -/
theorem reconstructDerivation?_accepted
    {input : Certificate} {result : DerivationVerificationResult input}
    (_equation : input.reconstructDerivation? = some result) :
    input.check = true := by
  rw [← result.equivalent.check_eq]
  exact result.outputAccepted

/-- Boolean convenience wrapper for checker-free automatic reconstruction. -/
def reconstructsDerivation (input : Certificate) : Bool :=
  input.reconstructDerivation?.isSome

/-- Boolean success is exactly the existence of a proof-bearing automatic
reconstruction result. -/
theorem reconstructsDerivation_eq_true_iff
    {input : Certificate} :
    input.reconstructsDerivation = true ↔
      ∃ result : DerivationVerificationResult input,
        input.reconstructDerivation? = some result := by
  unfold reconstructsDerivation
  cases input.reconstructDerivation? <;> simp

/-- The checker-free automatic reconstruction decision accepts exactly the
same certificates as the reference all-switchings checker. -/
theorem reconstructsDerivation_eq_true_iff_check
    (input : Certificate) :
    input.reconstructsDerivation = true ↔ input.check = true := by
  constructor
  · intro reconstructed
    rcases input.reconstructsDerivation_eq_true_iff.mp reconstructed with
      ⟨result, equation⟩
    exact input.reconstructDerivation?_accepted equation
  · intro accepted
    rcases input.reconstructDerivation?_complete accepted with
      ⟨result, equation⟩
    exact input.reconstructsDerivation_eq_true_iff.mpr
      ⟨result, equation⟩

/-- Boolean equality between checker-free reconstruction and the reference
all-switchings checker. -/
theorem reconstructsDerivation_eq_check (input : Certificate) :
    input.reconstructsDerivation = input.check := by
  apply Bool.eq_iff_iff.mpr
  exact input.reconstructsDerivation_eq_true_iff_check

end Certificate

end ProofNetIR
