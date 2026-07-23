import ProofNetIR.DerivationVerifier
import ProofNetIR.ExecutableSequentialization

namespace ProofNetIR

/-- Explicit input-size envelope for the fail-closed reconstruction API.
These limits bound formula occurrences, stored links, and ordered conclusions
before structure-guided search begins. -/
structure ReconstructionLimits where
  maxFormulaOccurrences : Nat
  maxLinks : Nat
  maxConclusions : Nat
  deriving Repr, DecidableEq

namespace ReconstructionLimits

/-- CI-qualified default envelope.  The adversarial suite exercises accepted
inputs through 126 formula occurrences, 94 links, and 22 conclusions below
these ceilings. -/
def qualified : ReconstructionLimits where
  maxFormulaOccurrences := 128
  maxLinks := 96
  maxConclusions := 24

end ReconstructionLimits

/-- Structured failures from bounded structure-guided reconstruction.
`noCandidate` and `candidateVerificationFailed` are deliberately
inconclusive: callers must not reinterpret them as logical rejection. -/
inductive ReconstructionError where
  | formulaLimitExceeded (actual limit : Nat)
  | linkLimitExceeded (actual limit : Nat)
  | conclusionLimitExceeded (actual limit : Nat)
  | structurallyMalformed
  | noCandidate
  | candidateVerificationFailed
  deriving Repr, DecidableEq

namespace ReconstructionError

/-- Stable reader-facing diagnostic for bounded reconstruction failures. -/
def message : ReconstructionError → String
  | .formulaLimitExceeded actual limit =>
      s!"formula occurrence limit exceeded: {actual} > {limit}"
  | .linkLimitExceeded actual limit =>
      s!"link limit exceeded: {actual} > {limit}"
  | .conclusionLimitExceeded actual limit =>
      s!"conclusion limit exceeded: {actual} > {limit}"
  | .structurallyMalformed =>
      "certificate failed structural well-formedness"
  | .noCandidate =>
      "bounded structure-guided reconstruction found no candidate"
  | .candidateVerificationFailed =>
      "bounded reconstruction candidate failed exact proof-net verification"

end ReconstructionError

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

/-- Heuristic boundary alignment induced by the two intrinsic occurrence
traversals. A candidate is returned only when every target boundary root has a
corresponding source traversal position and source boundary occurrence.
`alignAndVerify?` remains authoritative and the complete formula-order list is
retained as a fallback. -/
private def intrinsicBoundaryOrder? (source target : Certificate) :
    Option (List Nat) := do
  let sourceTraversal := source.intrinsicTraversalVertices
  let targetTraversal := target.intrinsicTraversalVertices
  if sourceTraversal.length != targetTraversal.length then
    none
  target.conclusions.mapM fun targetRoot => do
    let traversalIndex := targetTraversal.idxOf targetRoot
    let sourceRoot ← sourceTraversal[traversalIndex]?
    let boundaryIndex := source.conclusions.idxOf sourceRoot
    if boundaryIndex < source.conclusions.length then
      some boundaryIndex
    else
      none

private def axiomMate? (certificate : Certificate) (vertex : Vertex) :
    Option (Bool × Vertex) :=
  match certificate.links.find?
      (fun link => link.containsAxiomEndpoint vertex) with
  | some (.axiom left right) =>
      if left == vertex then
        some (true, right)
      else if right == vertex then
        some (false, left)
      else
        none
  | _ => none

private def boundaryAddress? (certificate : Certificate)
    (vertex : Vertex) : List Vertex → Option (Formula × Nat)
  | [] => none
  | root :: rest =>
      let walk := certificate.occurrenceWalk? root
      let offset := walk.idxOf vertex
      if offset < walk.length then
        match certificate.formula? root with
        | some formula => some (formula, offset)
        | none => none
      else
        boundaryAddress? certificate vertex rest

/-- A vertex-number-free description of how the atomic leaves below one
boundary root are attached to the other boundary formula trees.  Formula-tree
preorder offsets identify leaf addresses without depending on submitted
vertex numbers or link storage order. -/
private def boundaryAxiomProfile (certificate : Certificate)
    (root : Vertex) : List (Bool × Formula × Nat) :=
  (certificate.occurrenceWalk? root).filterMap fun vertex =>
    match certificate.formula? vertex with
    | some (.atom _ _) =>
        match axiomMate? certificate vertex with
        | some (role, mate) =>
            match boundaryAddress? certificate mate
                certificate.conclusions with
            | some (boundaryFormula, offset) =>
                some (role, boundaryFormula, offset)
            | none => none
        | none => none
    | _ => none

private def boundaryProfileCompatible (source target : Certificate)
    (targetPosition sourcePosition : Nat) : Bool :=
  match target.conclusions[targetPosition]?,
      source.conclusions[sourcePosition]? with
  | some targetRoot, some sourceRoot =>
      source.boundaryAxiomProfile sourceRoot ==
        target.boundaryAxiomProfile targetRoot
  | _, _ => false

private def profiledBoundaryOrderVisit? (source target : Certificate)
    (sourceLabels : List Formula) (position : Nat) (used : List Nat) :
    List Formula → Option (List Nat)
  | [] => some []
  | formula :: rest => do
      let sourcePosition ←
        (List.range sourceLabels.length).find? fun candidate =>
          !used.contains candidate &&
            sourceLabels[candidate]? == some formula &&
            boundaryProfileCompatible source target position candidate
      let suffix ← profiledBoundaryOrderVisit? source target sourceLabels
        (position + 1) (sourcePosition :: used) rest
      pure (sourcePosition :: suffix)

/-- Greedily select one boundary occurrence order whose complete
formula-tree/axiom profiles agree. This avoids materializing factorial lists
of repeated atomic conclusions on the preferred path. Equal profiles need not
be globally interchangeable: the completed tree is still verified, and the
exhaustive formula-only search remains the proved completeness fallback. -/
private def profiledBoundaryOrder? (source target : Certificate)
    (sourceLabels targetLabels : List Formula) : Option (List Nat) :=
  if sourceLabels.length != targetLabels.length then
    none
  else
    profiledBoundaryOrderVisit? source target sourceLabels 0 [] targetLabels

/-- Try every formula-compatible boundary occurrence order and return the first
cut-free derivation that the non-switching verifier proves equivalent to the
input certificate. -/
private def alignAndVerify? (input : Certificate)
    (tree : CutFreeDerivation) (target : List Formula) :
    Option (DerivationVerificationResult input) :=
  match tree.infer? with
  | none => none
  | some source =>
      let verify := fun order =>
        input.verifyDerivation?
          (CutFreeDerivation.exchange order tree)
      let preferred :=
        match tree.desequentialize? with
        | none => []
        | some sourceCertificate =>
            (profiledBoundaryOrder? sourceCertificate input source target).toList ++
              (intrinsicBoundaryOrder? sourceCertificate input).toList
      match firstVerification verify preferred with
      | some result => some result
      | none =>
          firstVerification verify (matchingFormulaOrders source target)

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
      let verify := fun candidateOrder =>
        input.verifyDerivation?
          (CutFreeDerivation.exchange candidateOrder rawTree)
      let preferred :=
        match rawTree.desequentialize? with
        | none => []
        | some sourceCertificate =>
            (profiledBoundaryOrder? sourceCertificate input source
              result.sequent).toList ++
              (intrinsicBoundaryOrder? sourceCertificate input).toList
      cases preferredEquation : firstVerification verify preferred with
      | some preferredResult => rfl
      | none =>
          apply firstVerification_isSome_of_mem _ _ order
          · exact orderMembership
          · exact candidateSuccess

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

private def boundaryOrderedCandidates (input : Certificate)
    (candidates : List (Vertex × Vertex × Vertex)) :
    List (Vertex × Vertex × Vertex) :=
  input.conclusions.flatMap fun conclusion =>
    candidates.filter fun candidate => candidate.2.2 == conclusion

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
    (boundaryOrderedCandidates input input.terminalPars ++
      input.terminalPars)

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
    (left, right, conclusion)
    (List.mem_append.mpr (Or.inr membership))
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
    (boundaryOrderedCandidates input input.terminalTensors ++
      input.terminalTensors)

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
    (left, right, conclusion)
    (List.mem_append.mpr (Or.inr membership))
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

private def alignTreeProfiled? (input : Certificate)
    (tree : CutFreeDerivation) (target : List Formula) :
    Option CutFreeDerivation := do
  let source ← tree.infer?
  let sourceCertificate ← tree.desequentialize?
  let verify := fun order =>
    let aligned := CutFreeDerivation.exchange order tree
    if aligned.infer? == some target then some aligned else none
  let preferred :=
    (profiledBoundaryOrder? sourceCertificate input source target).toList ++
      (intrinsicBoundaryOrder? sourceCertificate input).toList
  match firstVerification verify preferred with
  | some aligned => some aligned
  | none =>
      firstVerification verify (matchingFormulaOrders source target)

private def reconstructAxiomTree? (input : Certificate)
    (target : List Formula) : Option CutFreeDerivation :=
  firstVerification
    (fun formula =>
      match formula with
      | .atom name positive =>
          alignTreeProfiled? input (.axiom name positive) target
      | _ => none)
    input.formulas.toList

private def reconstructParTree?
    (recurse : Certificate → Option CutFreeDerivation)
    (input : Certificate) (target : List Formula) :
    Option CutFreeDerivation :=
  firstVerification
    (fun candidate =>
      let (left, right, conclusion) := candidate
      match input.peelTerminalParCandidate? left right conclusion with
      | none => none
      | some premise =>
          match recurse premise with
          | none => none
          | some premiseTree =>
              match premiseTree.infer? with
              | none => none
              | some premiseSequent =>
                  if premiseSequent.length < 2 then
                    none
                  else
                    let focus := premiseSequent.length - 2
                    alignTreeProfiled? input
                      (.par focus focus premiseTree) target)
    (boundaryOrderedCandidates input input.terminalPars ++
      input.terminalPars)

private def reconstructTensorTree?
    (recurse : Certificate → Option CutFreeDerivation)
    (input : Certificate) (target : List Formula) :
    Option CutFreeDerivation :=
  firstVerification
    (fun candidate =>
      let (left, right, conclusion) := candidate
      match input.splitTerminalTensorCandidate? left right conclusion with
      | none => none
      | some (leftPremise, rightPremise) =>
          match recurse leftPremise, recurse rightPremise with
          | some leftTree, some rightTree =>
              match leftTree.infer?, rightTree.infer? with
              | some leftSequent, some rightSequent =>
                  if leftSequent.isEmpty || rightSequent.isEmpty then
                    none
                  else
                    alignTreeProfiled? input
                      (.tensor (leftSequent.length - 1)
                        (rightSequent.length - 1)
                        leftTree rightTree)
                      target
              | _, _ => none
          | _, _ => none)
    (boundaryOrderedCandidates input input.terminalTensors ++
      input.terminalTensors)

/-- Heuristic inverse-rule construction that defers proof-net equivalence
verification until the complete tree has been assembled.  The public
reconstructor verifies this fast-path result once and retains the proved
exhaustive search as a fallback. -/
private def reconstructTreeWithFuel? : Nat → Certificate →
    Option CutFreeDerivation
  | 0, _ => none
  | fuel + 1, input =>
      match input.conclusionFormulas? with
      | none => none
      | some target =>
          if input.links.any (·.isConnective) then
            match reconstructParTree?
                (reconstructTreeWithFuel? fuel) input target with
            | some tree => some tree
            | none =>
                reconstructTensorTree?
                  (reconstructTreeWithFuel? fuel) input target
          else
            reconstructAxiomTree? input target

/-- Attempt to reconstruct and verify a cut-free derivation from a bare
certificate without calling the all-switchings checker.  A structure-guided
fast path constructs a complete tree and verifies it once; any failed
heuristic attempt falls back to the proved exhaustive reconstruction. -/
def reconstructDerivation? (input : Certificate) :
    Option (DerivationVerificationResult input) :=
  if _inputWellFormed : input.wellFormed = true then
    match reconstructTreeWithFuel? (input.formulas.size + 1) input with
    | some tree =>
        match input.verifyDerivation? tree with
        | some result => some result
        | none =>
            input.reconstructDerivationWithFuel? (input.formulas.size + 1)
    | none =>
          input.reconstructDerivationWithFuel? (input.formulas.size + 1)
  else
    none

/-- Every certificate accepted by the reference all-switchings semantics is
accepted by the executable checker-free reconstruction path. -/
theorem reconstructDerivation?_complete
    (input : Certificate) (accepted : input.check = true) :
    ∃ result : DerivationVerificationResult input,
      input.reconstructDerivation? = some result := by
  rcases input.reconstructDerivationWithFuel?_complete
      (input.formulas.size + 1) accepted (by omega) with
    ⟨fallback, fallbackEquation⟩
  have inputWellFormed : input.wellFormed = true :=
    input.wellFormed_iff_structurallyWellFormed.mpr
      (input.check_sound_declarative accepted).1
  unfold reconstructDerivation?
  rw [dif_pos inputWellFormed]
  cases fastEquation :
      reconstructTreeWithFuel? (input.formulas.size + 1) input with
  | none =>
      exact ⟨fallback, by simp [fallbackEquation]⟩
  | some tree =>
      cases verificationEquation : input.verifyDerivation? tree with
      | none =>
          exact ⟨fallback, by
            simp [verificationEquation, fallbackEquation]⟩
      | some result =>
          exact ⟨result, by
            simp [verificationEquation]⟩

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

/-- Fail-closed reconstruction within an explicit input-size envelope.

Unlike `reconstructDerivation?`, this API never enters the exhaustive
formula-order fallback.  A limit error or heuristic miss is not a logical
rejection.  Every successful result has still passed `verifyDerivation?` and
carries the same dependent proof evidence as the unbounded API. -/
def reconstructDerivationWithinLimits
    (input : Certificate)
    (limits : ReconstructionLimits := ReconstructionLimits.qualified) :
    Except ReconstructionError (DerivationVerificationResult input) :=
  if limits.maxFormulaOccurrences < input.formulas.size then
    .error (.formulaLimitExceeded input.formulas.size
      limits.maxFormulaOccurrences)
  else if limits.maxLinks < input.links.length then
    .error (.linkLimitExceeded input.links.length limits.maxLinks)
  else if limits.maxConclusions < input.conclusions.length then
    .error (.conclusionLimitExceeded input.conclusions.length
      limits.maxConclusions)
  else if !input.wellFormed then
    .error .structurallyMalformed
  else
    match reconstructTreeWithFuel? (input.formulas.size + 1) input with
    | none => .error .noCandidate
    | some tree =>
        match input.verifyDerivation? tree with
        | none => .error .candidateVerificationFailed
        | some result => .ok result

/-- A successful bounded reconstruction carries the full public soundness
contract, independently of which limits admitted the input. -/
theorem reconstructDerivationWithinLimits_sound
    {input : Certificate} {limits : ReconstructionLimits}
    {result : DerivationVerificationResult input}
    (_equation :
      input.reconstructDerivationWithinLimits limits = .ok result) :
    input.StructurallyWellFormed ∧
      input.conclusionFormulas? = some result.sequent ∧
      result.tree.infer? = some result.sequent ∧
      result.tree.desequentialize? = some result.output ∧
      result.output.check = true ∧
      result.output.ProofNetEquivalent input :=
  ⟨result.inputStructural, result.inputLabels, result.inferred,
    result.desequentialized, result.outputAccepted, result.equivalent⟩

/-- Bounded success implies acceptance by the exact reference semantics. -/
theorem reconstructDerivationWithinLimits_accepted
    {input : Certificate} {limits : ReconstructionLimits}
    {result : DerivationVerificationResult input}
    (_equation :
      input.reconstructDerivationWithinLimits limits = .ok result) :
    input.check = true := by
  rw [← result.equivalent.check_eq]
  exact result.outputAccepted

/-- Bounded success is always inside the unbounded reconstruction decision's
accepted set.  No converse is claimed for the heuristic bounded path. -/
theorem reconstructDerivationWithinLimits_implies_reconstructs
    {input : Certificate} {limits : ReconstructionLimits}
    {result : DerivationVerificationResult input}
    (equation :
      input.reconstructDerivationWithinLimits limits = .ok result) :
    input.reconstructsDerivation = true :=
  input.reconstructsDerivation_eq_true_iff_check.mpr
    (input.reconstructDerivationWithinLimits_accepted equation)

end Certificate

end ProofNetIR
