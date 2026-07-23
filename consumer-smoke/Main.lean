import Tutorial

open ProofNetIR

def consumedCertificate : Certificate :=
  canonicalCertificate "consumer-p" "consumer-q"

def reorderedConsumedCertificate : Certificate :=
  { consumedCertificate with links := consumedCertificate.links.reverse }

def consumerRightNestedFormula : Nat → Formula
  | 0 => .atom "consumer-key-base" true
  | depth + 1 =>
      .tensor (consumerRightNestedFormula depth)
        (.atom s!"consumer-key-right-{depth}" true)

def largeConsumedCertificate : Certificate :=
  identityCertificate (consumerRightNestedFormula 8)

def consumedTreeGraph : Graph where
  vertexCount := 3
  edges := [
    { first := 0, second := 1 },
    { first := 1, second := 2 }
  ]

def consumedTreeSwap : VertexRenaming consumedTreeGraph.vertexCount :=
  VertexRenaming.swap consumedTreeGraph.vertexCount 0 2
    (by decide) (by decide)

example : consumedCertificate.check = true := by native_decide

example : consumedCertificate.compactCheck = true := by native_decide

example : consumedCertificate.compactCheck = consumedCertificate.check :=
  consumedCertificate.compactCheck_eq_check

example : consumedCertificate.DeclarativelyCorrect :=
  consumedCertificate.check_iff_declarativelyCorrect.mp (by native_decide)

example : consumedTreeGraph.Acyclic :=
  (consumedTreeGraph.isTree_sound (by native_decide)).acyclic

example : consumedTreeGraph.isAcyclic = true := by native_decide

example : consumedTreeGraph.isAcyclic = true ↔
    consumedTreeGraph.Acyclic :=
  consumedTreeGraph.isAcyclic_eq_true_iff

example : consumedTreeGraph.isTreeViaAcyclic =
    consumedTreeGraph.isTree :=
  consumedTreeGraph.isTreeViaAcyclic_eq_isTree

example : consumedTreeGraph.IsTree ↔
    consumedTreeGraph.Bounded ∧ consumedTreeGraph.Connected ∧
      consumedTreeGraph.Acyclic :=
  consumedTreeGraph.isTree_iff_bounded_connected_acyclic

example : (consumedTreeGraph.reindex consumedTreeSwap).Acyclic :=
  ((consumedTreeGraph.isTree_sound (by native_decide)).acyclic).reindex
    consumedTreeSwap

example : (consumedTreeGraph.reindex consumedTreeSwap).Acyclic ↔
    consumedTreeGraph.Acyclic :=
  consumedTreeGraph.acyclic_reindex_iff consumedTreeSwap

def consumedTree : CutFreeDerivation :=
  CutFreeDerivation.generate 42 2

def consumedRuleTree : CutFreeDerivation :=
  .par 1 1
    (.tensor 0 0
      (.axiom "consumer-p" true)
      (.axiom "consumer-q" true))

example : consumedTree.elaborate?.isSome = true := by native_decide

example :
    consumedCertificate.verifiesDerivation consumedRuleTree = true := by
  native_decide

example : consumedCertificate.reconstructsDerivation = true := by
  native_decide

example : consumedCertificate.unificationFastCheck = true := by
  native_decide

example : consumedCertificate.unificationReconstruct.isOk = true := by
  native_decide

def consumedUnificationWithStats :=
  consumedCertificate.unificationReconstructWithStats

example : consumedUnificationWithStats.isOk = true := by
  native_decide

example : consumedCertificate.unificationCheck = true := by
  native_decide

example :
    consumedCertificate.unificationCheck = consumedCertificate.check :=
  consumedCertificate.unificationCheck_eq_check

def consumedBoundedReconstruction :=
  consumedCertificate.reconstructDerivationWithinLimits

example : consumedBoundedReconstruction.isOk = true := by
  native_decide

example :
    consumedCertificate.reconstructsDerivation =
      consumedCertificate.check :=
  consumedCertificate.reconstructsDerivation_eq_check

example : ∃ result : DerivationVerificationResult consumedCertificate,
    consumedCertificate.verifyDerivation? consumedRuleTree = some result := by
  apply Certificate.verifiesDerivation_eq_true_iff.mp
  native_decide

def consumedSequentialization :
    Except SequentializationError
      (ExecutableSequentializationResult consumedCertificate) :=
  consumedCertificate.sequentialize

example : consumedSequentialization.isOk = true := by native_decide

example : ∃ result : ExecutableSequentializationResult consumedCertificate,
    consumedCertificate.sequentialize = .ok result :=
  consumedCertificate.sequentialize_complete (by native_decide)

example : Certificate.proofNetEquivalent? consumedCertificate
    reorderedConsumedCertificate = true := by native_decide

example : consumedCertificate.ProofNetEquivalent reorderedConsumedCertificate := by
  apply (Certificate.proofNetEquivalent?_eq_true_iff
    (consumedCertificate.check_sound_declarative (by native_decide)).1).mp
  native_decide

example :
    consumedCertificate.intrinsicCanonicalKey =
      reorderedConsumedCertificate.intrinsicCanonicalKey := by
  apply (Certificate.proofNetEquivalent_iff_intrinsicCanonicalKey_eq_of_check
    (left := consumedCertificate) (right := reorderedConsumedCertificate)
    (by native_decide) (by native_decide)).mp
  apply (Certificate.proofNetEquivalent?_eq_true_iff
    (consumedCertificate.check_sound_declarative (by native_decide)).1).mp
  native_decide

example :
    largeConsumedCertificate.links.length >
      CanonicalKey.maxGenerationLinks := by
  native_decide

example : largeConsumedCertificate.proofNetCanonicalKeyString? = none := by
  native_decide

example : largeConsumedCertificate.intrinsicCanonicalKeyString?.isSome = true := by
  native_decide

example : ∀ candidate,
    candidate ∈ consumedCertificate.proofNetCanonicalFamily ↔
      candidate ∈ reorderedConsumedCertificate.proofNetCanonicalFamily :=
  (Certificate.proofNetEquivalent_iff_canonicalFamily_of_check
    (left := consumedCertificate) (right := reorderedConsumedCertificate)
    (by native_decide) (by native_decide)).mp (by
      apply (Certificate.proofNetEquivalent?_eq_true_iff
        (consumedCertificate.check_sound_declarative
          (by native_decide)).1).mp
      native_decide)

example (result : ExecutableSequentializationResult consumedCertificate) :
    result.output.ProofNetEquivalent consumedCertificate :=
  result.proofNetEquivalent

example :
    (Certificate.checkedFromString consumedCertificate.canonicalString).isOk =
      true := by
  native_decide

example :
    (Certificate.checkedFromString
      consumedCertificate.equivalenceCanonicalString).isOk = true := by
  native_decide

example :
    (Certificate.migrateV02StringToV03
      consumedCertificate.canonicalString).isOk = true := by
  native_decide

def main : IO Unit := do
  if consumedTreeGraph.isTree &&
      consumedCertificate.check && consumedCertificate.compactCheck &&
      consumedTree.elaborate?.isSome &&
      consumedCertificate.verifiesDerivation consumedRuleTree &&
      consumedCertificate.reconstructsDerivation &&
      consumedCertificate.unificationFastCheck &&
      consumedCertificate.unificationReconstruct.isOk &&
      consumedUnificationWithStats.isOk &&
      consumedCertificate.unificationCheck &&
      consumedBoundedReconstruction.isOk &&
      consumedSequentialization.isOk &&
      Certificate.proofNetEquivalent? consumedCertificate
        reorderedConsumedCertificate &&
      largeConsumedCertificate.intrinsicCanonicalKeyString?.isSome &&
      (Certificate.checkedFromString
        consumedCertificate.canonicalString).isOk &&
      (Certificate.checkedFromString
        consumedCertificate.equivalenceCanonicalString).isOk &&
      ProofNetIRTutorialSmoke.RawSchema.valid.infer?.isOk &&
      !ProofNetIRTutorialSmoke.RawSchema.invalid.infer?.isOk &&
      (LeanProp.Schema.Raw.Derivation.checkedFromString
        ProofNetIRTutorialSmoke.RawSchema.valid.canonicalString).isOk &&
      !(LeanProp.Schema.Raw.Derivation.checkedFromString
        ProofNetIRTutorialSmoke.RawSchema.invalid.canonicalString).isOk then
    IO.println "ProofNetIR downstream consumer smoke test passed"
  else
    throw <| IO.userError "ProofNetIR downstream consumer smoke test failed"
