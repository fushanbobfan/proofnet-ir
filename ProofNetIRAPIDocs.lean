import ProofNetIR
import Lean

open Lean

namespace ProofNetIRAPIDocs

structure Section where
  title : String
  declarations : List Name

def sections : List Section := [
  {
    title := "Core certificate model"
    declarations := [
      `ProofNetIR.Formula,
      `ProofNetIR.Link,
      `ProofNetIR.Certificate,
      `ProofNetIR.Certificate.StructurallyWellFormed,
      `ProofNetIR.Certificate.DeclarativelyCorrect
    ]
  },
  {
    title := "Checking"
    declarations := [
      `ProofNetIR.Certificate.wellFormed,
      `ProofNetIR.Certificate.check,
      `ProofNetIR.Certificate.wellFormed_iff_structurallyWellFormed,
      `ProofNetIR.Certificate.check_iff_declarativelyCorrect
    ]
  },
  {
    title := "Finite graph semantics"
    declarations := [
      `ProofNetIR.Graph.Bounded,
      `ProofNetIR.Graph.Bounded.retainEdges,
      `ProofNetIR.Graph.Connected,
      `ProofNetIR.Graph.EdgeSimpleCycle,
      `ProofNetIR.Graph.DirectedEdge.ne_reverse,
      `ProofNetIR.Graph.EdgeSimpleCycle.eq_of_index_eq,
      `ProofNetIR.Graph.retainEdgesByMask_lookup_exists_original,
      `ProofNetIR.Graph.DirectedEdge.inflateRetained_exists,
      `ProofNetIR.Graph.EdgeWalk.inflateRetained,
      `ProofNetIR.Graph.EdgeSimpleCycle.inflateRetained,
      `ProofNetIR.Graph.DirectedEdge.reindex,
      `ProofNetIR.Graph.EdgeWalk.reindex,
      `ProofNetIR.Graph.EdgeSimpleCycle.reindex,
      `ProofNetIR.Graph.Acyclic,
      `ProofNetIR.Graph.acyclic_iff_not_nonempty_edgeSimpleCycle,
      `ProofNetIR.Graph.Acyclic.reindex,
      `ProofNetIR.Graph.acyclic_reindex_iff,
      `ProofNetIR.Graph.Acyclic.edges_add_one_le_vertexCount,
      `ProofNetIR.Graph.isEdgeSimpleCycleTraversal,
      `ProofNetIR.Graph.isEdgeSimpleCycleTraversal_sound,
      `ProofNetIR.Graph.isEdgeSimpleCycleTraversal_complete,
      `ProofNetIR.Graph.edgeSimpleCycleTraversalCandidates,
      `ProofNetIR.Graph.hasEdgeSimpleCycle,
      `ProofNetIR.Graph.hasEdgeSimpleCycle_eq_true_iff,
      `ProofNetIR.Graph.isAcyclic,
      `ProofNetIR.Graph.isAcyclic_eq_true_iff,
      `ProofNetIR.Graph.isTreeViaAcyclic,
      `ProofNetIR.Graph.isTreeViaAcyclic_eq_true_iff,
      `ProofNetIR.Graph.isTreeViaAcyclic_eq_isTree,
      `ProofNetIR.Graph.IsTree,
      `ProofNetIR.Graph.isTree_iff_isTree,
      `ProofNetIR.Graph.IsTree.acyclic,
      `ProofNetIR.Graph.Acyclic.edges_nodup,
      `ProofNetIR.Graph.connected_of_bounded_acyclic_edgeCount,
      `ProofNetIR.Graph.isTree_iff_bounded_connected_acyclic,
      `ProofNetIR.Certificate.CuspAcyclic,
      `ProofNetIR.Certificate.linkFullEdgeParTargets_some_origin,
      `ProofNetIR.Certificate.FullSwitchingSelection.mask_parPairSparse,
      `ProofNetIR.Certificate.FullSwitchingSelection.kept_parTarget_index_unique,
      `ProofNetIR.Certificate.StructurallyWellFormed.parTarget_producerCount,
      `ProofNetIR.Certificate.FullSwitchingSelection.kept_parTarget_index_unique_of_structural,
      `ProofNetIR.Certificate.FullSwitchingSelection.no_cusp_of_kept,
      `ProofNetIR.Certificate.fullSwitchingSelection_cycle_cuspFree,
      `ProofNetIR.Certificate.CuspAcyclic.occurrenceSwitching_acyclic,
      `ProofNetIR.Certificate.cuspAcyclic_iff_allOccurrenceSwitchingsAcyclic,
      `ProofNetIR.Certificate.StructurallyWellFormed.fullGraph_bounded,
      `ProofNetIR.Certificate.FullSwitchingSelection.retained_length_eq,
      `ProofNetIR.Certificate.AllOccurrenceSwitchingsConnected,
      `ProofNetIR.Certificate.referenceSwitchingMask,
      `ProofNetIR.Certificate.referenceSwitchingGraph,
      `ProofNetIR.Certificate.ReferenceSwitchingConnected,
      `ProofNetIR.Certificate.referenceFullSwitchingSelection,
      `ProofNetIR.Certificate.declarativelyCorrect_iff_structural_cuspAcyclic_allConnected,
      `ProofNetIR.Certificate.check_iff_structural_cuspAcyclic_allConnected,
      `ProofNetIR.Certificate.allOccurrenceSwitchingsConnected_of_reference,
      `ProofNetIR.Certificate.allOccurrenceSwitchingsConnected_iff_referenceSwitchingConnected,
      `ProofNetIR.Certificate.declarativelyCorrect_iff_structural_cuspAcyclic_referenceConnected,
      `ProofNetIR.Certificate.check_iff_structural_cuspAcyclic_referenceConnected,
      `ProofNetIR.Certificate.isCuspFreeTraversal,
      `ProofNetIR.Certificate.isCuspFreeTraversal_eq_true_iff,
      `ProofNetIR.Certificate.isCuspFreeCycleTraversal,
      `ProofNetIR.Certificate.isCuspFreeCycleTraversal_eq_true_iff,
      `ProofNetIR.Certificate.hasCuspFreeEdgeSimpleCycle,
      `ProofNetIR.Certificate.hasCuspFreeEdgeSimpleCycle_eq_true_iff,
      `ProofNetIR.Certificate.isCuspAcyclic,
      `ProofNetIR.Certificate.isCuspAcyclic_eq_true_iff,
      `ProofNetIR.Certificate.DeclarativelyCorrect.isCuspAcyclic,
      `ProofNetIR.Certificate.isCuspAcyclic_of_check,
      `ProofNetIR.Certificate.compactCheck,
      `ProofNetIR.Certificate.referenceSwitchingGraph_connected_eq_true_iff,
      `ProofNetIR.Certificate.compactCheck_eq_true_iff_check,
      `ProofNetIR.Certificate.compactCheck_eq_check,
      `ProofNetIR.Certificate.compactCheck_eq_true_iff_declarativelyCorrect
    ]
  },
  {
    title := "First-order derivations"
    declarations := [
      `ProofNetIR.CutFreeDerivation,
      `ProofNetIR.CutFreeDerivation.infer?,
      `ProofNetIR.CutFreeDerivation.build?_exists_of_infer?,
      `ProofNetIR.CutFreeDerivation.infer?_eq_some_iff_build?_conclusions,
      `ProofNetIR.CutFreeDerivation.build?_formulaConsistent,
      `ProofNetIR.CutFreeDerivation.build?_structurallyWellFormed,
      `ProofNetIR.CutFreeDerivation.build?_switchingCorrect,
      `ProofNetIR.CutFreeDerivation.build?_declarativelyCorrect,
      `ProofNetIR.CutFreeDerivation.build?_check,
      `ProofNetIR.CutFreeDerivation.build?_conclusionFormulas?,
      `ProofNetIR.CutFreeDerivation.desequentialize?,
      `ProofNetIR.CutFreeDerivation.desequentialize?_conclusionFormulas?,
      `ProofNetIR.CutFreeDerivation.desequentialize?_declarativelyCorrect,
      `ProofNetIR.CutFreeDerivation.desequentialize?_check,
      `ProofNetIR.CutFreeDerivation.desequentialize?_exists_with_labels_of_infer?,
      `ProofNetIR.CutFreeDerivation.desequentialize?_exists_checked_of_infer?,
      `ProofNetIR.CutFreeDerivation.CheckedCertificate,
      `ProofNetIR.CutFreeDerivation.desequentializeChecked?,
      `ProofNetIR.CutFreeDerivation.desequentializeChecked?_exists_of_infer?,
      `ProofNetIR.CutFreeDerivation.ElaboratedCertificate,
      `ProofNetIR.CutFreeDerivation.elaborate?,
      `ProofNetIR.CutFreeDerivation.elaborate?_exists_of_infer?
    ]
  },
  {
    title := "Equivalence and canonical keys"
    declarations := [
      `ProofNetIR.VertexRenaming,
      `ProofNetIR.Certificate.ReindexEquivalent,
      `ProofNetIR.Certificate.LinkPermutationEquivalent,
      `ProofNetIR.Certificate.ProofNetEquivalent,
      `ProofNetIR.Certificate.reindexEquivalent?,
      `ProofNetIR.Certificate.reindexEquivalent?_eq_true_iff_of_check,
      `ProofNetIR.Certificate.proofNetEquivalent?,
      `ProofNetIR.Certificate.proofNetEquivalent?_eq_true_iff,
      `ProofNetIR.Certificate.proofNetIdentityCandidateCount,
      `ProofNetIR.CutFreeDerivation.CheckedCertificate.sameProofNet?,
      `ProofNetIR.CutFreeDerivation.CheckedCertificate.sameProofNet?_eq_true_iff,
      `ProofNetIR.Certificate.proofNetCanonicalFamily,
      `ProofNetIR.Certificate.proofNetEquivalent_iff_canonicalFamily,
      `ProofNetIR.Certificate.proofNetEquivalent_iff_canonicalFamily_of_check,
      `ProofNetIR.Certificate.proofNetCanonicalStringCandidates,
      `ProofNetIR.Certificate.proofNetCanonicalFingerprint?,
      `ProofNetIR.Certificate.proofNetCanonicalFingerprint?_exists,
      `ProofNetIR.Certificate.proofNetCanonicalFingerprint?_mem,
      `ProofNetIR.Certificate.ProofNetEquivalent.proofNetCanonicalFingerprint?_eq,
      `ProofNetIR.Formula.structuralCode,
      `ProofNetIR.Formula.structuralCode_injective,
      `ProofNetIR.Link.structuralCode,
      `ProofNetIR.Link.structuralCode_injective,
      `ProofNetIR.Certificate.structuralCode,
      `ProofNetIR.Certificate.structuralCode_injective,
      `ProofNetIR.Certificate.proofNetCanonicalCodeCandidates,
      `ProofNetIR.Certificate.proofNetCanonicalCode?,
      `ProofNetIR.Certificate.proofNetCanonicalCode?_exists,
      `ProofNetIR.Certificate.proofNetCanonicalCode?_mem,
      `ProofNetIR.Certificate.ProofNetEquivalent.proofNetCanonicalCode?_eq,
      `ProofNetIR.Certificate.proofNetEquivalent_iff_canonicalCode,
      `ProofNetIR.Certificate.proofNetEquivalent_iff_canonicalCode_of_check,
      `ProofNetIR.CanonicalKey,
      `ProofNetIR.Certificate.proofNetCanonicalKey?,
      `ProofNetIR.Certificate.proofNetCanonicalKey?_exists,
      `ProofNetIR.Certificate.ProofNetEquivalent.proofNetCanonicalKey?_eq,
      `ProofNetIR.Certificate.proofNetEquivalent_iff_canonicalKey,
      `ProofNetIR.Certificate.proofNetEquivalent_iff_canonicalKey_of_check,
      `ProofNetIR.Certificate.proofNetEquivalent_iff_canonicalKeyWithinLimit,
      `ProofNetIR.Certificate.proofNetEquivalent_iff_canonicalKeyWithinLimit_of_check,
      `ProofNetIR.Certificate.intrinsicTraversalVertices,
      `ProofNetIR.Certificate.IntrinsicTraversalComplete,
      `ProofNetIR.Certificate.StructurallyWellFormed.intrinsicTraversalComplete,
      `ProofNetIR.Certificate.intrinsicOrderedLinks,
      `ProofNetIR.Certificate.StructurallyWellFormed.intrinsicOrderedLinks_perm,
      `ProofNetIR.Certificate.intrinsicCanonicalize,
      `ProofNetIR.Certificate.ProofNetEquivalent.intrinsicCanonicalize_eq,
      `ProofNetIR.Certificate.StructurallyWellFormed.intrinsicCanonicalize_proofNetEquivalent,
      `ProofNetIR.Certificate.proofNetEquivalent_iff_intrinsicCanonicalize_eq_of_check,
      `ProofNetIR.Certificate.intrinsicCanonicalCode,
      `ProofNetIR.Certificate.proofNetEquivalent_iff_intrinsicCanonicalCode_eq_of_check,
      `ProofNetIR.IntrinsicCanonicalKey,
      `ProofNetIR.Certificate.intrinsicCanonicalKey,
      `ProofNetIR.Certificate.proofNetEquivalent_iff_intrinsicCanonicalKey_eq_of_check,
      `ProofNetIR.Certificate.equivalenceCanonicalString
    ]
  },
  {
    title := "Sequentialization"
    declarations := [
      `ProofNetIR.SequentializationResult,
      `ProofNetIR.ExecutableSequentializationResult,
      `ProofNetIR.SequentializationError,
      `ProofNetIR.Certificate.sequentialization_of_check,
      `ProofNetIR.Certificate.sequentialize,
      `ProofNetIR.Certificate.sequentialize_complete,
      `ProofNetIR.DerivationVerificationResult,
      `ProofNetIR.Certificate.verifyDerivation?,
      `ProofNetIR.Certificate.verifyDerivation?_sound,
      `ProofNetIR.Certificate.verifyDerivation?_complete,
      `ProofNetIR.Certificate.verifiesDerivation,
      `ProofNetIR.Certificate.verifiesDerivation_eq_true_iff,
      `ProofNetIR.Certificate.reconstructDerivationWithFuel?,
      `ProofNetIR.Certificate.reconstructDerivationWithFuel?_complete,
      `ProofNetIR.Certificate.reconstructDerivation?,
      `ProofNetIR.Certificate.reconstructDerivation?_sound,
      `ProofNetIR.Certificate.reconstructDerivation?_accepted,
      `ProofNetIR.Certificate.reconstructDerivation?_complete,
      `ProofNetIR.Certificate.reconstructsDerivation,
      `ProofNetIR.Certificate.reconstructsDerivation_eq_true_iff_check,
      `ProofNetIR.Certificate.reconstructsDerivation_eq_check,
      `ProofNetIR.ReconstructionLimits,
      `ProofNetIR.ReconstructionLimits.qualified,
      `ProofNetIR.ReconstructionError,
      `ProofNetIR.ReconstructionError.message,
      `ProofNetIR.Certificate.reconstructDerivationWithinLimits,
      `ProofNetIR.Certificate.reconstructDerivationWithinLimits_sound,
      `ProofNetIR.Certificate.reconstructDerivationWithinLimits_accepted,
      `ProofNetIR.Certificate.reconstructDerivationWithinLimits_implies_reconstructs,
      `ProofNetIR.UnificationMarking,
      `ProofNetIR.UnificationMarking.setMark,
      `ProofNetIR.UnificationMarking.FreshExtension,
      `ProofNetIR.UnificationMarking.MergeExtension,
      `ProofNetIR.UnificationRuleKind,
      `ProofNetIR.UnificationStep,
      `ProofNetIR.UnificationStep.link_exists,
      `ProofNetIR.UnificationStep.marks_fired_conclusion,
      `ProofNetIR.UnificationStep.tokenCount_mono,
      `ProofNetIR.UnificationScanStats,
      `ProofNetIR.UnificationCandidateResult,
      `ProofNetIR.UnificationCandidateResult.linkVisitsBound,
      `ProofNetIR.UnificationVerificationResult,
      `ProofNetIR.UnificationWorklistStats,
      `ProofNetIR.UnificationWorklistStats.attemptBudget,
      `ProofNetIR.UnificationWorklistCandidateResult,
      `ProofNetIR.UnificationWorklistCandidateResult.linkAttemptsWithinBudget,
      `ProofNetIR.UnificationWorklistVerificationResult,
      `ProofNetIR.UnificationErrorCode,
      `ProofNetIR.UnificationError,
      `ProofNetIR.UnificationError.render,
      `ProofNetIR.Certificate.unificationDerivationCandidateWithStats,
      `ProofNetIR.Certificate.unificationDerivationCandidate,
      `ProofNetIR.Certificate.unificationWorklistDerivationCandidate,
      `ProofNetIR.Certificate.unificationDerivationCandidate?,
      `ProofNetIR.Certificate.unificationReconstructWithStats,
      `ProofNetIR.Certificate.unificationReconstruct,
      `ProofNetIR.Certificate.unificationReconstruct?,
      `ProofNetIR.Certificate.unificationWorklistReconstructWithStats,
      `ProofNetIR.Certificate.unificationWorklistReconstruct?,
      `ProofNetIR.Certificate.unificationWorklistFastCheck,
      `ProofNetIR.Certificate.unificationWorklistReconstruct?_accepted,
      `ProofNetIR.Certificate.unificationWorklistFastCheck_sound,
      `ProofNetIR.Certificate.unificationWorklistCheck,
      `ProofNetIR.Certificate.unificationWorklistCheck_eq_check,
      `ProofNetIR.Certificate.unificationWorklistCheck_eq_true_iff_check,
      `ProofNetIR.Certificate.unificationWorklistCheck_eq_true_iff_declarativelyCorrect,
      `ProofNetIR.Certificate.unificationFastCheck,
      `ProofNetIR.Certificate.unificationReconstruct_accepted,
      `ProofNetIR.Certificate.unificationReconstruct?_sound,
      `ProofNetIR.Certificate.unificationReconstruct?_accepted,
      `ProofNetIR.Certificate.unificationFastCheck_eq_true_iff,
      `ProofNetIR.Certificate.unificationFastCheck_sound,
      `ProofNetIR.Certificate.unificationCheck,
      `ProofNetIR.Certificate.unificationCheck_eq_check,
      `ProofNetIR.Certificate.unificationCheck_eq_true_iff_check,
      `ProofNetIR.Certificate.unificationCheck_eq_true_iff_declarativelyCorrect,
      `ProofNetIR.ExecutableSequentializationResult.kernelDerivation,
      `ProofNetIR.ExecutableSequentializationResult.proofNetEquivalent
    ]
  },
  {
    title := "Serialization and untrusted input"
    declarations := [
      `ProofNetIR.ParseError,
      `ProofNetIR.ParseResult,
      `ProofNetIR.Certificate.canonicalString,
      `ProofNetIR.Certificate.fromString,
      `ProofNetIR.Certificate.checkedFromString,
      `ProofNetIR.Certificate.migrateV02StringToV03,
      `ProofNetIR.CanonicalKey.wireVersion,
      `ProofNetIR.CanonicalKey.canonicalization,
      `ProofNetIR.CanonicalKey.maxTokens,
      `ProofNetIR.CanonicalKey.maxCharacters,
      `ProofNetIR.CanonicalKey.maxGenerationLinks,
      `ProofNetIR.CanonicalKey.WireAdmissible,
      `ProofNetIR.CanonicalKey.isWireAdmissible,
      `ProofNetIR.CanonicalKey.toJson,
      `ProofNetIR.CanonicalKey.toString,
      `ProofNetIR.CanonicalKey.fromJson,
      `ProofNetIR.CanonicalKey.fromString,
      `ProofNetIR.Certificate.proofNetCanonicalKeyWithinLimit?,
      `ProofNetIR.Certificate.proofNetCanonicalKeyJson?,
      `ProofNetIR.Certificate.proofNetCanonicalKeyString?,
      `ProofNetIR.Certificate.matchesCanonicalKey,
      `ProofNetIR.Certificate.proofNetEquivalent_of_matchesCanonicalKey,
      `ProofNetIR.Certificate.migrateV03StringToCanonicalKey,
      `ProofNetIR.IntrinsicCanonicalKey.wireVersion,
      `ProofNetIR.IntrinsicCanonicalKey.canonicalization,
      `ProofNetIR.IntrinsicCanonicalKey.maxTokens,
      `ProofNetIR.IntrinsicCanonicalKey.maxCharacters,
      `ProofNetIR.IntrinsicCanonicalKey.WireAdmissible,
      `ProofNetIR.IntrinsicCanonicalKey.isWireAdmissible,
      `ProofNetIR.IntrinsicCanonicalKey.toJson,
      `ProofNetIR.IntrinsicCanonicalKey.toString,
      `ProofNetIR.IntrinsicCanonicalKey.fromJson,
      `ProofNetIR.IntrinsicCanonicalKey.fromString,
      `ProofNetIR.Certificate.intrinsicCanonicalKeyJson?,
      `ProofNetIR.Certificate.intrinsicCanonicalKeyString?,
      `ProofNetIR.Certificate.matchesIntrinsicCanonicalKey,
      `ProofNetIR.Certificate.proofNetEquivalent_of_matchesIntrinsicCanonicalKey,
      `ProofNetIR.Certificate.migrateV03StringToIntrinsicCanonicalKey
    ]
  },
  {
    title := "Persistent and linear LeanProp bridge"
    declarations := [
      `ProofNetIR.LeanProp.Assumptions,
      `ProofNetIR.LeanProp.Assumptions.split_append,
      `ProofNetIR.LeanProp.Assumptions.permute_symm,
      `ProofNetIR.LeanProp.Assumptions.permute_symm_right,
      `ProofNetIR.LeanProp.ContextPermutation,
      `ProofNetIR.LeanProp.ContextPermutation.toListPerm,
      `ProofNetIR.LeanProp.ContextPermutation.symm_symm,
      `ProofNetIR.LeanProp.ContextPermutation.nonempty_iff_listPerm,
      `ProofNetIR.LeanProp.Derivation,
      `ProofNetIR.LeanProp.Derivation.persistentExchange_nonempty_of_listPerm,
      `ProofNetIR.LeanProp.Derivation.linearExchange_nonempty_of_listPerm,
      `ProofNetIR.LeanProp.Derivation.linearAxiomCount,
      `ProofNetIR.LeanProp.Derivation.linearAxiomCount_eq_length,
      `ProofNetIR.LeanProp.Derivation.toProof,
      `ProofNetIR.LeanProp.Derivation.close,
      `ProofNetIR.LeanProp.Derivation.persistentStructuralSize,
      `ProofNetIR.LeanProp.Derivation.PersistentStructurallyReduced,
      `ProofNetIR.LeanProp.Derivation.normalizePersistentStructural,
      `ProofNetIR.LeanProp.Derivation.normalizePersistentStructural_reduced,
      `ProofNetIR.LeanProp.Derivation.normalizePersistentStructural_eq_self_of_reduced,
      `ProofNetIR.LeanProp.Derivation.normalizePersistentStructural_idempotent,
      `ProofNetIR.LeanProp.Derivation.normalizePersistentStructural_size_le,
      `ProofNetIR.LeanProp.Derivation.normalizePersistentStructural_contract_weaken,
      `ProofNetIR.LeanProp.Derivation.normalizePersistentStructural_linearAxiomCount,
      `ProofNetIR.LeanProp.Derivation.normalizePersistentStructural_toProof,
      `ProofNetIR.LeanProp.Schema.Formula,
      `ProofNetIR.LeanProp.Schema.Formula.evaluate,
      `ProofNetIR.LeanProp.Schema.Derivation,
      `ProofNetIR.LeanProp.Schema.Derivation.instantiate,
      `ProofNetIR.LeanProp.Schema.PackedDerivation,
      `ProofNetIR.LeanProp.Schema.PackedDerivation.sound,
      `ProofNetIR.LeanProp.Schema.Raw.Permutation,
      `ProofNetIR.LeanProp.Schema.Raw.Permutation.boundary?,
      `ProofNetIR.LeanProp.Schema.Raw.Permutation.boundary?_ofIndexed,
      `ProofNetIR.LeanProp.Schema.Raw.ElaboratedPermutation,
      `ProofNetIR.LeanProp.Schema.Raw.Permutation.elaborate?,
      `ProofNetIR.LeanProp.Schema.Raw.Permutation.boundary?_eq_elaborate?,
      `ProofNetIR.LeanProp.Schema.Raw.Derivation,
      `ProofNetIR.LeanProp.Schema.Raw.Sequent,
      `ProofNetIR.LeanProp.Schema.Raw.ErrorCode,
      `ProofNetIR.LeanProp.Schema.Raw.Error,
      `ProofNetIR.LeanProp.Schema.Raw.Error.render,
      `ProofNetIR.LeanProp.Schema.Raw.Derivation.infer?,
      `ProofNetIR.LeanProp.Schema.Raw.Derivation.ofIndexed,
      `ProofNetIR.LeanProp.Schema.Raw.Derivation.infer?_ofIndexed,
      `ProofNetIR.LeanProp.Schema.Raw.ElaboratedDerivation,
      `ProofNetIR.LeanProp.Schema.Raw.ElaboratedDerivation.sequent,
      `ProofNetIR.LeanProp.Schema.Raw.ElaboratedDerivation.toPacked,
      `ProofNetIR.LeanProp.Schema.Raw.Derivation.elaborate?,
      `ProofNetIR.LeanProp.Schema.Raw.Derivation.inferAt_eq_elaborateAt,
      `ProofNetIR.LeanProp.Schema.Raw.Derivation.elaborate?_complete,
      `ProofNetIR.LeanProp.Schema.Raw.InputError,
      `ProofNetIR.LeanProp.Schema.Raw.InputError.render,
      `ProofNetIR.LeanProp.Schema.Raw.CheckedDerivation,
      `ProofNetIR.LeanProp.Schema.Raw.CheckedDerivation.sequent,
      `ProofNetIR.LeanProp.Schema.Raw.CheckedDerivation.toPacked,
      `ProofNetIR.LeanProp.Schema.Raw.CheckedDerivation.inferred,
      `ProofNetIR.LeanProp.Schema.Raw.CheckedDerivation.sound,
      `ProofNetIR.LeanProp.Schema.Raw.FormulaWire.toJson,
      `ProofNetIR.LeanProp.Schema.Raw.FormulaWire.fromJsonAt,
      `ProofNetIR.LeanProp.Schema.Raw.Permutation.toJson,
      `ProofNetIR.LeanProp.Schema.Raw.Permutation.fromJsonAt,
      `ProofNetIR.LeanProp.Schema.Raw.Derivation.toJson,
      `ProofNetIR.LeanProp.Schema.Raw.Derivation.fromJsonAt,
      `ProofNetIR.LeanProp.Schema.Raw.Derivation.canonicalJson,
      `ProofNetIR.LeanProp.Schema.Raw.Derivation.canonicalString,
      `ProofNetIR.LeanProp.Schema.Raw.Derivation.fromJson,
      `ProofNetIR.LeanProp.Schema.Raw.Derivation.fromString,
      `ProofNetIR.LeanProp.Schema.Raw.Derivation.check,
      `ProofNetIR.LeanProp.Schema.Raw.Derivation.checkedFromJson,
      `ProofNetIR.LeanProp.Schema.Raw.Derivation.checkedFromString,
      `ProofNetIR.LeanProp.Schema.Corpus.generated
    ]
  }
]

def normalizeNewlines (value : String) : String :=
  value.replace "\r\n" "\n"

def declarationKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque definition"
  | .quotInfo _ => "quotient primitive"
  | .inductInfo _ => "inductive type"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

def renderDeclaration (environment : Environment) (name : Name) : IO String := do
  let some info := environment.find? name
    | throw <| IO.userError s!"public API declaration not found: {name}"
  if info.isUnsafe then
    throw <| IO.userError s!"unsafe declaration entered public API manifest: {name}"
  let typeFormat ← PrettyPrinter.ppExprLegacy environment {} {} {} info.type
  let some doc ← findSimpleDocString? environment name (includeBuiltin := false)
    | throw <| IO.userError s!"public API declaration lacks a docstring: {name}"
  return s!"### `{name}`\n\nKind: {declarationKind info}.\n\n{doc.trimAscii.toString}\n\n```lean\n{name} : {typeFormat}\n```\n\n"

def renderSection (environment : Environment) (apiSection : Section) : IO String := do
  let declarations ← apiSection.declarations.mapM (renderDeclaration environment)
  return s!"## {apiSection.title}\n\n{String.join declarations}"

def render (environment : Environment) : IO String := do
  let renderedSections ← sections.mapM (renderSection environment)
  return normalizeNewlines <|
    "# ProofNet-IR public API reference\n\n" ++
    "<!-- Generated by ProofNetIRAPIDocs.lean. Do not edit by hand. -->\n\n" ++
    "This reference is generated from the kernel-loaded Lean environment. " ++
    "The curated manifest records the supported public boundary; generation " ++
    "fails if a listed declaration disappears or becomes unsafe. Regenerate " ++
    "with `lake exe proofnet_ir_api_docs` and verify drift with " ++
    "`lake exe proofnet_ir_api_docs --check`.\n\n" ++
    String.join renderedSections

end ProofNetIRAPIDocs

unsafe def main (args : List String) : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let environment ← Lean.importModules #[{ module := `ProofNetIR }] {}
    (loadExts := true)
  let generated ← ProofNetIRAPIDocs.render environment
  let output : System.FilePath := "docs" / "api-reference.md"
  if args == ["--check"] then
    let existing ← IO.FS.readFile output
    unless ProofNetIRAPIDocs.normalizeNewlines existing == generated do
      throw <| IO.userError
        "docs/api-reference.md is stale; run `lake exe proofnet_ir_api_docs`"
    IO.println "ProofNet-IR generated API reference is current"
  else if args.isEmpty then
    IO.FS.writeFile output generated
    IO.println s!"generated {output}"
  else
    throw <| IO.userError
      "usage: lake exe proofnet_ir_api_docs [--check]"
