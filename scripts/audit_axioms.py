#!/usr/bin/env python3
"""Fail if the public theorem boundary silently gains trust dependencies."""

from __future__ import annotations

import re
import shutil
import subprocess
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
AUDIT_FILE = ROOT / "ProofNetIRAxiomAudit.lean"
EXPECTED_CLASSICAL_THEOREMS = {
    "ProofNetIR.Certificate.check_iff_declarativelyCorrect",
    "ProofNetIR.Graph.IsTree.acyclic",
    "ProofNetIR.Graph.Acyclic.edges_add_one_le_vertexCount",
    "ProofNetIR.Graph.connected_of_bounded_acyclic_edgeCount",
    "ProofNetIR.Graph.isTree_iff_bounded_connected_acyclic",
    "ProofNetIR.Graph.hasEdgeSimpleCycle_eq_true_iff",
    "ProofNetIR.Graph.isAcyclic_eq_true_iff",
    "ProofNetIR.Graph.isTreeViaAcyclic_eq_true_iff",
    "ProofNetIR.Graph.isTreeViaAcyclic_eq_isTree",
    "ProofNetIR.Certificate.hasCuspFreeEdgeSimpleCycle_eq_true_iff",
    "ProofNetIR.Certificate.isCuspAcyclic_eq_true_iff",
    "ProofNetIR.Certificate.DeclarativelyCorrect.isCuspAcyclic",
    "ProofNetIR.Certificate.isCuspAcyclic_of_check",
    "ProofNetIR.Certificate.CuspAcyclic.occurrenceSwitching_acyclic",
    "ProofNetIR.Certificate.cuspAcyclic_iff_allOccurrenceSwitchingsAcyclic",
    "ProofNetIR.Certificate.declarativelyCorrect_iff_structural_cuspAcyclic_allConnected",
    "ProofNetIR.Certificate.check_iff_structural_cuspAcyclic_allConnected",
    "ProofNetIR.Certificate.allOccurrenceSwitchingsConnected_of_reference",
    "ProofNetIR.Certificate.check_iff_structural_cuspAcyclic_referenceConnected",
    "ProofNetIR.Certificate.compactCheck_eq_check",
    "ProofNetIR.CutFreeDerivation.infer?_eq_some_iff_build?_conclusions",
    "ProofNetIR.CutFreeDerivation.build?_structurallyWellFormed",
    "ProofNetIR.CutFreeDerivation.build?_switchingCorrect",
    "ProofNetIR.CutFreeDerivation.build?_declarativelyCorrect",
    "ProofNetIR.CutFreeDerivation.build?_check",
    "ProofNetIR.CutFreeDerivation.desequentialize?_conclusionFormulas?",
    "ProofNetIR.CutFreeDerivation.desequentialize?_declarativelyCorrect",
    "ProofNetIR.CutFreeDerivation.desequentialize?_check",
    "ProofNetIR.CutFreeDerivation.desequentialize?_exists_with_labels_of_infer?",
    "ProofNetIR.CutFreeDerivation.desequentialize?_exists_checked_of_infer?",
    "ProofNetIR.CutFreeDerivation.desequentializeChecked?_exists_of_infer?",
    "ProofNetIR.CutFreeDerivation.elaborate?_exists_of_infer?",
    "ProofNetIR.Certificate.sequentialization_of_check",
    "ProofNetIR.Certificate.generallySequentializable",
    "ProofNetIR.Certificate.reindexEquivalent?_eq_true_iff_of_check",
    "ProofNetIR.Certificate.matchingFormulaOrders_complete",
    "ProofNetIR.Certificate.localIdentityCompatible_inverse",
    "ProofNetIR.Certificate.directProofNetEquivalentWitness?_complete",
    "ProofNetIR.Certificate.proofNetEquivalent?_eq_true_iff",
    "ProofNetIR.CutFreeDerivation.CheckedCertificate.sameProofNet?_eq_true_iff",
    "ProofNetIR.Certificate.proofNetEquivalent_iff_canonicalFamily_of_check",
    "ProofNetIR.Certificate.proofNetCanonicalFingerprint?_exists",
    "ProofNetIR.Certificate.ProofNetEquivalent.proofNetCanonicalFingerprint?_eq",
    "ProofNetIR.Certificate.structuralCode_injective",
    "ProofNetIR.Certificate.proofNetCanonicalCode?_exists",
    "ProofNetIR.Certificate.ProofNetEquivalent.proofNetCanonicalCode?_eq",
    "ProofNetIR.Certificate.proofNetEquivalent_iff_canonicalCode_of_check",
    "ProofNetIR.Certificate.proofNetCanonicalKey?_exists",
    "ProofNetIR.Certificate.ProofNetEquivalent.proofNetCanonicalKey?_eq",
    "ProofNetIR.Certificate.proofNetEquivalent_iff_canonicalKey_of_check",
    "ProofNetIR.Certificate.proofNetEquivalent_iff_canonicalKeyWithinLimit",
    "ProofNetIR.Certificate.proofNetEquivalent_iff_canonicalKeyWithinLimit_of_check",
    "ProofNetIR.Certificate.proofNetEquivalent_of_matchesCanonicalKey",
    "ProofNetIR.Certificate.StructurallyWellFormed.intrinsicTraversalComplete",
    "ProofNetIR.Certificate.StructurallyWellFormed.intrinsicOrderedLinks_perm",
    "ProofNetIR.Certificate.ProofNetEquivalent.intrinsicCanonicalize_eq",
    "ProofNetIR.Certificate.StructurallyWellFormed.intrinsicCanonicalize_proofNetEquivalent",
    "ProofNetIR.Certificate.proofNetEquivalent_iff_intrinsicCanonicalize_eq_of_check",
    "ProofNetIR.Certificate.proofNetEquivalent_iff_intrinsicCanonicalCode_eq_of_check",
    "ProofNetIR.Certificate.proofNetEquivalent_iff_intrinsicCanonicalKey_eq_of_check",
    "ProofNetIR.Certificate.proofNetEquivalent_of_matchesIntrinsicCanonicalKey",
    "ProofNetIR.Certificate.sequentialize_complete",
    "ProofNetIR.Certificate.verifyDerivation?_sound",
    "ProofNetIR.Certificate.verifyDerivation?_complete",
    "ProofNetIR.Certificate.reconstructDerivationWithFuel?_complete",
    "ProofNetIR.Certificate.reconstructDerivation?_sound",
    "ProofNetIR.Certificate.reconstructDerivation?_accepted",
    "ProofNetIR.Certificate.reconstructDerivation?_complete",
    "ProofNetIR.Certificate.reconstructsDerivation_eq_true_iff_check",
    "ProofNetIR.Certificate.reconstructsDerivation_eq_check",
    "ProofNetIR.Certificate.reconstructDerivationWithinLimits_sound",
    "ProofNetIR.Certificate.reconstructDerivationWithinLimits_accepted",
    "ProofNetIR.Certificate.reconstructDerivationWithinLimits_implies_reconstructs",
    "ProofNetIR.Certificate.unificationReconstruct_accepted",
    "ProofNetIR.Certificate.unificationReconstruct?_sound",
    "ProofNetIR.Certificate.unificationReconstruct?_accepted",
    "ProofNetIR.Certificate.unificationWorklistReconstruct?_accepted",
    "ProofNetIR.Certificate.unificationWorklistFastCheck_sound",
    "ProofNetIR.Certificate.unificationWorklistCheck_eq_check",
    "ProofNetIR.Certificate.unificationWorklistCheck_eq_true_iff_check",
    "ProofNetIR.Certificate.unificationWorklistCheck_eq_true_iff_declarativelyCorrect",
    "ProofNetIR.Certificate.unificationFastCheck_eq_true_iff",
    "ProofNetIR.Certificate.unificationFastCheck_sound",
    "ProofNetIR.Certificate.unificationCheck_eq_check",
    "ProofNetIR.Certificate.unificationCheck_eq_true_iff_check",
    "ProofNetIR.Certificate.unificationCheck_eq_true_iff_declarativelyCorrect",
    "ProofNetIR.ExecutableSequentializationResult.kernelDerivation",
    "ProofNetIR.ExecutableSequentializationResult.proofNetEquivalent",
    "ProofNetIR.UnificationState.OrderedParents.startMarking_representative_eq",
    "ProofNetIR.UnificationState.OrderedParents.startMarking_sameThread_iff",
    "ProofNetIR.UnificationState.Abstractable.startMarking_ordered",
    "ProofNetIR.UnificationState.OrderedParents.toMarking_isFreshToken",
    "ProofNetIR.UnificationState.startMarking_toMarking_mark_ordered",
    "ProofNetIR.UnificationState.startMarking_startStep_ordered",
    "ProofNetIR.SequentialUnification.StructurallyWellFormed.sourceIndex_lookup_eq_singleton",
    "ProofNetIR.SequentialUnification.mem_sourceIndex_origin",
    "ProofNetIR.SequentialUnification.sourceIndex_sound",
    "ProofNetIR.SequentialUnification.nextAxiomWithFuel?_exists_of_structural_clearThrough",
    "ProofNetIR.SequentialUnification.nextAxiomWithFuel?_exists_of_structural_carrierClear",
    "ProofNetIR.SequentialUnification.DynamicStartResult.refinesStart",
    "ProofNetIR.Certificate.UnificationComponent.axiom?_formulaConsistent",
    "ProofNetIR.Certificate.reserveAxiomAt?_orderedParents",
    "ProofNetIR.Certificate.reserveAxiomAt?_abstractable",
    "ProofNetIR.Certificate.reserveAxiomAt?_componentsFormulaConsistent",
    "ProofNetIR.Certificate.reserveAxiomAt?_old_representative",
    "ProofNetIR.Certificate.reserveAxiomAt?_fresh_representative",
    "ProofNetIR.SequentialSchedulerBridge.init_reserve_carrier_realizesSigma",
    "ProofNetIR.SequentialSchedulerBridge.init_reserve_route_exact",
    "ProofNetIR.SequentialSchedulerBridge.init_reserve_route_fields",
    "ProofNetIR.SequentialSchedulerBridge.empty_reservationInvariant",
    "ProofNetIR.SequentialSchedulerBridge.initializeReservation?_some_iff",
    "ProofNetIR.SequentialSchedulerBridge.reserveNewAxiom?_some_iff",
    "ProofNetIR.SequentialSchedulerBridge.InitialReservationStep.route",
    "ProofNetIR.SequentialSchedulerBridge.InitialReservationStep.linkIndex_ne_next",
    "ProofNetIR.SequentialSchedulerBridge.NewReservationStep.route",
    "ProofNetIR.SequentialSchedulerBridge.NewReservationStep.linkIndex_ne",
    "ProofNetIR.SequentialSchedulerBridge.InitialReservationStep.reservationInvariant",
    "ProofNetIR.SequentialSchedulerBridge.new_reserve_carrier_realizesSigma",
    "ProofNetIR.SequentialSchedulerBridge.new_reserve_route_exact",
    "ProofNetIR.SequentialSchedulerBridge.new_reserve_route_fields",
    "ProofNetIR.SequentialSchedulerBridge.NewReservationStep.reservationInvariant",
    "ProofNetIR.SequentialSchedulerState.SequentialStackState.AllWaitingUndefined.lookup",
    "ProofNetIR.SequentialSchedulerState.SequentialStackState.initEnqueue?_exact",
    "ProofNetIR.SequentialSchedulerState.SequentialStackState.initEnqueue?_operationalWaitingDomain",
    "ProofNetIR.ConsumerIndex.build_members_eq",
    "ProofNetIR.ConsumerIndex.build_singleton",
    "ProofNetIR.ConsumerIndex.build_uniqueConsumer?_eq_some",
    "ProofNetIR.Certificate.worklistConsumers_members_eq",
    "ProofNetIR.UnificationState.markReadyRaw?_componentsFormulaConsistent",
    "ProofNetIR.SequentialSchedulerBridge.popReadyMark_markReadyRaw_reservationInvariant",
    "ProofNetIR.SequentialFigure7.new?_some_iff",
    "ProofNetIR.SequentialFigure7.NewStep.tensorValid",
    "ProofNetIR.SequentialFigure7.NewStep.mate_unmarked",
    "ProofNetIR.SequentialFigure7.NewStep.route",
    "ProofNetIR.SequentialFigure7.NewStep.markedMiddle_reservationInvariant",
    "ProofNetIR.SequentialFigure7.NewStep.reservationInvariant",
    "ProofNetIR.SequentialFigure7.new?_reservationInvariant",
    "ProofNetIR.SequentialFigure7.initial_output_tags_eq",
    "ProofNetIR.SequentialFigure7.initial_tagsExtend",
    "ProofNetIR.SequentialFigure7.NewStep.output_tags_eq",
    "ProofNetIR.SequentialFigure7.NewStep.tagsExtend",
    "ProofNetIR.SequentialFigure7.InitNewHistory.reservationInvariant",
    "ProofNetIR.SequentialFigure7.InitNewHistory.tagged_iff_touched",
    "ProofNetIR.SequentialFigure7.InitNewHistory.touched_disjoint_next",
    "ProofNetIR.SequentialFigure7.InitNewHistory.mem_linkIndices_witness",
    "ProofNetIR.SequentialFigure7.InitNewHistory.linkIndices_nodup",
    "ProofNetIR.SequentialFigure7.InitNewHistory.length_eq_nextAge",
    "ProofNetIR.SequentialFigure7.InitNewHistory.length_eq_startedAxioms",
    "ProofNetIR.SequentialFigure7.reachable_empty",
    "ProofNetIR.SequentialFigure7.reachable_of_initializeReservation?_eq_some",
    "ProofNetIR.SequentialFigure7.ReachableByImplementedInitNew.new",
    "ProofNetIR.UnificationState.mergeConclusion_toMarking_mark",
    "ProofNetIR.UnificationState.OrderedParents.setParent_representative",
    "ProofNetIR.UnificationState.OrderedParents.setParent_sameThread",
    "ProofNetIR.UnificationState.OrderedParents.setParent_sameThread_all",
    "ProofNetIR.UnificationState.unifyTokens?_refines",
    "ProofNetIR.UnificationState.ComponentsFormulaConsistent.componentAt",
    "ProofNetIR.UnificationMarking.referencePath_has_first_marked_to_unmarked_boundary",
    "ProofNetIR.UnificationMarking.referencePath_has_last_unmarked_to_marked_boundary",
}
EXPECTED_AXIOM_FREE_THEOREMS = {
    "ProofNetIR.LeanProp.Derivation.toProof",
    "ProofNetIR.LeanProp.ContextPermutation.nonempty_iff_listPerm",
    "ProofNetIR.LeanProp.Derivation.persistentExchange_nonempty_of_listPerm",
    "ProofNetIR.LeanProp.Derivation.linearExchange_nonempty_of_listPerm",
    "ProofNetIR.UnificationCandidateResult.linkVisitsBound",
    "ProofNetIR.UnificationWorklistCandidateResult.linkAttemptsWithinBudget",
    "ProofNetIR.UnificationStep.link_exists",
    "ProofNetIR.UnificationStep.tokenCount_mono",
    "ProofNetIR.UnificationState.toMarking_tokenCount",
    "ProofNetIR.UnificationState.toMarking_mark",
    "ProofNetIR.UnificationState.toMarking_sameThread",
    "ProofNetIR.UnificationState.Abstractable.tokenAt?_bound",
    "ProofNetIR.UnificationState.tokenAt?_some_witness",
    "ProofNetIR.UnificationState.Abstractable.tokenAt?_sameThread_witness",
    "ProofNetIR.UnificationState.Abstractable.tokenAt?_root",
    "ProofNetIR.UnificationMarking.mergeExtension_equivalence",
    "ProofNetIR.UnificationExecution.trans",
    "ProofNetIR.UnificationState.ObservationEquivalent.identityParents",
    "ProofNetIR.SequentialSchedulerState.WaitingCell.undefined_ne_initialized_empty",
    "ProofNetIR.SequentialSchedulerState.sigmaBoundary_unique_of_greatest",
    "ProofNetIR.SequentialSchedulerBridge.RealizesSigma.rawAgeAt?_eq_assignedToken?",
    "ProofNetIR.SequentialFigure7.TagsExtend.refl",
    "ProofNetIR.SequentialFigure7.TagsExtend.trans",
}
EXPECTED_PROPEXT_ONLY_THEOREMS = {
    "ProofNetIR.Certificate.linkLeftRetainedEdges_lookup_origin",
    "ProofNetIR.LeanProp.Derivation.linearAxiomCount_eq_length",
    "ProofNetIR.LeanProp.Assumptions.split_append",
    "ProofNetIR.LeanProp.Assumptions.permute_symm",
    "ProofNetIR.LeanProp.Assumptions.permute_symm_right",
    "ProofNetIR.LeanProp.ContextPermutation.symm_symm",
    "ProofNetIR.Certificate.isCuspFreeTraversal_eq_true_iff",
    "ProofNetIR.Certificate.isCuspFreeCycleTraversal_eq_true_iff",
    "ProofNetIR.UnificationStep.marks_fired_conclusion",
    "ProofNetIR.UnificationMarking.referenceDirectedEdge_origin",
    "ProofNetIR.UnificationMarking.marked_to_unmarked_referenceEdge_connective_origin",
    "ProofNetIR.UnificationState.Abstractable.markConclusion",
    "ProofNetIR.UnificationMarking.ext",
    "ProofNetIR.UnificationState.ObservationEquivalent.abstractable",
    "ProofNetIR.SequentialUnification.sourceIndex_size",
    "ProofNetIR.SequentialUnification.nextAxiomWithFuel?_sound",
    "ProofNetIR.SequentialUnification.nextAxiomWithFuel?_tag_trace_invariants",
    "ProofNetIR.SequentialUnification.nextAxiomWithFuel?_touched_tagged",
    "ProofNetIR.SequentialUnification.nextAxiomWithFuel?_tagged_iff_input_or_touched",
    "ProofNetIR.SequentialUnification.nextAxiom?_tagged_iff_input_or_touched",
    "ProofNetIR.SequentialUnification.nextAxiomWithFuel?_threaded_touched_disjoint",
    "ProofNetIR.SequentialUnification.NextAxiomResult.linkIndex_ne_of_input_left_tagged",
    "ProofNetIR.SequentialUnification.NextAxiomResult.threaded_linkIndex_ne",
    "ProofNetIR.SequentialUnification.SourceLeftChain.cons_of_head",
    "ProofNetIR.SequentialUnification.SourceLeftChain.reachable_of_head_last",
    "ProofNetIR.SequentialUnification.nextAxiomWithFuel?_route",
    "ProofNetIR.SequentialUnification.nextAxiom?_route",
    "ProofNetIR.SequentialUnification.nextAxiomWithFuel?_startReady",
    "ProofNetIR.SequentialUnification.nextAxiom?_startReady",
    "ProofNetIR.ConsumerIndex.build_size",
    "ProofNetIR.ConsumerIndex.Sound.origin",
    "ProofNetIR.Certificate.UnificationComponent.axiom?_success",
    "ProofNetIR.SequentialSchedulerBridge.initial_realizesSigma",
    "ProofNetIR.SequentialSchedulerState.sigmaBoundary?_mem",
    "ProofNetIR.SequentialSchedulerState.sigmaBoundary?_le",
    "ProofNetIR.SequentialSchedulerState.sigmaBoundary?_append_fresh_old",
    "ProofNetIR.SequentialSchedulerState.SequentialStackState.WellShaped.waiting_lookup_exists",
    "ProofNetIR.SequentialSchedulerState.SequentialStackState.popReadyMark?_ok_iff",
    "ProofNetIR.SequentialSchedulerState.SequentialStackState.popReadyMark?_exact",
    "ProofNetIR.SequentialSchedulerState.SequentialStackState.initEnqueue?_some_iff",
    "ProofNetIR.SequentialSchedulerState.SequentialStackState.newEnqueue?_some_iff",
    "ProofNetIR.SequentialSchedulerState.SequentialStackState.newEnqueue?_exact",
    "ProofNetIR.SequentialSchedulerState.SequentialStackState.newEnqueue?_waiting_of_ne",
    "ProofNetIR.SequentialSchedulerState.SequentialStackState.newEnqueue?_endpoint_unmarked",
    "ProofNetIR.SequentialSchedulerState.SequentialStackState.empty_operationalWaitingDomain",
    "ProofNetIR.UnificationState.markReadyRaw?_ok_iff",
    "ProofNetIR.UnificationState.markReadyRaw?_markOutOfBounds_iff",
    "ProofNetIR.UnificationState.markReadyRaw?_alreadyMarked_iff",
    "ProofNetIR.UnificationState.markReadyRaw?_exact",
    "ProofNetIR.UnificationState.markReadyRaw?_carriers",
    "ProofNetIR.UnificationState.markReadyRaw?_counters",
    "ProofNetIR.UnificationState.markReadyRaw?_orderedParents",
    "ProofNetIR.UnificationState.markReadyRaw?_abstractable",
    "ProofNetIR.SequentialSchedulerBridge.popReadyMark_markReadyRaw_realizesSigma",
    "ProofNetIR.LeanProp.Derivation.normalizePersistentStructural_reduced",
    "ProofNetIR.LeanProp.Derivation.normalizePersistentStructural_eq_self_of_reduced",
    "ProofNetIR.LeanProp.Derivation.normalizePersistentStructural_idempotent",
    "ProofNetIR.LeanProp.Derivation.normalizePersistentStructural_contract_weaken",
    "ProofNetIR.LeanProp.Derivation.normalizePersistentStructural_linearAxiomCount",
    "ProofNetIR.LeanProp.Derivation.normalizePersistentStructural_toProof",
    "ProofNetIR.LeanProp.Schema.PackedDerivation.sound",
    "ProofNetIR.LeanProp.Schema.Raw.Derivation.infer?_ofIndexed",
    "ProofNetIR.LeanProp.Schema.Raw.Permutation.boundary?_eq_elaborate?",
    "ProofNetIR.LeanProp.Schema.Raw.CheckedDerivation.sound",
}
EXPECTED_PROPEXT_QUOT_THEOREMS = {
    "ProofNetIR.Graph.EdgeSimplePath.exists_traversed_first_boundary_of_start_true",
    "ProofNetIR.Graph.EdgeSimplePath.prefixBefore",
    "ProofNetIR.Graph.EdgeSimplePath.suffixAfter",
    "ProofNetIR.Graph.EdgeSimplePath.uniqueIntersection_of_traversal_split",
    "ProofNetIR.UnificationMarking.referencePath_has_first_unmarked_to_marked_boundary",
    "ProofNetIR.Graph.Acyclic.reindex",
    "ProofNetIR.Graph.acyclic_reindex_iff",
    "ProofNetIR.Graph.isEdgeSimpleCycleTraversal_sound",
    "ProofNetIR.Graph.isEdgeSimpleCycleTraversal_complete",
    "ProofNetIR.LeanProp.Schema.Raw.Derivation.inferAt_eq_elaborateAt",
    "ProofNetIR.LeanProp.Schema.Raw.Derivation.elaborate?_complete",
    "ProofNetIR.LeanProp.Schema.Raw.CheckedDerivation.inferred",
    "ProofNetIR.LeanProp.Derivation.normalizePersistentStructural_size_le",
    "ProofNetIR.UnificationState.markConclusion_toMarking_mark",
    "ProofNetIR.UnificationState.markConclusion_forwardStep",
    "ProofNetIR.UnificationState.ObservationEquivalent.toMarking_eq",
    "ProofNetIR.UnificationState.forwardToken?_success",
    "ProofNetIR.UnificationState.forwardToken?_refines",
    "ProofNetIR.UnificationMarking.mergeExtension_congr",
    "ProofNetIR.UnificationMarking.mergeExtension_comm",
    "ProofNetIR.SequentialSchedulerState.SigmaAgePartition.empty",
    "ProofNetIR.SequentialSchedulerState.SigmaAgePartition.reserveInitial",
    "ProofNetIR.SequentialSchedulerState.SigmaAgePartition.appendFresh",
    "ProofNetIR.SequentialSchedulerState.SigmaAgePartition.sigmaBoundary?_append_fresh_self",
    "ProofNetIR.SequentialSchedulerState.sigmaBoundary?_greatest",
    "ProofNetIR.SequentialSchedulerState.SigmaAgePartition.boundary_exists",
    "ProofNetIR.SequentialSchedulerState.SequentialStackState.empty_wellShaped",
    "ProofNetIR.SequentialSchedulerState.SequentialStackState.AllMarksUndefined.lookup",
    "ProofNetIR.SequentialSchedulerState.SequentialStackState.initEnqueue?_endpoint_unmarked",
    "ProofNetIR.SequentialSchedulerState.SequentialStackState.initEnqueue?_wellShaped",
    "ProofNetIR.SequentialSchedulerState.SequentialStackState.newEnqueue?_wellShaped",
    "ProofNetIR.SequentialSchedulerState.SequentialStackState.OperationalWaitingDomain.active_undefined",
    "ProofNetIR.SequentialSchedulerState.SequentialStackState.operationalNewEnqueue?_some_iff",
    "ProofNetIR.SequentialSchedulerState.SequentialStackState.operationalNewEnqueue?_exact",
    "ProofNetIR.SequentialSchedulerState.SequentialStackState.operationalNewEnqueue?_endpoint_unmarked",
    "ProofNetIR.SequentialSchedulerState.SequentialStackState.operationalNewEnqueue?_wellShaped",
    "ProofNetIR.SequentialSchedulerState.SequentialStackState.operationalNewEnqueue?_operationalWaitingDomain",
    "ProofNetIR.ConsumerIndex.build_origin",
    "ProofNetIR.ConsumerIndex.build_complete",
    "ProofNetIR.ConsumerIndex.build_sound",
    "ProofNetIR.ConsumerIndex.build_isComplete",
    "ProofNetIR.ConsumerIndex.uniqueConsumer?_eq_some_iff",
    "ProofNetIR.tensorBelow?_eq_some_iff",
    "ProofNetIR.tensorBelow?_consumer",
    "ProofNetIR.tensorBelow?_link",
    "ProofNetIR.tensorBelow?_wellFormed",
    "ProofNetIR.tensorBelow?_premise",
    "ProofNetIR.tensorBelow?_mate_ne",
    "ProofNetIR.Certificate.tensorBelow?_eq_some_iff",
    "ProofNetIR.Certificate.tensorBelow?_consumer",
    "ProofNetIR.Certificate.tensorBelow?_link",
    "ProofNetIR.Certificate.tensorBelow?_wellFormed",
    "ProofNetIR.Certificate.tensorBelow?_premise",
    "ProofNetIR.Certificate.tensorBelow?_mate_ne",
    "ProofNetIR.Certificate.mem_worklistConsumers_of_premise",
    "ProofNetIR.Certificate.mem_worklistConsumers_origin",
    "ProofNetIR.Certificate.mem_worklistConsumers_submitted_connective",
    "ProofNetIR.SequentialSchedulerState.SequentialStackState.popReadyMark?_wellShaped",
    "ProofNetIR.SequentialUnification.NextAxiomRoute.orientedEndpoints?_eq",
    "ProofNetIR.Certificate.reserveAxiomAt?_exact",
    "ProofNetIR.Certificate.reserveAxiomAt?_endpoint_unmarked",
    "ProofNetIR.Certificate.reserveAxiomAt?_componentsParentsAligned",
    "ProofNetIR.Certificate.reserveAxiomAt?_counterAligned",
}
EXPECTED_THEOREMS = (
    EXPECTED_CLASSICAL_THEOREMS
    | EXPECTED_AXIOM_FREE_THEOREMS
    | EXPECTED_PROPEXT_ONLY_THEOREMS
    | EXPECTED_PROPEXT_QUOT_THEOREMS
)
EXPECTED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def find_lake() -> str:
    on_path = shutil.which("lake")
    if on_path is not None:
        return on_path
    elan_bin = Path.home() / ".elan" / "bin"
    for executable in ("lake", "lake.exe"):
        candidate = elan_bin / executable
        if candidate.is_file():
            return str(candidate)
    raise FileNotFoundError("lake was not found on PATH or under ~/.elan/bin")


def main() -> None:
    completed = subprocess.run(
        [find_lake(), "env", "lean", str(AUDIT_FILE)],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
        encoding="utf-8",
    )
    output = completed.stdout + completed.stderr
    matches = re.findall(
        r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", output, re.DOTALL
    )
    actual: dict[str, set[str]] = {}
    for theorem, raw_axioms in matches:
        actual[theorem] = {
            axiom.strip() for axiom in raw_axioms.split(",") if axiom.strip()
        }
    for theorem in re.findall(
        r"'([^']+)' does not depend on any axioms", output
    ):
        actual[theorem] = set()

    if set(actual) != EXPECTED_THEOREMS:
        raise AssertionError(
            "theorem audit boundary changed: "
            f"actual={sorted(actual)}, expected={sorted(EXPECTED_THEOREMS)}\n{output}"
        )
    unexpected = {}
    for theorem, axioms in actual.items():
        if theorem in EXPECTED_AXIOM_FREE_THEOREMS:
            expected = set()
        elif theorem in EXPECTED_PROPEXT_ONLY_THEOREMS:
            expected = {"propext"}
        elif theorem in EXPECTED_PROPEXT_QUOT_THEOREMS:
            expected = {"propext", "Quot.sound"}
        else:
            expected = EXPECTED_AXIOMS
        if axioms != expected:
            unexpected[theorem] = {
                "actual": sorted(axioms),
                "expected": sorted(expected),
            }
    if unexpected:
        raise AssertionError(
            "theorem trust dependencies changed: "
            f"actual={unexpected}"
        )
    print(
        "ProofNet-IR axiom audit passed: "
        f"{len(EXPECTED_CLASSICAL_THEOREMS)} public MLL theorems use exactly "
        "[propext, Classical.choice, Quot.sound]; "
        f"{len(EXPECTED_AXIOM_FREE_THEOREMS)} additional audited theorems "
        "are axiom-free; "
        f"{len(EXPECTED_PROPEXT_ONLY_THEOREMS)} use exactly [propext]; "
        f"{len(EXPECTED_PROPEXT_QUOT_THEOREMS)} use exactly "
        "[propext, Quot.sound]"
    )


if __name__ == "__main__":
    main()
