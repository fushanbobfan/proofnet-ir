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
    "ProofNetIR.Certificate.unificationFastCheck_eq_true_iff",
    "ProofNetIR.Certificate.unificationFastCheck_sound",
    "ProofNetIR.Certificate.unificationCheck_eq_check",
    "ProofNetIR.Certificate.unificationCheck_eq_true_iff_check",
    "ProofNetIR.Certificate.unificationCheck_eq_true_iff_declarativelyCorrect",
    "ProofNetIR.ExecutableSequentializationResult.kernelDerivation",
    "ProofNetIR.ExecutableSequentializationResult.proofNetEquivalent",
}
EXPECTED_AXIOM_FREE_THEOREMS = {
    "ProofNetIR.LeanProp.Derivation.toProof",
    "ProofNetIR.LeanProp.ContextPermutation.nonempty_iff_listPerm",
    "ProofNetIR.LeanProp.Derivation.persistentExchange_nonempty_of_listPerm",
    "ProofNetIR.LeanProp.Derivation.linearExchange_nonempty_of_listPerm",
    "ProofNetIR.UnificationCandidateResult.linkVisitsBound",
}
EXPECTED_PROPEXT_ONLY_THEOREMS = {
    "ProofNetIR.LeanProp.Derivation.linearAxiomCount_eq_length",
    "ProofNetIR.LeanProp.Assumptions.split_append",
    "ProofNetIR.LeanProp.Assumptions.permute_symm",
    "ProofNetIR.LeanProp.Assumptions.permute_symm_right",
    "ProofNetIR.LeanProp.ContextPermutation.symm_symm",
    "ProofNetIR.Certificate.isCuspFreeTraversal_eq_true_iff",
    "ProofNetIR.Certificate.isCuspFreeCycleTraversal_eq_true_iff",
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
    "ProofNetIR.Graph.Acyclic.reindex",
    "ProofNetIR.Graph.acyclic_reindex_iff",
    "ProofNetIR.Graph.isEdgeSimpleCycleTraversal_sound",
    "ProofNetIR.Graph.isEdgeSimpleCycleTraversal_complete",
    "ProofNetIR.LeanProp.Schema.Raw.Derivation.inferAt_eq_elaborateAt",
    "ProofNetIR.LeanProp.Schema.Raw.Derivation.elaborate?_complete",
    "ProofNetIR.LeanProp.Schema.Raw.CheckedDerivation.inferred",
    "ProofNetIR.LeanProp.Derivation.normalizePersistentStructural_size_le",
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
