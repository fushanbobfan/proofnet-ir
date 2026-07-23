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
    "ProofNetIR.Certificate.sequentialize_complete",
    "ProofNetIR.ExecutableSequentializationResult.kernelDerivation",
    "ProofNetIR.ExecutableSequentializationResult.proofNetEquivalent",
}
EXPECTED_AXIOM_FREE_THEOREMS = {
    "ProofNetIR.LeanProp.Derivation.toProof",
    "ProofNetIR.LeanProp.Derivation.linearAxiomCount_eq_length",
}
EXPECTED_THEOREMS = EXPECTED_CLASSICAL_THEOREMS | EXPECTED_AXIOM_FREE_THEOREMS
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
        expected = set() if theorem in EXPECTED_AXIOM_FREE_THEOREMS else EXPECTED_AXIOMS
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
        f"{len(EXPECTED_AXIOM_FREE_THEOREMS)} LeanProp theorems are axiom-free"
    )


if __name__ == "__main__":
    main()
