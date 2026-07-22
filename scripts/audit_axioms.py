#!/usr/bin/env python3
"""Fail if the public theorem boundary silently gains trust dependencies."""

from __future__ import annotations

import re
import shutil
import subprocess
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
AUDIT_FILE = ROOT / "ProofNetIRAxiomAudit.lean"
EXPECTED_THEOREMS = {
    "ProofNetIR.Certificate.check_iff_declarativelyCorrect",
    "ProofNetIR.Certificate.sequentialization_of_check",
    "ProofNetIR.Certificate.generallySequentializable",
    "ProofNetIR.Certificate.reindexEquivalent?_eq_true_iff_of_check",
    "ProofNetIR.Certificate.matchingFormulaOrders_complete",
    "ProofNetIR.Certificate.directProofNetEquivalentWitness?_complete",
    "ProofNetIR.ExecutableSequentializationResult.kernelDerivation",
    "ProofNetIR.ExecutableSequentializationResult.proofNetEquivalent",
}
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

    if set(actual) != EXPECTED_THEOREMS:
        raise AssertionError(
            "theorem audit boundary changed: "
            f"actual={sorted(actual)}, expected={sorted(EXPECTED_THEOREMS)}\n{output}"
        )
    unexpected = {
        theorem: sorted(axioms)
        for theorem, axioms in actual.items()
        if axioms != EXPECTED_AXIOMS
    }
    if unexpected:
        raise AssertionError(
            "theorem trust dependencies changed: "
            f"actual={unexpected}, expected={sorted(EXPECTED_AXIOMS)}"
        )
    print(
        "ProofNet-IR axiom audit passed: "
        f"{len(actual)} public theorems use exactly "
        "[propext, Classical.choice, Quot.sound]"
    )


if __name__ == "__main__":
    main()
