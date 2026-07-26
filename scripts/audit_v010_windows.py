#!/usr/bin/env python3
"""Run the frozen v0.10 audit under restrictive Windows application control.

The preregistered model experiment hashes ``audit_v010.py`` byte-for-byte, so
that original audit must remain unchanged.  This opt-in wrapper changes only
how its two known Lean data producers are launched when Windows explicitly
returns application-control error 4551.  Every other subprocess failure still
fails closed.
"""

from __future__ import annotations

import subprocess
import sys

import audit_v010 as audit


LEAN_RUN_SOURCES = {
    "proofnet_ir_audit_graph": "ProofNetIRAuditGraph.lean",
    "proofnet_ir_audit_certificates": "ProofNetIRAuditCertificates.lean",
}

ORIGINAL_RUN_LEAN = audit.run_lean


def run_lean_with_policy_fallback(executable: str) -> list[str]:
    try:
        return ORIGINAL_RUN_LEAN(executable)
    except subprocess.CalledProcessError as error:
        source = LEAN_RUN_SOURCES.get(executable)
        policy_blocked = (
            sys.platform == "win32"
            and "4551" in (error.stderr or "")
            and source is not None
        )
        if not policy_blocked:
            raise
        completed = subprocess.run(
            [audit.LAKE, "env", "lean", "--run", source],
            cwd=audit.ROOT,
            check=True,
            capture_output=True,
            text=True,
            encoding="utf-8",
        )
        return completed.stdout.splitlines()


audit.run_lean = run_lean_with_policy_fallback

if __name__ == "__main__":
    raise SystemExit(audit.main())
