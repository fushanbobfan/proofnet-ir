#!/usr/bin/env python3
"""Exercise the trust gate against real, isolated Lean-compiled declarations."""

from __future__ import annotations

import os
from pathlib import Path
import subprocess
import tempfile
import unittest

import audit_axioms as audit


class LibraryTrustTests(unittest.TestCase):
    def test_inventory_includes_modules_outside_facade(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / "ProofNetIR.lean").write_text("", encoding="utf-8")
            (root / "ProofNetIR" / "Nested").mkdir(parents=True)
            (root / "ProofNetIR" / "Nested" / "Unimported.lean").touch()
            self.assertEqual(audit.library_modules(root), [
                "ProofNetIR", "ProofNetIR.Nested.Unimported",
            ])

    def test_inventory_fails_closed_when_empty(self):
        with tempfile.TemporaryDirectory() as temporary:
            with self.assertRaisesRegex(AssertionError, "inventory"):
                audit.library_modules(Path(temporary))

    def compile_and_audit(
        self, source: str, *, module_system: bool = False,
    ) -> subprocess.CompletedProcess:
        with tempfile.TemporaryDirectory(prefix="proofnet-trust-") as temporary:
            directory = Path(temporary)
            fixture = directory / "TrustFixture.lean"
            header = "module\nimport Lean\n" if module_system else "import Lean\n"
            fixture.write_text(header + source + "\n", encoding="utf-8")
            env = os.environ.copy()
            env["LEAN_PATH"] = str(directory) + os.pathsep + env.get("LEAN_PATH", "")
            command = [audit.find_lake(), "env", "lean"]
            compiled = subprocess.run(
                command + ["--root", str(directory), "-o",
                           str(fixture.with_suffix(".olean")), str(fixture)],
                cwd=audit.ROOT, env=env, capture_output=True, text=True, encoding="utf-8",
            )
            self.assertEqual(compiled.returncode, 0, compiled.stdout + compiled.stderr)
            return subprocess.run(
                command + ["--trust=0", "-DwarningAsError=true", "--run",
                           str(audit.LIBRARY_AUDIT_FILE),
                           "TrustFixture"],
                cwd=audit.ROOT, env=env, capture_output=True, text=True, encoding="utf-8",
            )

    def assert_rejected(self, source: str, dependency: str):
        result = self.compile_and_audit(source)
        output = result.stdout + result.stderr
        self.assertNotEqual(result.returncode, 0, output)
        self.assertIn("library trust audit rejected", output)
        self.assertIn(dependency, output)
        self.assertIn("TrustFixture:", output)

    def test_standard_axioms_and_private_helpers_pass(self):
        result = self.compile_and_audit("""
private theorem helper : True := True.intro
theorem visible : True := helper
theorem extensional (p q : Prop) (h : p ↔ q) : p = q := propext h
noncomputable def choose (h : Nonempty Nat) : Nat := Classical.choice h
theorem quotient {α : Sort u} {r : α → α → Prop} {a b : α} (h : r a b) :
    Quot.mk r a = Quot.mk r b := Quot.sound h
""")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("library trust audit passed", result.stdout)

    def test_unlisted_theorem_with_sorry_is_rejected(self):
        self.assert_rejected("theorem unlisted : False := by sorry", "sorryAx")

    def test_private_placeholder_is_rejected(self):
        self.assert_rejected("private theorem hidden : False := by sorry", "sorryAx")

    def test_definition_with_placeholder_is_rejected(self):
        self.assert_rejected("def hidden : Nat := by sorry", "sorryAx")

    def test_module_system_private_proof_is_rejected(self):
        result = self.compile_and_audit(
            "private theorem hidden : False := by sorry", module_system=True,
        )
        output = result.stdout + result.stderr
        self.assertNotEqual(result.returncode, 0, output)
        self.assertIn("library trust audit rejected", output)
        self.assertIn("sorryAx", output)

    def test_no_declarations_fails_closed(self):
        result = self.compile_and_audit("")
        self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("found no declarations", result.stdout + result.stderr)

    def test_axiom_outside_library_namespace_is_rejected(self):
        self.assert_rejected("axiom Foreign.unsound : False", "Foreign.unsound")

    def test_transitive_dependency_is_rejected(self):
        self.assert_rejected("""
axiom Foreign.unsound : False
private theorem helper : False := Foreign.unsound
theorem consequence : 0 = 1 := False.elim helper
""", "consequence depends on #[Foreign.unsound]")

    def test_native_decide_fixture_is_rejected(self):
        self.assert_rejected(
            "theorem nativeFact : 1 + 1 = 2 := by native_decide",
            "nativeFact._native.native_decide.",
        )


if __name__ == "__main__":
    unittest.main(verbosity=2)
