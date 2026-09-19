#!/usr/bin/env python3
"""Unit tests for the pure convergence-checker rules."""

from __future__ import annotations

import unittest

import check_convergence as check


def added_file(path: str, lines: list[str]) -> str:
    body = "\n".join(f"+{line}" for line in lines)
    return (
        f"diff --git a/{path} b/{path}\n"
        "new file mode 100644\n"
        "index 0000000..1111111\n"
        "--- /dev/null\n"
        f"+++ b/{path}\n"
        f"@@ -0,0 +1,{len(lines)} @@\n{body}\n"
    )


def theorem_fixture(name: str, private: bool = False):
    path = "ProofNetIR/Fresh.lean"
    source = f"{'private ' if private else ''}theorem {name} : True := by trivial\n"
    diffs = check.parse_diff(added_file(path, source.splitlines()))
    return check.new_theorems(diffs, {}, {path: source})


def changelog(body: list[str]) -> str:
    return "# Changelog\n\n## Unreleased\n" + "\n".join(body) + "\n\n## 0.9.0\n"


class ConvergenceRuleTests(unittest.TestCase):
    def test_a_module_path_passes(self):
        suffix = "A" * 35 + ".lean"
        diffs = check.parse_diff(added_file("ProofNetIR/" + suffix, ["def x := 1"]))
        self.assertEqual(check.check_module_paths(diffs), [])

    def test_a_module_path_fails(self):
        suffix = "A" * 36 + ".lean"
        diffs = check.parse_diff(added_file("ProofNetIR/" + suffix, ["def x := 1"]))
        self.assertIn("41 characters", check.check_module_paths(diffs)[0])

    def test_b_module_count_passes(self):
        diffs = check.parse_diff(added_file("ProofNetIR/One.lean", ["def one := 1"]))
        self.assertEqual(check.check_module_count(diffs, 1), [])

    def test_b_module_count_fails(self):
        text = added_file("ProofNetIR/One.lean", ["def one := 1"])
        text += added_file("ProofNetIR/Two.lean", ["def two := 2"])
        self.assertIn("2 new files", check.check_module_count(check.parse_diff(text), 1)[0])

    def test_c_theorem_name_passes_and_private_is_ignored(self):
        public = theorem_fixture("t" * 60)
        private = theorem_fixture("t" * 61, private=True)
        self.assertEqual(check.check_theorem_names(public + private), [])
        self.assertEqual(private, [])

    def test_c_theorem_name_fails(self):
        errors = check.check_theorem_names(theorem_fixture("t" * 61))
        self.assertIn("61 characters", errors[0])

    def test_d_prose_budget_passes_at_ratio_and_for_docs_only(self):
        balanced = check.parse_numstat("10\t0\tProofNetIR/A.lean\n5\t0\tdocs/note.md\n")
        docs_only = check.parse_numstat("20\t0\tdocs/note.md\n")
        self.assertEqual(check.check_prose_budget(balanced, 0.5), [])
        self.assertEqual(check.check_prose_budget(docs_only, 0.5), [])

    def test_d_prose_budget_fails(self):
        stats = check.parse_numstat("10\t0\tProofNetIR/A.lean\n6\t0\tCONTRIBUTING.md\n")
        self.assertIn("prose additions 6", check.check_prose_budget(stats, 0.5)[0])

    def test_e_growth_cap_passes(self):
        base = {"docs/current-status.md": "\n".join(["old"] * 399)}
        head = {"docs/current-status.md": "\n".join(["old"] * 400)}
        self.assertEqual(check.check_growth_caps(base, head), [])

    def test_e_growth_cap_fails(self):
        base = {"docs/current-status.md": "\n".join(["old"] * 399)}
        head = {"docs/current-status.md": "\n".join(["old"] * 401)}
        self.assertIn("399 -> 401", check.check_growth_caps(base, head)[0])

    def test_e_over_cap_status_allows_receipt_replacement(self):
        base = {"docs/current-status.md": "\n".join(["old"] * 1488)}
        head = {"docs/current-status.md": "\n".join(["old"] * 1496)}
        self.assertEqual(check.check_growth_caps(base, head), [])

    def test_e_over_cap_status_rejects_accumulation(self):
        base = {"docs/current-status.md": "\n".join(["old"] * 1488)}
        head = {"docs/current-status.md": "\n".join(["old"] * 1501)}
        self.assertIn("receipt replacements", check.check_growth_caps(base, head)[0])

    def test_e_over_cap_changelog_allows_one_twelve_line_entry(self):
        old_body = ["- old entry"] + ["  retained"] * 300
        entry = ["- checkpoint"] + ["  detail"] * 11
        base = {"CHANGELOG.md": changelog(old_body)}
        head = {"CHANGELOG.md": changelog(entry + old_body)}
        self.assertEqual(check.check_growth_caps(base, head), [])

    def test_e_over_cap_changelog_rejects_larger_growth(self):
        old_body = ["- old entry"] + ["  retained"] * 300
        entry = ["- checkpoint"] + ["  detail"] * 12
        base = {"CHANGELOG.md": changelog(old_body)}
        head = {"CHANGELOG.md": changelog(entry + old_body)}
        self.assertIn("one entry of at most 12 lines", check.check_growth_caps(base, head)[0])

    def test_e_over_cap_changelog_rejects_two_entries(self):
        old_body = ["- old entry"] + ["  retained"] * 300
        base = {"CHANGELOG.md": changelog(old_body)}
        head = {"CHANGELOG.md": changelog(["- first", "- second"] + old_body)}
        self.assertTrue(check.check_growth_caps(base, head))

    def test_e_over_cap_changelog_explains_maintenance(self):
        base = {"CHANGELOG.md": changelog(["- old entry"] + ["  retained"] * 300)}
        notes = check.maintenance_notes(base)
        self.assertIn("3,200-line", notes[0])
        self.assertIn("docs-only commit", notes[0])

    def test_f_one_place_passes_in_permitted_homes(self):
        theorem = theorem_fixture("fresh_result")[0]
        head = {
            "docs/goal-ledger.md": "`ProofNetIR.fresh_result`\n",
            "scripts/helper.py": "name = 'fresh_result'\n",
            "ProofNetIR/Fresh.lean": "theorem fresh_result : True := by trivial\n",
        }
        self.assertEqual(check.check_one_place([theorem], head), [])

    def test_f_one_place_fails_elsewhere(self):
        theorem = theorem_fixture("fresh_result")[0]
        errors = check.check_one_place([theorem], {"README.md": "See `fresh_result`.\n"})
        self.assertIn("README.md:1", errors[0])


if __name__ == "__main__":
    unittest.main(verbosity=2)
