#!/usr/bin/env python3
"""Mechanical convergence gates for a two-ref diff (no third-party packages).

Renames are deliberately counted as deletion/addition. The theorem scan is a
lexical source scan, not a Lean parser: it handles ordinary theorem commands,
attributes, namespaces, private declarations, strings and nested comments.
It does not expand macros. Semantic ledger closure remains a review decision.
"""

from __future__ import annotations

import argparse
import ast
from difflib import SequenceMatcher
from dataclasses import dataclass, field
import math
import re
import subprocess
import sys


# Absolute line caps for maintained prose. A file under its cap may not cross it;
# a file already over its cap may not grow (with the two narrow exceptions
# below). Shrinking is always permitted.
CAPS = {
    "CHANGELOG.md": 300,  # the ## Unreleased section only
    "docs/current-status.md": 400,
    "README.md": 600,
    "docs/architecture.md": 600,
    "docs/trust-model.md": 400,
    "docs/library-readiness-audit.md": 500,
    "docs/source-coverage-audit.md": 200,
    "docs/v0.10-design.md": 400,
    "docs/v0.11-design.md": 400,
    "docs/roadmap.md": 600,
    "docs/guerrini-unification-audit.md": 500,
    "docs/performance.md": 500,
}
STATUS_REPLACEMENT_SLACK = 12
THEOREM_HOMES = {
    "CHANGELOG.md", "docs/api-reference.md", "docs/roadmap.md", "docs/goal-ledger.md",
}
IDENT = r"(?:«[^»\n]+»|[^\W\d][\w'!?]*)(?:\.(?:«[^»\n]+»|[^\W\d][\w'!?]*))*"
THEOREM = re.compile(
    rf"^[ \t]*(?P<modifiers>(?:(?:@\[[^]]*\]|private|protected|noncomputable|"
    rf"unsafe|partial|nonrec)\s+)*)theorem\s+(?P<name>{IDENT})", re.MULTILINE,
)
SCOPE = re.compile(
    rf"^[ \t]*(?P<kind>namespace|section|end)\b[ \t]*(?P<name>{IDENT})?", re.MULTILINE,
)


@dataclass
class FileDiff:
    path: str
    new: bool = False
    added: set[int] = field(default_factory=set)


@dataclass(frozen=True)
class Theorem:
    path: str
    name: str
    qualified: str
    first_line: int
    last_line: int


def parse_numstat(text: str) -> dict[str, tuple[int, int]]:
    """Parse --no-renames --numstat, including its NUL-delimited form, into
    per-path (added, deleted) line counts; binary paths count as (0, 0)."""
    result = {}
    for record in text.split("\0") if "\0" in text else text.splitlines():
        if not record:
            continue
        added, deleted, path = record.split("\t", 2)
        result[path] = (0, 0) if added == "-" else (int(added), int(deleted))
    return result


def diff_path(text: str) -> str:
    if text.startswith('"'):
        # Git quotes UTF-8 bytes with C-style octal escapes.
        text = ast.literal_eval(text)
        try:
            text = text.encode("latin1").decode("utf-8")
        except (UnicodeEncodeError, UnicodeDecodeError):
            pass
    return text[2:] if text.startswith(("a/", "b/")) else text


def parse_diff(text: str) -> list[FileDiff]:
    result = []
    current = None
    is_new = False
    in_hunk = False
    head_line = 0
    for line in text.splitlines():
        if line.startswith("diff --git "):
            current, is_new, in_hunk = None, False, False
        elif not in_hunk and line.startswith("new file mode "):
            is_new = True
        elif not in_hunk and line == "--- /dev/null":
            is_new = True
        elif not in_hunk and line.startswith("+++ "):
            path = diff_path(line[4:].rstrip("\t"))
            current = FileDiff(path, is_new)
            result.append(current)
        elif line.startswith("@@ "):
            match = re.match(r"@@ -\d+(?:,\d+)? \+(\d+)(?:,\d+)? @@", line)
            if match is None:
                raise ValueError(f"unsupported diff hunk: {line}")
            head_line, in_hunk = int(match[1]), True
        elif current is not None and in_hunk:
            if line.startswith("+"):
                current.added.add(head_line)
                head_line += 1
            elif line.startswith(" "):
                head_line += 1
    return result


def lean_code(source: str) -> str:
    """Mask comments and string literals while preserving offsets/newlines."""
    out = list(source)
    i, depth, string = 0, 0, False
    while i < len(source):
        pair = source[i:i + 2]
        if depth:
            width = 2 if pair in ("/-", "-/") else 1
            depth += (1 if pair == "/-" else -1 if pair == "-/" else 0)
        elif string:
            width = 2 if source[i] == "\\" else 1
            if source[i] == '"':
                string = False
        elif pair == "--":
            end = source.find("\n", i)
            width = (len(source) if end < 0 else end) - i
        elif pair == "/-":
            depth, width = 1, 2
        elif source[i] == '"':
            string, width = True, 1
        elif source[i] == "«":
            end = source.find("»", i + 1)
            i = len(source) if end < 0 else end + 1
            continue
        else:
            i += 1
            continue
        for j in range(i, min(i + width, len(source))):
            if source[j] != "\n":
                out[j] = " "
        i += width
    return "".join(out)


def public_theorems(path: str, source: str) -> list[Theorem]:
    code = lean_code(source)
    scopes = []
    result = []
    events = [(m.start(), "scope", m) for m in SCOPE.finditer(code)]
    events += [(m.start(), "theorem", m) for m in THEOREM.finditer(code)]
    for _, kind, match in sorted(events, key=lambda event: event[0]):
        if kind == "scope":
            if match["kind"] == "end":
                if scopes:
                    scopes.pop()
            else:
                scopes.append(match["name"] if match["kind"] == "namespace" else None)
        elif not re.search(r"\bprivate\b", match["modifiers"]):
            name = match["name"]
            qualified = ".".join([s for s in scopes if s] + [name])
            if name.startswith("_root_."):
                qualified = name.removeprefix("_root_.")
            result.append(Theorem(
                path, name, qualified,
                code.count("\n", 0, match.start()) + 1,
                code.count("\n", 0, match.end()) + 1,
            ))
    return result


def new_theorems(
    diffs: list[FileDiff], base: dict[str, str], head: dict[str, str],
) -> list[Theorem]:
    old_names = {
        theorem.qualified for path, source in base.items() if path.endswith(".lean")
        for theorem in public_theorems(path, source)
    }
    return [
        theorem for diff in diffs if diff.path.endswith(".lean")
        for theorem in public_theorems(diff.path, head.get(diff.path, ""))
        if theorem.qualified not in old_names
        and any(line in diff.added for line in range(theorem.first_line, theorem.last_line + 1))
    ]


def check_module_paths(diffs: list[FileDiff]) -> list[str]:
    return [
        f"(a) new module path {d.path!r}: {len(d.path[11:])} characters after ProofNetIR/ (max 40)"
        for d in diffs if d.new and d.path.startswith("ProofNetIR/") and len(d.path[11:]) > 40
    ]


def check_module_count(diffs: list[FileDiff], maximum: int = 1) -> list[str]:
    count = sum(d.new and d.path.startswith("ProofNetIR/") for d in diffs)
    return [f"(b) {count} new files under ProofNetIR/ exceed --max-new-modules {maximum}"] if count > maximum else []


def check_theorem_names(theorems: list[Theorem]) -> list[str]:
    return [
        f"(c) {t.path}:{t.first_line}: new public theorem {t.name!r} has {len(t.name)} characters (max 60)"
        for t in theorems if len(t.name) > 60
    ]


def prose_path(path: str) -> bool:
    return path in {"README.md", "CHANGELOG.md", "CONTRIBUTING.md"} or (
        path.startswith("docs/") and path.count("/") == 1 and path.endswith(".md")
        and path != "docs/api-reference.md"
    )


def line_totals(numstat: dict[str, tuple[int, int]]) -> tuple[int, int]:
    """Library lines added and net prose growth (additions minus deletions,
    floored at zero): rewriting a stale description in place is not growth."""
    return (
        sum(added for p, (added, _) in numstat.items() if p.startswith("ProofNetIR/")),
        max(0, sum(added - deleted for p, (added, deleted) in numstat.items() if prose_path(p))),
    )


def check_prose_budget(numstat: dict[str, tuple[int, int]], ratio: float = 0.5) -> list[str]:
    lean, prose = line_totals(numstat)
    return [
        f"(d) net prose growth {prose} exceeds {ratio:g} * {lean} library additions = {ratio * lean:g}"
    ] if lean and prose > ratio * lean else []


def changelog_section(contents: str) -> list[str]:
    lines = contents.splitlines()
    start = next((i for i, line in enumerate(lines) if line.strip() == "## Unreleased"), None)
    if start is None:
        return []
    end = next((i for i in range(start + 1, len(lines)) if lines[i].startswith("## ")), len(lines))
    return lines[start:end]


def capped_lines(path: str, contents: str) -> int:
    return len(changelog_section(contents)) if path == "CHANGELOG.md" else len(contents.splitlines())


def added_head_lines(before: list[str], after: list[str]) -> set[int]:
    """Zero-based head indices introduced by a line-oriented comparison."""
    indices = set()
    for tag, _i1, _i2, j1, j2 in SequenceMatcher(None, before, after).get_opcodes():
        if tag in ("insert", "replace"):
            indices.update(range(j1, j2))
    return indices


def changelog_entry_ranges(section: list[str]) -> list[range]:
    starts = [i for i, line in enumerate(section) if line.startswith("- ")]
    return [range(start, starts[i + 1] if i + 1 < len(starts) else len(section))
            for i, start in enumerate(starts)]


def over_cap_changelog_growth_allowed(before: str, after: str, cap: int) -> bool:
    old = changelog_section(before)
    new = changelog_section(after)
    if len(new) <= len(old):
        return True
    if len(new) - len(old) > 12:
        return False
    added = added_head_lines(old, new)
    containing = [entry for entry in changelog_entry_ranges(new) if added.intersection(entry)]
    return (
        bool(added)
        and len(containing) == 1
        and added.issubset(set(containing[0]))
        and len(containing[0]) <= 12
    )


def check_growth_caps(base: dict[str, str], head: dict[str, str]) -> list[str]:
    errors = []
    for path, cap in CAPS.items():
        before = capped_lines(path, base.get(path, ""))
        after = capped_lines(path, head.get(path, ""))
        if path == "CHANGELOG.md" and before > cap:
            permitted = over_cap_changelog_growth_allowed(
                base.get(path, ""), head.get(path, ""), cap,
            )
        elif path == "docs/current-status.md" and before > cap:
            # The rolling receipt is replaced in place; a replacement may net a
            # few lines, but the page must not keep accumulating checkpoints.
            permitted = after <= before + STATUS_REPLACEMENT_SLACK
        else:
            permitted = after <= max(cap, before)
        if not permitted:
            if path == "CHANGELOG.md" and before > cap:
                suffix = "; over-cap ranges may add one entry of at most 12 lines"
            elif path == "docs/current-status.md" and before > cap:
                suffix = f"; over-cap receipt replacements may net at most {STATUS_REPLACEMENT_SLACK} lines"
            else:
                suffix = ""
            errors.append(f"(e) {path}{' ## Unreleased' if path == 'CHANGELOG.md' else ''}: {before} -> {after} lines; cap {cap}{suffix}")
    return errors


def maintenance_notes(base: dict[str, str]) -> list[str]:
    lines = capped_lines("CHANGELOG.md", base.get("CHANGELOG.md", ""))
    if lines > CAPS["CHANGELOG.md"]:
        return [f"Maintenance note: fold the oldest entries of the {lines:,}-line CHANGELOG.md ## Unreleased section into their family entries in a docs-only commit."]
    return []


def theorem_mentions(theorems: list[Theorem]) -> set[str]:
    return {name for t in theorems for name in (t.name, t.name.rsplit(".", 1)[-1])}


def check_one_place(theorems: list[Theorem], head: dict[str, str]) -> list[str]:
    errors = []
    for name in sorted(theorem_mentions(theorems)):
        pattern = re.compile(r"(?<![\w'!?])" + re.escape(name) + r"(?![\w'!?])")
        for path, contents in sorted(head.items()):
            if path.endswith(".lean") or path.startswith("scripts/") or path in THEOREM_HOMES:
                continue
            match = pattern.search(contents)
            if match:
                line = contents.count("\n", 0, match.start()) + 1
                errors.append(f"(f) new public theorem {name!r} appears in {path}:{line}; permitted prose homes: {', '.join(sorted(THEOREM_HOMES))}")
    return errors


def git(*args: str, allowed_codes: tuple[int, ...] = (0,)) -> str:
    result = subprocess.run(["git", *args], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if result.returncode not in allowed_codes:
        raise RuntimeError(result.stderr.decode("utf-8", errors="replace").strip() or f"git exited {result.returncode}")
    return result.stdout.decode("utf-8", errors="replace")


def file_at(ref: str, path: str, inventory: set[str]) -> str:
    return git("show", f"{ref}:{path}") if path in inventory else ""


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--base", default="origin/main")
    parser.add_argument("--head", default="HEAD")
    parser.add_argument("--max-new-modules", type=int, default=1)
    parser.add_argument("--prose-ratio", type=float, default=0.5)
    parser.add_argument("--explain", action="store_true")
    args = parser.parse_args(argv)
    if args.max_new_modules < 0 or not math.isfinite(args.prose_ratio) or args.prose_ratio < 0:
        parser.error("module limit and prose ratio must be finite and nonnegative")
    try:
        base = git("rev-parse", "--verify", "--end-of-options", f"{args.base}^{{commit}}").strip()
        head = git("rev-parse", "--verify", "--end-of-options", f"{args.head}^{{commit}}").strip()
        options = ("--no-renames", "--no-ext-diff", "--no-textconv")
        numstat = parse_numstat(git("diff", *options, "--numstat", "-z", base, head, "--"))
        diffs = parse_diff(git("diff", *options, "--no-color", "--unified=3", base, head, "--"))
        base_paths = set(git("ls-tree", "-r", "--name-only", "-z", base).split("\0"))
        head_paths = set(git("ls-tree", "-r", "--name-only", "-z", head).split("\0"))
        paths = set(CAPS) | {p for p in numstat if p.endswith(".lean")}
        before = {p: file_at(base, p, base_paths) for p in paths}
        after = {p: file_at(head, p, head_paths) for p in paths}
        theorems = new_theorems(diffs, before, after)
        names = sorted(theorem_mentions(theorems))
        # Scan the entire tracked head, not just added prose, without loading
        # every artifact. grep is only a candidate filter; pure rule (f) checks
        # identifier boundaries and the allowed homes below.
        for offset in range(0, len(names), 100):
            patterns = [arg for name in names[offset:offset + 100] for arg in ("-e", name)]
            matches = git("grep", "-I", "-l", "-z", "-F", *patterns, head, "--", allowed_codes=(0, 1))
            for match in filter(None, matches.split("\0")):
                path = match.split(":", 1)[1]
                if path not in after and not path.endswith(".lean") and not path.startswith("scripts/"):
                    after[path] = file_at(head, path, head_paths)
        errors = (
            check_module_paths(diffs) + check_module_count(diffs, args.max_new_modules)
            + check_theorem_names(theorems) + check_prose_budget(numstat, args.prose_ratio)
            + check_growth_caps(before, after) + check_one_place(theorems, after)
        )
        lean, prose = line_totals(numstat)
        if args.explain:
            print("Rules: (a) path suffix <=40; (b) new-file limit; (c) written public theorem name <=60;")
            print("(d) net prose growth budget (skipped with zero library additions); (e) max(base, cap),")
            print("with one over-cap Unreleased entry of at most 12 lines allowed per range and an")
            print(f"over-cap current-status receipt replacement netting at most {STATUS_REPLACEMENT_SLACK} lines;")
            print("(f) new theorem names across all tracked head text, except Lean, scripts and four prose homes.")
            for path, cap in CAPS.items():
                print(f"  {path}: {capped_lines(path, before[path])} -> {capped_lines(path, after[path])} (cap {cap})")
            for note in maintenance_notes(before):
                print(note)
        if errors:
            print("Convergence check failed:", file=sys.stderr)
            for error in errors:
                print(f"  {error}", file=sys.stderr)
            return 1
        modules = sum(d.new and d.path.startswith("ProofNetIR/") for d in diffs)
        print(f"Convergence check passed: {modules} new modules, {len(theorems)} new public theorems, {lean} library lines added, {prose} prose lines net growth" + (" (prose budget skipped)." if not lean else "."))
        return 0
    except (RuntimeError, ValueError, OSError) as error:
        print(f"Convergence check error: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
