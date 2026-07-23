#!/usr/bin/env python3
"""Deterministic mutation fuzzing for the native LeanProp schema boundary."""

from __future__ import annotations

import json
import os
from pathlib import Path
import shutil
import subprocess


ROOT = Path(__file__).resolve().parents[1]
TARGET_CASES = 5_000


def find_lake() -> str:
    discovered = shutil.which("lake")
    if discovered:
        return discovered
    executable = "lake.exe" if os.name == "nt" else "lake"
    candidate = Path.home() / ".elan" / "bin" / executable
    if candidate.exists():
        return str(candidate)
    raise RuntimeError("lake executable not found")


def nested_derivation(depth: int) -> str:
    formula = '{"kind":"atom","name":"deep"}'
    derivation = f'{{"kind":"persistent-axiom","formula":{formula}}}'
    for _ in range(depth):
        derivation = (
            '{"kind":"persistent-weaken","extra":'
            f'{formula},"premise":{derivation}}}'
        )
    return (
        '{"version":"leanprop-schema-0.1","derivation":'
        f'{derivation}}}'
    )


def generated_cases(valid: str) -> list[str]:
    cases = [
        "null",
        "{}",
        "[]",
        '"schema"',
        '{"version":"leanprop-schema-0.1"}',
        '{"version":1,"derivation":{}}',
        '{"version":"wrong","derivation":{}}',
        '{"version":"leanprop-schema-0.1","derivation":{"kind":"unknown"}}',
        '{"version":"leanprop-schema-0.1","extra":true,"derivation":{}}',
        nested_derivation(2_049),
    ]
    alphabet = '{}[],:"\\0123456789truefalsenullxyz-'
    state = 0x1EA4_0F01
    while len(cases) < TARGET_CASES:
        state = (1_664_525 * state + 1_013_904_223) & 0xFFFF_FFFF
        position = state % len(valid)
        operation = (state >> 8) % 6
        replacement = alphabet[(state >> 16) % len(alphabet)]
        if operation == 0:
            mutated = valid[:position] + valid[position + 1 :]
        elif operation == 1:
            mutated = valid[:position] + replacement + valid[position + 1 :]
        elif operation == 2:
            mutated = valid[:position] + replacement + valid[position:]
        elif operation == 3:
            mutated = valid[: position + 1]
        elif operation == 4:
            width = 1 + ((state >> 20) % min(31, len(valid) - position))
            mutated = valid[:position] + valid[position + width :]
        else:
            width = 1 + ((state >> 20) % min(31, len(valid) - position))
            mutated = (
                valid[:position]
                + f'"fuzz-{state:08x}"'
                + valid[position + width :]
            )
        if mutated and "\n" not in mutated and "\r" not in mutated:
            cases.append(mutated)
    return cases[:TARGET_CASES]


def main() -> None:
    fixture = (ROOT / "examples" / "leanprop-identity-v0.1.json").read_text(
        encoding="utf-8"
    )
    valid = json.dumps(json.loads(fixture), separators=(",", ":"), ensure_ascii=False)
    cases = generated_cases(valid)
    completed = subprocess.run(
        [find_lake(), "exe", "proofnet_ir_leanprop_parser_fuzz"],
        cwd=ROOT,
        input="\n".join(cases) + "\n",
        capture_output=True,
        text=True,
        encoding="utf-8",
        check=True,
    )
    output = completed.stdout.strip()
    expected = f"leanprop-parser-fuzz-ok cases={TARGET_CASES}"
    if expected not in output:
        raise RuntimeError(f"unexpected LeanProp fuzz harness output: {output!r}")
    print(output)


if __name__ == "__main__":
    main()
