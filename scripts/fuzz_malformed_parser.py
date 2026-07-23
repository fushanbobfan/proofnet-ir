#!/usr/bin/env python3
"""Deterministic malformed-input fuzzing for the native Lean JSON boundary."""

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
    candidate = Path.home() / ".elan" / "bin" / ("lake.exe" if os.name == "nt" else "lake")
    if candidate.exists():
        return str(candidate)
    raise RuntimeError("lake executable not found")


def nested_formula(depth: int) -> str:
    formula = '{"kind":"atom","name":"deep","positive":true}'
    for _ in range(depth):
        formula = f'{{"kind":"tensor","left":{formula},"right":{{"kind":"atom","name":"r","positive":false}}}}'
    return (
        '{"version":"0.3","canonical":true,"canonicalization":"reindex-v1",'
        f'"formulas":[{formula}],"links":[],"conclusions":[0]}}'
    )


def mutate_cases(
    valid: str, initial: list[str], seed: int
) -> list[str]:
    cases = list(initial)
    alphabet = '{}[],:"\\0123456789truefalsenullxyz'
    state = seed
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


def generated_cases(valid: str) -> list[str]:
    initial = [
        "null",
        "{}",
        "[]",
        '"certificate"',
        '{"version":"0.3"}',
        '{"version":3,"canonical":true}',
        '{"version":"9.9","canonical":true}',
        '{"version":"0.3","canonical":true,"canonicalization":"unknown",'
        '"formulas":[],"links":[],"conclusions":[]}',
        '{"version":"0.3","canonical":true,"canonicalization":"reindex-v1",'
        '"formulas":[{"kind":"atom","name":"","positive":true}],'
        '"links":[],"conclusions":[0]}',
        nested_formula(1_025),
    ]
    return mutate_cases(valid, initial, 0x5EED_C0DE)


def canonical_key_cases(valid: str) -> list[str]:
    initial = [
        "null",
        "{}",
        "[]",
        '"canonical-key"',
        '{"version":"proofnet-canonical-key-0.1"}',
        '{"version":3,"canonicalization":"proofnet-equivalent-v1","tokens":[]}',
        '{"version":"wrong","canonicalization":"proofnet-equivalent-v1","tokens":["x"]}',
        '{"version":"proofnet-canonical-key-0.1","canonicalization":"wrong","tokens":["x"]}',
        '{"version":"proofnet-canonical-key-0.1","canonicalization":"proofnet-equivalent-v1","tokens":[]}',
        '{"version":"proofnet-canonical-key-0.1","canonicalization":"proofnet-equivalent-v1","tokens":[1]}',
    ]
    return mutate_cases(valid, initial, 0xC0DE_0A71)


def intrinsic_canonical_key_cases(valid: str) -> list[str]:
    initial = [
        "null",
        "{}",
        "[]",
        '"intrinsic-canonical-key"',
        '{"version":"proofnet-canonical-key-0.2"}',
        '{"version":3,"canonicalization":"proofnet-equivalent-intrinsic-v1","tokens":[]}',
        '{"version":"wrong","canonicalization":"proofnet-equivalent-intrinsic-v1","tokens":["x"]}',
        '{"version":"proofnet-canonical-key-0.2","canonicalization":"wrong","tokens":["x"]}',
        '{"version":"proofnet-canonical-key-0.2","canonicalization":"proofnet-equivalent-intrinsic-v1","tokens":[]}',
        '{"version":"proofnet-canonical-key-0.2","canonicalization":"proofnet-equivalent-intrinsic-v1","tokens":[1]}',
    ]
    return mutate_cases(valid, initial, 0x1A71_2026)


def main() -> None:
    fixture = (ROOT / "examples" / "canonical-v0.3.json").read_text(encoding="utf-8")
    valid = json.dumps(json.loads(fixture), separators=(",", ":"), ensure_ascii=False)
    cases = generated_cases(valid)
    completed = subprocess.run(
        [find_lake(), "exe", "proofnet_ir_parser_fuzz"],
        cwd=ROOT,
        input="\n".join(cases) + "\n",
        capture_output=True,
        text=True,
        encoding="utf-8",
        check=True,
    )
    output = completed.stdout.strip()
    expected = f"parser-fuzz-ok cases={TARGET_CASES}"
    if expected not in output:
        raise RuntimeError(f"unexpected fuzz harness output: {output!r}")
    print(output)

    key_fixture = (
        ROOT / "examples" / "canonical-key-v0.1.json"
    ).read_text(encoding="utf-8")
    valid_key = json.dumps(
        json.loads(key_fixture), separators=(",", ":"), ensure_ascii=False
    )
    key_inputs = canonical_key_cases(valid_key)
    key_completed = subprocess.run(
        [find_lake(), "exe", "proofnet_ir_parser_fuzz", "--canonical-key"],
        cwd=ROOT,
        input="\n".join(key_inputs) + "\n",
        capture_output=True,
        text=True,
        encoding="utf-8",
        check=True,
    )
    key_output = key_completed.stdout.strip()
    key_expected = f"canonical-key-parser-fuzz-ok cases={TARGET_CASES}"
    if key_expected not in key_output:
        raise RuntimeError(
            f"unexpected canonical-key fuzz harness output: {key_output!r}"
        )
    print(key_output)

    intrinsic_key_fixture = (
        ROOT / "examples" / "canonical-key-v0.2.json"
    ).read_text(encoding="utf-8")
    valid_intrinsic_key = json.dumps(
        json.loads(intrinsic_key_fixture),
        separators=(",", ":"),
        ensure_ascii=False,
    )
    intrinsic_key_inputs = intrinsic_canonical_key_cases(valid_intrinsic_key)
    intrinsic_key_completed = subprocess.run(
        [
            find_lake(),
            "exe",
            "proofnet_ir_parser_fuzz",
            "--intrinsic-canonical-key",
        ],
        cwd=ROOT,
        input="\n".join(intrinsic_key_inputs) + "\n",
        capture_output=True,
        text=True,
        encoding="utf-8",
        check=True,
    )
    intrinsic_key_output = intrinsic_key_completed.stdout.strip()
    intrinsic_key_expected = (
        f"intrinsic-canonical-key-parser-fuzz-ok cases={TARGET_CASES}"
    )
    if intrinsic_key_expected not in intrinsic_key_output:
        raise RuntimeError(
            "unexpected intrinsic canonical-key fuzz harness output: "
            f"{intrinsic_key_output!r}"
        )
    print(intrinsic_key_output)


if __name__ == "__main__":
    main()
