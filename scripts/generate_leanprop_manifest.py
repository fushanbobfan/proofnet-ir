#!/usr/bin/env python3
"""Hash the Lean-emitted LeanProp corpus without reimplementing its labels."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess


ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "datasets" / "leanprop-v0.1" / "manifest.json"


def find_lake() -> str:
    discovered = shutil.which("lake")
    if discovered:
        return discovered
    executable = "lake.exe" if os.name == "nt" else "lake"
    candidate = Path.home() / ".elan" / "bin" / executable
    if candidate.exists():
        return str(candidate)
    raise RuntimeError("lake executable not found")


def calculate() -> dict[str, object]:
    completed = subprocess.run(
        [find_lake(), "exe", "proofnet_ir_leanprop_corpus_export"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        encoding="utf-8",
        check=True,
    )
    lines = [line for line in completed.stdout.splitlines() if line.startswith("{")]
    records = [json.loads(line) for line in lines]
    positives = sum(record["expected"] == "accepted" for record in records)
    negatives = sum(record["expected"] == "rejected" for record in records)
    if (positives, negatives) != (600, 1_000):
        raise RuntimeError(
            f"unexpected Lean corpus counts: positives={positives}, negatives={negatives}"
        )
    payload = ("\n".join(lines) + "\n").encode("utf-8")
    return {
        "format": "proofnet-ir-leanprop-corpus-manifest-v0.1",
        "wire_version": "leanprop-schema-0.1",
        "generator": "ProofNetIRLeanPropCorpusExport.lean",
        "record_count": len(records),
        "positive_count": positives,
        "negative_count": negatives,
        "sha256": hashlib.sha256(payload).hexdigest(),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--print", action="store_true", dest="print_manifest")
    args = parser.parse_args()
    generated = calculate()
    rendered = json.dumps(generated, indent=2, sort_keys=True) + "\n"
    if args.print_manifest:
        print(rendered, end="")
        return
    if not args.check:
        raise SystemExit("use --check or --print")
    existing = json.loads(MANIFEST.read_text(encoding="utf-8"))
    if existing != generated:
        raise RuntimeError(
            "LeanProp corpus manifest is stale:\n"
            f"expected={json.dumps(existing, sort_keys=True)}\n"
            f"actual={json.dumps(generated, sort_keys=True)}"
        )
    print(
        "LeanProp corpus manifest current: "
        f"records={generated['record_count']} sha256={generated['sha256']}"
    )


if __name__ == "__main__":
    main()
