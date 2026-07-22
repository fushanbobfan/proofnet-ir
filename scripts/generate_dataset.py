#!/usr/bin/env python3
"""Regenerate or verify the deterministic v0.2 checker-labeled dataset."""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
from collections import Counter
from pathlib import Path

from jsonschema import Draft202012Validator

from audit_v010 import LAKE, ROOT, independent_certificate_check


DATASET_DIR = ROOT / "datasets" / "v0.2"
DATASET_PATH = DATASET_DIR / "certificates.jsonl"
MANIFEST_PATH = DATASET_DIR / "manifest.json"
CERTIFICATE_SCHEMA_PATH = ROOT / "schemas" / "certificate-v0.2.schema.json"
RECORD_SCHEMA_PATH = ROOT / "schemas" / "dataset-record-v0.2.schema.json"


def generate_payload() -> tuple[str, dict[str, object]]:
    completed = subprocess.run(
        [LAKE, "exe", "proofnet_ir_dataset"],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
        encoding="utf-8",
    )
    lines = completed.stdout.splitlines()
    if len(lines) != 1_000:
        raise AssertionError(f"expected exactly 1000 records, got {len(lines)}")

    certificate_schema = json.loads(CERTIFICATE_SCHEMA_PATH.read_text(encoding="utf-8"))
    record_schema = json.loads(RECORD_SCHEMA_PATH.read_text(encoding="utf-8"))
    record_schema["properties"]["certificate"] = certificate_schema
    validator = Draft202012Validator(record_schema)

    ids: set[str] = set()
    labels: Counter[bool] = Counter()
    provenances: Counter[str] = Counter()
    for line_number, line in enumerate(lines, start=1):
        record = json.loads(line)
        validator.validate(record)
        if record["id"] in ids:
            raise AssertionError(f"duplicate id at line {line_number}: {record['id']}")
        ids.add(record["id"])
        label = bool(record["label"])
        oracle = independent_certificate_check(record["certificate"])
        if label != oracle:
            raise AssertionError(
                f"oracle disagreement at {record['id']}: Lean={label}, oracle={oracle}"
            )
        if (record["provenance"] == "valid-derivation") != label:
            raise AssertionError(f"unexpected label/provenance pair: {record['id']}")
        labels[label] += 1
        provenances[record["provenance"]] += 1

    expected_provenances = {
        "valid-derivation": 250,
        "missing-link": 250,
        "duplicated-resource": 250,
        "self-axiom": 250,
    }
    if labels != Counter({False: 750, True: 250}):
        raise AssertionError(f"unexpected label counts: {dict(labels)}")
    if dict(provenances) != expected_provenances:
        raise AssertionError(f"unexpected provenance counts: {dict(provenances)}")

    payload = "\n".join(lines) + "\n"
    manifest: dict[str, object] = {
        "version": "0.2",
        "records": 1_000,
        "positive": 250,
        "negative": 750,
        "sha256": hashlib.sha256(payload.encode("utf-8")).hexdigest(),
        "generator": "lake exe proofnet_ir_dataset",
        "independentOracle": "scripts/audit_v010.py",
        "provenanceCounts": expected_provenances,
    }
    return payload, manifest


def main() -> int:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args()

    payload, manifest = generate_payload()
    manifest_text = json.dumps(manifest, indent=2, sort_keys=True) + "\n"
    if args.write:
        DATASET_DIR.mkdir(parents=True, exist_ok=True)
        DATASET_PATH.write_text(payload, encoding="utf-8", newline="\n")
        MANIFEST_PATH.write_text(manifest_text, encoding="utf-8", newline="\n")
        print(f"wrote {DATASET_PATH} ({manifest['sha256']})")
        return 0

    if DATASET_PATH.read_text(encoding="utf-8") != payload:
        raise AssertionError("committed dataset differs from deterministic generator output")
    if MANIFEST_PATH.read_text(encoding="utf-8") != manifest_text:
        raise AssertionError("committed dataset manifest is stale")
    print(
        "dataset-valid: 1000 records, 250 positive, 750 negative, "
        f"sha256={manifest['sha256']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
