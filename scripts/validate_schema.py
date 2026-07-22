"""Validate the versioned ProofNet-IR JSON contract and checked-in fixtures."""

from __future__ import annotations

import json
from pathlib import Path

from jsonschema import Draft202012Validator


ROOT = Path(__file__).resolve().parents[1]


def main() -> None:
    schema_path = ROOT / "schemas" / "certificate-v0.1.schema.json"
    schema = json.loads(schema_path.read_text(encoding="utf-8"))
    Draft202012Validator.check_schema(schema)
    validator = Draft202012Validator(schema)

    fixtures = sorted((ROOT / "examples").glob("*.json"))
    if not fixtures:
        raise RuntimeError("no JSON fixtures found")

    for fixture in fixtures:
        value = json.loads(fixture.read_text(encoding="utf-8"))
        validator.validate(value)
        print(f"schema-valid: {fixture.name}")


if __name__ == "__main__":
    main()
