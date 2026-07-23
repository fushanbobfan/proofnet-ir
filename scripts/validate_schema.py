"""Validate the versioned ProofNet-IR JSON contract and checked-in fixtures."""

from __future__ import annotations

import json
from pathlib import Path

from jsonschema import Draft202012Validator


ROOT = Path(__file__).resolve().parents[1]


def main() -> None:
    schemas: dict[str, dict] = {}
    for schema_path in sorted((ROOT / "schemas").glob("*.schema.json")):
        schema = json.loads(schema_path.read_text(encoding="utf-8"))
        Draft202012Validator.check_schema(schema)
        schemas[schema_path.name] = schema
        print(f"schema-definition-valid: {schema_path.name}")

    fixtures = {
        "canonical.json": "certificate-v0.1.schema.json",
        "canonical-v0.3.json": "certificate-v0.3.schema.json",
        "canonical-key-v0.1.json": "canonical-key-v0.1.schema.json",
        "invalid-disconnected.json": "certificate-v0.1.schema.json",
        "focused-sequent-v0.2.json": "sequent-v0.2.schema.json",
        "leanprop-identity-v0.1.json": "leanprop-schema-v0.1.schema.json",
        "leanprop-invalid-projection-v0.1.json": "leanprop-schema-v0.1.schema.json",
    }
    for fixture_name, schema_name in fixtures.items():
        fixture = ROOT / "examples" / fixture_name
        value = json.loads(fixture.read_text(encoding="utf-8"))
        Draft202012Validator(schemas[schema_name]).validate(value)
        print(f"schema-valid: {fixture.name}")


if __name__ == "__main__":
    main()
