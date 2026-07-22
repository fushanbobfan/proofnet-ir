#!/usr/bin/env python3
"""Independent property audit for the v0.3 reindex-v1 wire key."""

from __future__ import annotations

import copy
import json
import random
from pathlib import Path

from jsonschema import Draft202012Validator


ROOT = Path(__file__).resolve().parents[1]
DATASET = ROOT / "datasets" / "v0.2" / "certificates.jsonl"
SCHEMA = ROOT / "schemas" / "certificate-v0.3.schema.json"


def link_vertices(link: dict[str, object]) -> list[int]:
    vertices = [int(link["left"]), int(link["right"])]
    if link["kind"] != "axiom":
        vertices.append(int(link["conclusion"]))
    return vertices


def reindex_v1(certificate: dict[str, object]) -> dict[str, object]:
    submitted = list(certificate["conclusions"])
    for link in certificate["links"]:
        submitted.extend(link_vertices(link))

    order: list[int] = []
    seen: set[int] = set()
    for vertex in submitted:
        vertex = int(vertex)
        if vertex not in seen:
            seen.add(vertex)
            order.append(vertex)
    rename = {vertex: index for index, vertex in enumerate(order)}

    formulas = certificate["formulas"]
    normalized_formulas = [
        copy.deepcopy(formulas[vertex])
        for vertex in order
        if 0 <= vertex < len(formulas)
    ]
    normalized_links: list[dict[str, object]] = []
    for link in certificate["links"]:
        normalized = {"kind": link["kind"]}
        normalized["left"] = rename[int(link["left"])]
        normalized["right"] = rename[int(link["right"])]
        if link["kind"] != "axiom":
            normalized["conclusion"] = rename[int(link["conclusion"])]
        normalized_links.append(normalized)

    return {
        "version": "0.3",
        "canonical": True,
        "canonicalization": "reindex-v1",
        "formulas": normalized_formulas,
        "links": normalized_links,
        "conclusions": [rename[int(vertex)] for vertex in certificate["conclusions"]],
    }


def permute_vertices(
    certificate: dict[str, object], permutation: list[int]
) -> dict[str, object]:
    result = copy.deepcopy(certificate)
    formulas = certificate["formulas"]
    result["formulas"] = [None] * len(formulas)
    for old, new in enumerate(permutation):
        result["formulas"][new] = copy.deepcopy(formulas[old])
    for link in result["links"]:
        link["left"] = permutation[int(link["left"])]
        link["right"] = permutation[int(link["right"])]
        if link["kind"] != "axiom":
            link["conclusion"] = permutation[int(link["conclusion"])]
    result["conclusions"] = [
        permutation[int(vertex)] for vertex in result["conclusions"]
    ]
    return result


def canonical_payload(normalized: dict[str, object]) -> dict[str, object]:
    return {
        "formulas": normalized["formulas"],
        "links": normalized["links"],
        "conclusions": normalized["conclusions"],
    }


def main() -> None:
    schema = json.loads(SCHEMA.read_text(encoding="utf-8"))
    validator = Draft202012Validator(schema)
    records = [
        json.loads(line)
        for line in DATASET.read_text(encoding="utf-8").splitlines()
        if line
    ]
    if len(records) != 1_000:
        raise AssertionError(f"expected 1000 records, got {len(records)}")

    order_sensitive_cases = 0
    for index, record in enumerate(records):
        certificate = record["certificate"]
        normalized = reindex_v1(certificate)
        validator.validate(normalized)

        rng = random.Random(index)
        permutation = list(range(len(certificate["formulas"])))
        rng.shuffle(permutation)
        permuted = permute_vertices(certificate, permutation)
        if reindex_v1(permuted) != normalized:
            raise AssertionError(f"reindex invariance failed for {record['id']}")

        renormalized = reindex_v1(canonical_payload(normalized))
        if renormalized != normalized:
            raise AssertionError(f"idempotence failed for {record['id']}")

        if len(certificate["links"]) >= 2:
            reordered = copy.deepcopy(certificate)
            reordered["links"].reverse()
            if reordered == certificate:
                raise AssertionError(
                    f"link reversal did not change certificate {record['id']}"
                )
            if reindex_v1(reordered) != normalized:
                order_sensitive_cases += 1

    if order_sensitive_cases != 1_000:
        raise AssertionError(
            "link-order sensitivity was not observed for every dataset record: "
            f"{order_sensitive_cases}/1000"
        )
    print(
        "v0.3-canonical-audit-valid: 1000 reindex-invariant, schema-valid, "
        "idempotent, and link-order-sensitive records"
    )


if __name__ == "__main__":
    main()
