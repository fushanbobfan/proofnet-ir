# ProofNet-IR v0.2 dataset

`certificates.jsonl` contains exactly 1,000 deterministic records:

- 250 positive certificates desequentialized from generated cut-free MLL
  derivation trees;
- 250 missing-link negatives;
- 250 duplicated-resource negatives;
- 250 self-axiom negatives.

Every label is computed by the compiled Lean reference checker and then
independently recomputed by the Python certificate/union-find oracle. The
manifest records the byte-level SHA-256 digest and provenance counts.

Regenerate or verify from the repository root:

```powershell
python scripts/generate_dataset.py --write
python scripts/generate_dataset.py --check
```

The certificate payload follows `schemas/certificate-v0.2.schema.json`.
Canonical v0.2 serialization keeps formula-array indices as occurrence
identities and normalizes link order, conclusion order, and symmetric axiom
orientation. It does not claim invariance under arbitrary vertex renaming or
proof-net graph isomorphism.
