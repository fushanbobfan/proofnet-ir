# Compatibility policy

## Lean API

ProofNet-IR uses semantic versioning for tagged releases. Until 1.0, a minor
release may make source-incompatible Lean API changes when the changelog names
them and a migration is documented. Patch releases must not intentionally
change accepted-certificate semantics or wire output. Every release pins its
Lean toolchain in `lean-toolchain`; consumers should use the same toolchain or
test their own explicitly.

## Wire API

Wire versions are independent, explicit contracts. Existing version markers
are never silently reinterpreted:

- v0.2 fixes formula-array indices as vertex identity and normalizes link
  order, conclusion order, and symmetric axiom orientation;
- v0.3 `reindex-v1` removes bounded submitted vertex names while preserving
  all list and premise orders described in `docs/v0.3-design.md`.

The generic parser accepts every supported version. Version-specific parsers
remain available for migration boundaries. The v0.2-to-v0.3 migration parses
and validates the source normal form before emitting a v0.3 string. Future
canonicalization algorithms must use a new `canonicalization` value and, when
the payload contract changes, a new wire version.

Release v0.4.0 adds the general sequentialization Lean API and theorem without
introducing a new wire version or changing the v0.2/v0.3 payload contracts.
`Certificate.sequentialization_of_check` and
`Certificate.generallySequentializable` are additive public declarations.

The post-v0.5 additive `CheckedCertificate.sameProofNet?` API wraps the same
`ProofNetEquivalent` semantics in a checker-accepted input type. Integrating
ordered-conclusion constraints into candidate generation changes performance,
not accepted-certificate semantics or v0.2/v0.3 wire output.

Release v0.5.0 adds
`Certificate.sequentialize`, `ExecutableSequentializationResult`, and
`SequentializationError` without changing either wire payload. These APIs are
additive. The result carries v0.4 `ProofNetEquivalent`: a bounded vertex
renaming followed by semantically irrelevant link-list permutation, while the
ordered conclusion boundary is still preserved. This is broader than the
order-sensitive v0.3 `ReindexEquivalent` key but remains narrower than
arbitrary graph isomorphism and never reorders conclusions or connective
premises. v0.5.0 also exposes `proofNetCanonicalFamily` as a factorial
specification oracle with a complete iff theorem; it does not introduce a new
wire version or promise a compact canonical representative.

## Deprecation and release checks

A public API scheduled for removal will remain for at least one tagged minor
release when technically possible. CI builds a path-based downstream consumer
and a clean consumer pinned to the latest public release. Schema fixtures,
round trips, migration tests, and the independent property audit are release
gates.
