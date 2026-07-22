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

The unreleased v0.5 development line adds
`Certificate.sequentialize`, `ExecutableSequentializationResult`, and
`SequentializationError` without changing either wire payload. These APIs are
additive, but their names and error-stage vocabulary remain pre-release until a
v0.5 tag is cut. The result's `ReindexEquivalent` field preserves the narrower
order-sensitive v0.3 identity contract; it does not introduce arbitrary graph
isomorphism or reorder link/conclusion lists.

## Deprecation and release checks

A public API scheduled for removal will remain for at least one tagged minor
release when technically possible. CI builds a path-based downstream consumer
and a clean consumer pinned to the latest public release. Schema fixtures,
round trips, migration tests, and the independent property audit are release
gates.
