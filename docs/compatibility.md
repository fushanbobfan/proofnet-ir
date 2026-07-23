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

The independent `leanprop-schema-0.1` marker names the first raw LeanProp
template contract. It covers named atoms, ordinary conjunction/implication,
explicit persistent structural rules, exchange witnesses, and linear rule
syntax. It is not a certificate wire version and does not reinterpret MLL
tensor/par. Later LeanProp payload changes require a new explicit marker and
migration tests; typed equality and quantifier terms are outside v0.1.
The v0.6.0 `CheckedDerivation` API is intentionally typed: successful
checking retains an indexed derivation and exposes `toPacked`/`sound`. This API
is additive to the MLL certificate API and is compatibility-stable within the
v0.6 minor line under the policy above.
The additive `normalizePersistentStructural` API is under the same
v0.6 stability boundary; its theorem scope is the explicit
contraction-over-weakening normal form, not arbitrary proof-term equivalence,
and the function is not a runtime raw-schema transformer.

The generic parser accepts every supported version. Version-specific parsers
remain available for migration boundaries. The v0.2-to-v0.3 migration parses
and validates the source normal form before emitting a v0.3 string. Future
canonicalization algorithms must use a new `canonicalization` value and, when
the payload contract changes, a new wire version.

The unreleased `proofNetCanonicalFingerprint?` is a Lean-level experimental
value, not a wire contract. It takes the least existing v0.3 string across the
finite `ProofNetEquivalent` family and has a forward invariance theorem.
The separate `proofNetCanonicalCode?` token value uses an explicitly versioned,
proved-injective structural encoder; code equality is proved equivalent to
`ProofNetEquivalent` on structurally well-formed or checker-accepted inputs.
The JSON fingerprint is not a wire contract. The typed code now has the
separate `proofnet-canonical-key-0.1` /
`proofnet-equivalent-v1` wire wrapper, bounded parser, schema, and semantic
migration from checker-accepted v0.3 certificates. Existing v0.2/v0.3 strings
are not reinterpreted. The new wire remains unreleased. Its generator and
parsed-key matcher check a seven-link ceiling before materializing the
factorial family; inputs above that limit fail closed. Changing that ceiling is
a documented resource-policy change, while changing the relation or payload
requires the versioning rules above.

Release v0.4.0 adds the general sequentialization Lean API and theorem without
introducing a new wire version or changing the v0.2/v0.3 payload contracts.
`Certificate.sequentialization_of_check` and
`Certificate.generallySequentializable` are additive public declarations.

The post-v0.5 additive `CheckedCertificate.sameProofNet?` API wraps the same
`ProofNetEquivalent` semantics in a checker-accepted input type. Integrating
ordered-conclusion constraints into candidate generation changes performance,
not accepted-certificate semantics or v0.2/v0.3 wire output.
These changes are released as v0.5.1 together with the additive
derivation-first soundness theorems; the package metadata now matches the
release tag.

Release v0.5.2 adds a proved numeric-free local-incidence constraint to the
existing exact `ProofNetEquivalent` search. The new theorem shows every direct
equivalence witness survives the filter, so this is a performance change, not
an identity, accepted-certificate, or wire-format change. The model-experiment
runner, amendment, raw responses, results, and report are research artifacts
and do not alter the Lean or JSON API.

Release v0.6.0 adds the separate persistent/linear LeanProp derivation,
`leanprop-schema-0.1` checked wire boundary, typed elaboration and universal
soundness API, proof-relevant exchange completeness, and scoped persistent
structural normalization. It does not change MLL certificate acceptance,
v0.2/v0.3 serialization, or `ProofNetEquivalent`, and it does not identify
ordinary Lean conjunction/implication with MLL tensor/par.

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
release when technically possible. CI builds a path-based downstream consumer,
a clean consumer pinned to the latest public release, and a separate clean
consumer pinned to the exact public v0.6 API revision. The final v0.6 release
gate changes that consumer to the public `v0.6.0` tag and rebuilds it before
the GitHub release is created. Schema fixtures, round trips, applicable
migration tests, and the independent property audit are release gates.
