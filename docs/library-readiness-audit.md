# Library-readiness audit

Audit date: 2026-07-23
Audited baseline: v0.6.0 release candidate

## Verdict

ProofNet-IR v0.6.0 is a usable research prototype and reference checker. It is
not yet a mature reusable Lean library. The published checker can validate its
documented unit-free, cut-free MLL certificates; the dataset and focused-search
baseline can be reproduced. v0.5.0 proves that any accepted
certificate can be converted into a concrete first-order derivation whose
desequentialization is `ProofNetEquivalent` to the input. It also
lets a downstream consumer parse v0.2/v0.3 JSON directly into a checked Lean
object and migrate v0.2 to a reindex-invariant v0.3 key, but that closes only
part of the engineering and proof-identity gap.

## What is logically established

- involutive linear negation;
- proposition-level local link/resource semantics equivalent to the Boolean
  structural checker;
- exact enumeration of one-edge-per-par switchings;
- checker soundness for independent unbounded walk semantics;
- checker soundness and completeness for the independent fuel-indexed path
  semantics;
- after v0.2.0, loop erasure and finite vertex counting prove completeness for
  the standard unbounded walk semantics as well
  (`check_iff_declarativelyCorrect`);
- exhaustive differential agreement for all 33,868 simple graphs through six
  vertices and two separate 1,000-certificate corpora;
- exact reconstruction for the recursive identity family;
- after v0.2.0, successful first-order derivation inference denotes a genuine
  kernel-typed `Derivation` (`CutFreeDerivation.infer?_sound`).
- `CutFreeDerivation.elaborate?` returns only when the inferred sequent has a
  kernel-typed derivation, the certificate boundary labels are that same
  sequent, and the reference checker accepted the certificate.
- the post-release parser accepts the canonical serializer for all 250
  generated derivation-tree fixtures and returns the normalized certificate.
- after v0.2.0, bounded vertex reindexing is lossless and forms an explicit
  equivalence relation; structural validation, graph/tree semantics, switching
  correctness, and the final checker are invariant under it.
- v0.3 proves that every `ReindexEquivalent` certificate has the same
  `reindex-v1` serialized key; 250 generated certificates round-trip through
  the native checked parser and an independent audit exercises all 1,000
  committed records under deterministic vertex permutations.
- v0.3.1 proves structural well-formedness gives a complete traversal,
  normalization is an in-class representative, and normal-form equality is an
  iff/decision procedure for the exact order-preserving reindex relation.
- v0.4.0 defines a broader `ProofNetEquivalent` relation generated
  by bounded reindexing and link-list permutation. Lean proves that link
  permutation preserves all structural conditions, transports every par
  switching to a tree-equivalent graph, and preserves declarative correctness,
  `Correct`, and the Boolean checker.
- v0.4.0 implements checker-gated terminal-par and splitting-tensor
  inverse candidates, with 250 generated nets exposing an accepted recursive
  step; the supporting vertex-deletion graph layer now proves the complete
  theorem that deleting a leaf preserves `IsTree`. Terminal-par preservation is
  complete, and a genuine splitting tensor now produces two universally
  structurally well-formed components whose every switching is an induced
  input restriction and remains an `IsTree`. Checker/declarative preservation
  for this reduction is complete. Universal terminal-par-or-splitting-tensor
  existence, strict decrease of both reductions, and the axiom-only recursive
  base are now kernel checked. Boundary transport and well-founded logical
  recursion are also complete. Exact par/tensor occurrence reconstruction and
  inverse-rule congruence now close `sequentialization_of_check` and
  `generallySequentializable`: every accepted certificate has a concrete
  first-order tree whose executable desequentialization is
  `ProofNetEquivalent` to the input and has exactly its ordered conclusion
  formulas.
- the post-v0.4 `Certificate.sequentialize_complete` theorem closes the
  separate runtime path: finite terminal-par/splitting-tensor search, complete
  repeated-label boundary alignment, and fuel-bounded recursion return a
  proof-bearing result for every checker-accepted certificate.

## Logical gaps blocking a mature-library claim

1. Formula inference and occurrence-aware construction have a proved exact
   success-domain/boundary equivalence, including duplicate-label exchanges.
   Structural composition and all-switchings tree composition now prove every
   successful construction declaratively correct and checker-accepted;
   `desequentializeChecked?` and `elaborate?` are proved total on `infer?`
   success. The remaining logical scope gaps are units, cuts, additives,
   exponentials, and integration with the initial persistent LeanProp bridge.
   The bridge now has separate persistent/linear contexts, explicit persistent
   structural rules, ordinary Lean connective/quantifier nodes, an axiom-free
   proof-term interpreter, and an exact linear-leaf count theorem. It remains
   separate from MLL certificate semantics and lacks release-level
   qualification. A deterministic 600-template positive schema corpus,
   universal atom-valuation soundness theorem, unindexed raw checker, positive
   erasure/recovery theorem, strict versioned JSON/checker-gated parser, and
   1,000 malformed cases with exact raw/wire diagnostic expectations are now
   present. A typed structural normalizer recursively removes immediate
   persistent contraction-over-weakening redexes and has proved reducedness,
   fixed-point, idempotence, size, linear-count, and pointwise interpretation
   laws. It is noncomputable and does not normalize raw wire schemas. Equality
   and quantifier terms remain outside the wire fragment.
2. The stronger `GenerallySequentializable` result and the public executable
   totality theorem are complete for the
   documented unit-free, cut-free MLL representation. Remaining logical scope
   gaps concern unsupported connectives/units/cuts and broader notions of
   canonical graph identity, not the accepted-net reverse theorem.
3. The edge-count tree characterization is used correctly, but no explicit
   acyclicity predicate/equivalence theorem is exposed as public API.
4. A semantic relation modulo reordered links now has a complete executable
   decision procedure on structurally well-formed certificates. It now also
   has a complete executable finite canonical family: Lean proves extensional
   family membership equality iff `ProofNetEquivalent`. The family is
   factorial and is not a compact single-representative wire key.
   Conclusion-order canonicalization and arbitrary graph isomorphism remain
   outside the current claim. The v0.3.1 wire theorem remains intentionally
   about the narrower, order-preserving `ReindexEquivalent` relation.
   For accepted certificates, `CheckedCertificate.sameProofNet?` is now the
   supported production pairwise identity boundary and has an exact iff
   theorem. Ordered conclusions constrain candidate generation, reducing the
   64-pair repeated-label stress case from `(64!)^2` theoretical unconstrained
   orders to one generated candidate. Numeric-free one-hop incident-link views
   now also prune internal repeated-label alignments, with a proof that every
   direct equivalence witness survives the filter. This does not provide a
   compact wire key or a polynomial worst-case bound.

## Engineering gaps blocking a mature-library claim

- v0.2/v0.3 serialization now has a native Lean parser, path-aware parse
  errors, normalization validation, migration, and a checker-gated
  untrusted-input API;
- many older APIs return `Option`, losing the location and reason for failure;
  executable sequentialization now returns a staged `SequentializationError`;
- separate path-dependency and clean pinned-v0.5.0 Lake consumers now pass;
  the path dependency executes the v0.5 sequentializer and consumes its
  equivalence theorem, while the pinned consumer protects the v0.5.0 API. A
  third clean consumer installs the exact public v0.6 candidate Git commit
  and typechecks the retained-boundary, packed-witness, soundness, and
  persistent-normalization APIs;
- the finite direct-equivalence search is now proved complete on structurally
  well-formed left certificates, including repeated labels and link reordering;
- CI now parses `#print axioms` for twenty-five public MLL logical-boundary theorems and
  fails if their exact dependency set changes from `propext`,
  `Classical.choice`, and `Quot.sound`;
- the separate LeanProp trust boundary locks four theorems as axiom-free,
  fifteen dependent metatheorems to exactly `propext`, and four theorems to
  exactly
  `[propext, Quot.sound]`;
- an initial compatibility policy and v0.2-to-v0.3 migration suite now exist;
  long-term API documentation and deprecation automation are still incomplete;
- a curated public declaration manifest now generates types and docstrings
  from the kernel-loaded environment, fails on missing/unsafe declarations,
  and is drift-checked in CI; an external Lake consumer tutorial covers
  checking, parsing, both proof directions, and precise scope boundaries;
- a deterministic 5,000-case native parser fuzz gate covers truncation,
  deletion, replacement, insertion, malformed fields, and excessive formula
  nesting; broader coverage-guided fuzzing remains future hardening;
- the LeanProp wire boundary has an independent deterministic 5,000-case
  mutation gate plus JSON Schema fixtures and a SHA-256 manifest over 1,600
  Lean-emitted labeled records; every accepted wire value now retains an
  indexed derivation and exposes universal `sound`. A clean consumer pins the
  exact public `v0.6.0` tag and typechecks that API, including the structural
  normalizer;
- a 291-case depth-2/3/4 native CI workload now has a 45-second catastrophic
  regression budget; it explicitly does not establish favorable asymptotics,
  and the measured depth-4 cost remains a library-readiness limitation;
- the focused baseline is a Python experiment component, not a Lean library
  module;
- a deterministic 1,000-task matched algorithmic experiment now compares
  focused search, direct atom-matching net generation, and one-edit repair;
  all 930 distinct accepted outputs pass the Lean checker and runtime
  sequentializer, while all 930 distinct mutations are rejected. The supplied
  formula skeleton, positive derivation-first corpus, mostly unique atom
  labels, and distance-one mutations prevent this from establishing the
  research hypothesis;
- a 180-task held-out model experiment is preregistered with balanced
  depth/label/polarity strata, exact implementation/prompt/corpus hashes,
  negative atom-balance witnesses, and reference repair distances two/three;
  no task-specific model response or formal aggregate existed at registration.
  All 360 calls are now frozen, but the original runner failed to finish
  algorithmic scoring in 120 minutes because its wall-clock budget lacked a
  hard interrupt. A public amendment preserves every frozen input/response
  while adding process isolation and hard deadlines. Final scoring is now
  complete: model direct solved 117/180 overall but only 27/90 positives,
  model repair solved 2/180, proof-net generation solved 160/180 with 20
  depth-4 negative hard timeouts, focused search solved 85/180, and the
  constructed distance-ordered repair baseline solved 180/180. This does not
  establish a general model or proof-net advantage.

## Current usability boundary

It can currently be used for:

- constructing MLL certificates in Lean;
- checking structural and Danos-Regnier switching correctness;
- using the general sequentialization existence theorem inside Lean proofs;
- running the proof-bearing executable sequentializer on accepted certificates,
  with kernel-checked universal success for the documented certificate model;
- generating/desequentializing the first-order derivation syntax and retaining
  only checker-accepted results;
- regenerating the labeled v0.2 corpus;
- producing stable v0.3 cache/dataset keys across bounded vertex renamings;
- deciding exact `ProofNetEquivalent` pairwise identity between
  checker-accepted certificates through a checked API;
- running the focused-search comparison baseline;
- reproducing the first deterministic 1,000-task matched experiment and
  validating its hashed artifacts.
- auditing the frozen 180-task model experiment, amendment, raw responses,
  results, and final Lean-verification hashes without calling the model.

It should not yet be presented as:

- a general Lean/mathlib proof assistant extension;
- a performance-qualified executable sequentializer beyond the documented
  unit-free, cut-free MLL certificate model;
- a complete isomorphism-canonical proof identity library;
- a performance-qualified compact wire canonicalizer for the broader
  `ProofNetEquivalent` relation;
- evidence that proof-net generation reduces search redundancy beyond the
  committed experiment's narrow, explicitly biased controlled setting.

## Release gate for library readiness

The macro goal may call the project a mature library only after all logical
gaps above are closed, a clean downstream Lake consumer passes on Windows and
Linux, JSON round trips have structured diagnostics and fuzz coverage, public
API docs and
compatibility rules are published, performance limits are measured, and the
matched algorithmic and model-backed experiments report their results whether
positive or negative. Both controlled runs are now complete; the broader-
logic/corpus, hard performance, and compact identity/canonicalization gates
remain open.
