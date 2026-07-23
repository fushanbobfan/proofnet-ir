# Roadmap

## v0.1 - Verified MLL reference core

- [x] Pin Lean 4 toolchain.
- [x] Define unit-free MLL formulas and involutive negation.
- [x] Define formula occurrences and axiom/tensor/par links.
- [x] Check local structural invariants.
- [x] Enumerate all switchings.
- [x] Prove switching enumeration sound and complete against an independent
  one-edge-per-par inductive relation.
- [x] Implement the reference tree checker.
- [x] Prove semantic soundness against an independent inductive walk relation.
- [x] Prove completeness/iff for the exact finite-computation contract.
- [x] Reconstruct one supported canonical sequent derivation.
- [x] Add at least 20 compile-time positive/negative assertions.
- [x] Add a versioned JSON Schema and fixtures.
- [x] Prove finite closure membership implies an inductive graph walk.
- [x] Prove a bounded inductive walk is found after some finite closure depth.
- [x] Prove `closureN fuel` iff an independent path of at most `fuel` steps
  exists, and lift the iff through `isTree` and `Certificate.check`.
- [x] Prove every arbitrary in-bounds graph walk reduces to a path within the
  `vertexCount` budget, identifying `Correct` and `FuelCorrect`.
- [x] Prove general sequentialization for the supported representation.
- [x] Add a second generated proof-tree/net family and labeled mutation tests.
- [x] Generalize derivation-first generation and gated reconstruction to the
  recursive identity family `A, A-dual` at arbitrary formula depth.
- [x] Audit the v0.1.0 checker against an independent oracle on all 33,868
  simple graphs through six vertices and 1,000 generated/mutated certificates.
- [x] Replace the Boolean premise in declarative structural correctness with
  an independent proposition and prove the executable/specification iff.
- [x] Generalize generation/desequentialization from identity nets to arbitrary
  cut-free derivation trees.
- [x] Define lossless bounded vertex renaming, formula/link/conclusion
  transport, and a kernel-checked inverse round trip.
- [x] Prove structural, switching, and checker/declarative correctness
  invariant under arbitrary bounded vertex renaming.
- [x] Define `ReindexEquivalent`, prove it is an equivalence relation, and
  prove it preserves executable and declarative correctness.
- [x] Compute a stable v0.3 serialization key proved invariant under
  `ReindexEquivalent`, with v0.2 migration and 1,000-record property tests.
- [x] Prove the converse/completeness theorem for the v0.3 certificate normal
  form and prove that normalization returns an in-class representative for
  every structurally well-formed certificate.

## v0.2 - Dataset and repair loop

- [x] Specify a controlled comparison against focused cut-free proof search.
- [x] Generate valid derivation trees first, then desequentialize to proof nets.
- [x] Produce dataset mutations for missing links, duplicated resources, and
  self-axioms; retain regression fixtures for non-dual axioms, cycles,
  disconnection, and wrong connective attachment.
- [x] Canonicalize v0.2 certificate serialization under the documented fixed
  occurrence-numbering contract.
- [x] Publish 1,000 checker-labeled records with a deterministic generator,
  independent-oracle verification, and a content hash.
- [x] Implement a runnable focused cut-free search baseline.
- [x] Define deterministic graph edit operations and complete a first matched
  1,000-task algorithmic comparison of focused search, direct net generation,
  and one-edit repair, with every unique certificate result rechecked and
  sequentialized by Lean.
- [x] Report validity, repair success, Lean/checker calls, zero model-token
  cost, timing, memory, failures, and bounded redundancy collapse with explicit
  corpus and formula-skeleton limitations.
- [x] Repeat the comparison with genuinely model-backed proposals, held-out
  negative tasks, harder repeated-label strata, and repair distances above one.
  The 180-task corpus and protocol are now preregistered with balanced
  depth/label/polarity strata and frozen implementation/prompt hashes; the
  360 task-specific model calls are captured with zero transport errors. A
  publicly recorded execution amendment adds real per-method hard timeouts
  after the original runner failed to finish scoring in 120 minutes; amended
  scoring and the final result audit are complete. The negative result is
  retained: model direct solved 27/90 positives and model repair 2/180 tasks;
  every Lean-accepted output sequentialized.

## v0.3 - Reindex-invariant wire keys

- [x] Prove whole-checker invariance under bounded vertex bijections.
- [x] Add `reindex-v1` JSON, schema, native parser, migration, fixtures, and
  downstream-consumer coverage.
- [x] Audit invariance, schema validity, idempotence, and documented order
  sensitivity on all 1,000 committed records.
- [x] Complete the reindex normal-form converse and
  representative-membership proofs, with an executable decision procedure.

## v0.4 - General sequentialization

- [x] Define `LinkPermutationEquivalent` and the generated
  `ProofNetEquivalent` relation, then prove link-order permutation preserves
  structural well-formedness, every switching tree, declarative correctness,
  and the executable checker.
- [x] Define the evidence-rich `SequentializationResult` theorem contract,
  ordered-boundary transport, and checker-safe terminal-par candidate peeling.
- [x] Prove terminal-par peeling preserves structural and switching
  correctness for every accepted input: the conclusion is a leaf in every
  switching, full premise structural preservation holds, and every premise
  switching is the deleted input switching up to edge-order permutation.
- [x] Implement checker-gated splitting-tensor candidate discovery,
  occurrence-component restriction, and cross-link rejection.
- [x] Prove terminal-tensor local ownership and switching degree: its producer
  is unique, no other link is incident to its conclusion, selected par edges
  contribute zero incidence, and the two fixed tensor edges give degree two.
- [x] Define the proposition-level `SplittingTensor` condition and prove the
  bounded full-occurrence graph's `vertexCount`-round closure decides its
  unbounded walk/non-reachability condition exactly.
- [x] Prove a genuine splitting tensor induces a disjoint exhaustive vertex
  partition with no crossing remaining link, both boundary reindexings are
  defined, and `splitTerminalTensorCandidate?` necessarily returns two
  certificates that are both structurally well formed.
- [x] Prove every child switching lifts to an input switching as an induced
  occurrence restriction, and prove both restricted graphs bounded and
  connected via the terminal-tensor separator theorem.
- [x] Prove the two restricted switching graphs satisfy the exact tree
  edge-count equation and derive full checker/declarative correctness,
  including totality of the checker-gated split on accepted inputs.
- [x] Prove every accepted net containing a connective has a terminal par or splitting tensor.
  The finite-rank sublemma that every structurally well-formed net containing a
  connective has some terminal tensor or par is now complete; the remaining
  case is the global splitting lemma for terminal tensors when no terminal par
  exists. Its edge-aware multigraph paths/simple cycles and exact local
  switching colors/cusps are now formalized. The exact tree-acyclic theorem,
  par-sparse cycle-to-switching containment construction, mask-compaction
  transport, and `DeclarativelyCorrect.cuspAcyclic` bridge are proved for
  exact multigraph edge occurrences. Exact-edge simple paths, cusp-free
  continuation concatenation, the strengthened strict edge order, and its
  finite maximal-element theorem are also complete. Simple-cycle orientation,
  minimal non-closing cusp count, and continuation to the first nontrivial
  cusping edge are now kernel checked. Cusp-count reversal/additivity, first
  intersection truncation, full-graph looplessness, and cusp-adjacent
  occurrence exclusion now supply the next bungee layer. The normalized
  intersection and return paths now close into an exact simple cycle with
  disjoint occurrences, and cusp-acyclicity forces its splice boundary to be
  its unique internal cusp. Exact cycle rotation, complementary wrap-around
  path extraction, the one-cusp split arithmetic, edge-disjoint first-return
  splicing, and rotation of that splice back to the original base are now
  formalized. The same-base closing proof and strict minimal-cycle inequality
  now close the full contradiction for every first hit away from the old base,
  and both hit-at-base endpoint orientations are complete. The after-cusp
  branch, adjacent incoming-edge case, exhaustive first-intersection
  classifier, universal-separation conclusion, and finite generalized-Yeo
  maximality theorem are now kernel checked. Exact annotation inversion
  identifies maximal cusping occurrences with stored par links, while
  `SplittingVertex.toSplittingTensor` turns any colored splitting terminal
  tensor into the existing deletion/non-reachability separator. The
  representation-specific sequentialization carrier, exact parent-occurrence
  step, universal separation proof, and finite parametrized maximality now
  yield a public terminal par or splitting tensor for every correct
  certificate containing a connective; see
  `docs/splitting-theorem-audit.md`.
- [x] Prove the general graph leaf-deletion theorem: boundedness, exact edge
  accounting, simple-walk leaf avoidance, connectedness, and `IsTree` are all
  preserved under vertex compaction.
- [x] Prove the well-founded occurrence measure for both inverse rules:
  terminal-par peeling strictly decreases formula-array size, and both
  splitting-tensor restrictions are strictly smaller than the input.
- [x] Close the no-connective recursive base case: correctness forces exactly
  two formula occurrences, one axiom, a complete two-element boundary, and a
  full `SequentializationResult` for either axiom orientation and either
  ordered conclusion orientation.
- [x] Factor the recursive rule layer into an auditable logical contract:
  prove exact inference/build equations for par and tensor focused on terminal
  boundary entries, and prove that premise derivations compose through par or
  tensor plus explicit exchange while preserving the exact ordered input
  sequent. This step deliberately omits graph reconstruction/equivalence.
- [x] Recursively construct a kernel-typed cut-free `Derivation` modulo
  explicit exchange for every checker-accepted certificate, with a
  well-founded proof over formula-occurrence count and exact preservation of
  the ordered input sequent. This is the logical theorem
  `logicallySequentializable`; it does not yet manufacture a first-order
  `CutFreeDerivation` tree or prove graph reconstruction.
- [x] Establish the strong-reconstruction foundation: flatten every generated
  `ProofNetEquivalent` proof to one bounded reindexing followed by one link
  permutation; prove `pick?` and accepted `reorder?` commute with boundary
  projection; and prove every successful first-order `build?` is balanced and
  has exactly the same formula boundary as `infer?`.
- [x] Prove exact terminal-par reconstruction and full inverse-rule
  composition into a first-order tree with executable exchange.
- [x] Prove exact splitting-tensor occurrence-boundary reconstruction,
  block-sum renaming, binary inverse-rule composition, and equivalence to the
  input certificate.
- [x] Close the well-founded `sequentialization_of_check` recursion and public
  `generallySequentializable` theorem: every accepted certificate returns a
  `SequentializationResult` whose desequentialization is
  `ProofNetEquivalent` to the input.

## v0.5 - Executable sequentialization and library hardening

- [x] Add a runtime certificate-to-tree search over checker-preserving terminal
  par and splitting-tensor inverses.
- [x] Return a proof-bearing result with exact ordered input labels, accepted
  desequentialization, and `ProofNetEquivalent` output.
- [x] Exhaustively backtrack over repeated boundary formula occurrences rather
  than assuming formula labels are unique.
- [x] Prove completeness of the optimized occurrence-permutation enumeration.
- [x] Prove completeness of executable direct-equivalence witness search on
  structurally well-formed certificates.
- [x] Expose and characterize a Boolean `ProofNetEquivalent` decision API on
  structurally well-formed certificates.
- [x] Add structured staged errors and 250 broad generated regressions plus a
  repeated-label regression.
- [x] Reject the over-strong link-order-sensitive identity contract and retain
  an accepted reversed-link-order certificate as a regression.
- [x] Exercise the runtime API from a clean path-dependency consumer and pin
  the public theorem trust boundary in CI.
- [x] Prove the finite alignment kernel cannot miss an explicitly supplied
  inference/desequentialization/equivalence witness, and close executable
  totality for all four accepted axiom-only representations.
- [x] Connect terminal-par candidate totality and the recursively returned
  premise tree to `rebuildParTree?` success.
- [x] Connect splitting-tensor candidate totality and both recursively returned
  premise trees to `rebuildTensorTree?` success.
- [x] Prove the executable search succeeds for every checker-accepted
  certificate, using the terminal-rule dichotomy, candidate totality, and
  completeness of the finite occurrence-permutation enumeration. The proof
  connects both recursive rule rebuilders, the axiom base, and the generic
  alignment layer through a formula-count fuel induction and exposes
  `Certificate.sequentialize_complete`.
- [x] Add a deterministic 5,000-case malformed-input fuzz gate for the native
  checked parser.
- [x] Add a checked depth-2/3/4 runtime workload and CI regression budget,
  documenting the current depth-sensitive cost.
- [x] Add a kernel-environment-generated, CI drift-checked public API reference
  and an external Lake consumer tutorial.
- [x] Add an executable finite canonical family and prove extensional family
  equality iff `ProofNetEquivalent` on structurally well-formed inputs,
  without quotienting ordered conclusions or claiming arbitrary graph
  isomorphism.
- [x] Establish the existing exact decision procedure as the supported
  production pairwise identity boundary: checker-accepted callers use
  `CheckedCertificate.sameProofNet?`, whose iff theorem decides exactly
  `ProofNetEquivalent`. Ordered conclusions now prune occurrence candidates
  during generation with a proved completeness theorem and a 64-pair
  repeated-label regression. The factorial family remains a specification
  oracle; a compact single-representative wire key is still a separate future
  feature, not part of this completed alternative.

## Post-v0.5 derivation-first soundness

- [x] Prove that a successful formula-only `infer?` pass always lifts through
  positional picks and exchanges to a successful occurrence-aware `build?`,
  with exactly the same ordered conclusion formulas even for duplicate labels.
- [x] Prove that every successfully inferred first-order rule tree produces a
  structurally well-formed, switching-correct certificate with matching
  conclusion lookup, and derive totality of `elaborate?` on `infer?` success.

## v0.6 - Persistent LeanProp bridge

- [x] Add a conservative two-context derivation design for persistent and
  linear hypotheses without changing the MLL certificate semantics.
- [x] Make persistent weakening and contraction explicit, omit their linear
  counterparts, and prove one linear-axiom leaf per linear occurrence.
- [x] Support conjunction, implication, equality rewriting, universal
  instantiation, and existential witness nodes.
- [x] Reconstruct Lean proof terms for a hand-curated cross-rule smoke corpus.
- [x] Add a deterministic 600-item positive schema corpus across six resource
  and connective strata, with universal reconstruction under atom valuations.
- [x] Add an unindexed checker with stable path-aware diagnostics, a positive
  erasure/recovery theorem, and 1,000 stratified malformed inputs covering all
  error codes.
- [x] Add strict `leanprop-schema-0.1` JSON, a native checker-gated parser,
  JSON Schema/fixtures, 600 positive and 1,000 negative wire-path checks, and a
  deterministic 5,000-case mutation-fuzz gate.
- [x] Pin the 1,600-record Lean-emitted corpus with a reproducible SHA-256
  manifest without duplicating checker labels in Python.
- [x] Elaborate every accepted raw/wire schema into an indexed derivation,
  prove exact infer/elaborate agreement and acceptance lifting in Lean, and
  expose the universal checked-input soundness theorem to downstream users.
- [x] Build a clean downstream Lake consumer from an exact public
  v0.6-development Git commit and typecheck the checked-input theorems there.
- [x] Prove proof-relevant exchange complete for `List.Perm` under `Nonempty`,
  both dependent-environment inverse laws, and persistent/linear exchange
  admissibility for every proposition-level permutation.
- [x] Implement typed recursive cancellation of persistent
  contraction-over-weakening redexes and prove reducedness, fixed points,
  idempotence, structural-size nonincrease, linear-resource preservation, and
  pointwise proof preservation.
- [x] Freeze `leanprop-schema-0.1` as the sole v0.6 LeanProp wire contract and
  require explicit migration fixtures when a second wire version is added.
- [x] Qualify the public bridge through a final v0.6-tag-pinned downstream
  consumer.

## v0.7 - ProofNetEquivalent fingerprint and wire qualification

- [x] Define the finite v0.3 serialized image of
  `proofNetCanonicalFamily` and select its lexicographically least member.
- [x] Prove fingerprint totality, selected-member provenance, and forward
  invariance under `ProofNetEquivalent`.
- [x] Exercise the API in the source tests and path-based downstream consumer.
- [x] Introduce an explicitly versioned, length-framed structural token code
  and prove it injective, avoiding any unproved assumption about JSON
  compression.
- [x] Derive the exact theorem: equal typed canonical codes iff
  `ProofNetEquivalent` under precise structural/checked preconditions.
- [x] Introduce `proofnet-canonical-key-0.1` /
  `proofnet-equivalent-v1` instead of reinterpreting v0.3, with a bounded
  parser, schema, v0.3 semantic migration, negative tests, 1,000 wire
  properties, and 5,000 malformed-key fuzz cases.
- [x] Qualify factorial wire generation with a pre-computation seven-link
  ceiling and a measured 1/4/7-link, 5,065-candidate benchmark under a
  separate 10-second budget. The unbounded typed key remains a specification
  oracle; the non-factorial construction was deferred to v0.8.
- [x] Pin a clean downstream consumer to the public `v0.7.0` release and
  qualify local and exact-tag CI. The post-tag main-branch CI is the final
  publication receipt.

## v0.8 - Intrinsic non-factorial canonicalization

- [x] Define an occurrence-forest traversal rooted at the ordered conclusion
  boundary and invariant under bounded vertex renaming and submitted link-list
  permutation.
- [x] Prove that structural well-formedness makes the traversal cover every
  formula occurrence exactly once.
- [x] Assign every axiom/tensor/par link an orientation-sensitive owner and
  prove intrinsic emission is exactly a permutation of the submitted links.
- [x] Prove the intrinsic normalized certificate is in the input's exact
  `ProofNetEquivalent` class and derive canonical-form equality iff
  `ProofNetEquivalent`.
- [x] Derive exact typed structural-code and typed-key iff theorems without
  enumerating link permutations.
- [x] Introduce the distinct `proofnet-canonical-key-0.2` /
  `proofnet-equivalent-intrinsic-v1` JSON wire, parser, schema, fixture,
  checker-certificate migration, safe matcher, and trust audit.
- [x] Differentially compare the intrinsic key with the v0.7 factorial oracle
  on 1,000 deterministic positive/negative cases and exercise 1,000 additional
  mixed derivation-generated accepted nets.
- [x] Extend malformed-key fuzzing, schema validation, generated API docs, and
  the path-based downstream consumer.
- [x] Qualify the direct polynomial implementation beyond the old ceiling:
  four structural identity cases through 145 links complete under a separate
  five-second budget on the development machine.
- [x] Publish `v0.8.0`, verify both automatic tag-push and explicit
  `release_ref=v0.8.0` CI, and pin a clean consumer to the exact public tag.

## v0.9 - Graph semantics and correctness performance

- [x] Expose occurrence-aware `Graph.Acyclic` as the absence of an exact
  `EdgeSimpleCycle`, preserving parallel stored edges as distinct cycle
  occurrences.
- [x] Prove every public declarative `Graph.IsTree` is `Graph.Acyclic`, add
  cyclic/tree regressions, generate the API reference, and lock the theorem's
  trust dependencies in CI.
- [x] Prove exact directed-edge, edge-walk, simple-cycle, and acyclicity
  transport under bounded vertex renaming, including negative cyclic and
  positive tree regressions after nontrivial swaps.
- [x] Prove the converse finite-multigraph forest theorem and derive
  `IsTree ↔ Bounded ∧ Connected ∧ Acyclic` without retaining the current
  edge-count equation as a redundant premise.
- [x] Introduce an exhaustive certified cycle/forest decision procedure,
  prove `isAcyclic = true ↔ Acyclic`, and prove the resulting
  `isTreeViaAcyclic` Boolean-equal to the existing
  reachability-plus-edge-count `isTree` checker. This remains an exponential
  specification oracle.
- [x] Introduce an exhaustive certified colored-cycle oracle, prove
  `isCuspAcyclic = true ↔ CuspAcyclic`, and prove every declaratively correct
  or reference-checker-accepted certificate passes it. This is the executable
  differential specification for the generalized-Yeo route, not yet a
  replacement checker.
- [x] Prove the acyclicity half of the reverse bridge:
  under structural well-formedness,
  `CuspAcyclic ↔ every occurrence-order switching is Acyclic`, with exact
  occurrence-index transport through switching masks and regressions covering
  the public canonical net.
- [x] Prove the exact correctness decomposition
  `check = true ↔ StructurallyWellFormed ∧ CuspAcyclic ∧
  AllOccurrenceSwitchingsConnected`, isolating connectedness as the sole
  remaining all-switchings graph obligation.
- [x] Add a proof-bearing verifier for a supplied cut-free derivation that
  performs structural validation, inference/desequentialization, and
  non-factorial intrinsic identity checking without evaluating input
  switchings or enumerating vertex permutations. Prove soundness and
  completeness relative to an equivalent supplied derivation.
- [x] Implement checker-free automatic inverse-rule reconstruction for bare
  certificates, prove universal completeness for every reference-accepted
  certificate, and prove its Boolean decision equal to the all-switchings
  checker.
- [ ] Qualify and optimize the automatic path across the frozen corpus,
  adversarial tensor/par shapes, and repeated-label boundaries. The current
  path avoids switching and vertex-permutation enumeration but may backtrack;
  retain the all-switchings implementation as a differential specification
  oracle and make no linear-time claim yet.
  - [x] CI-gate exact agreement on the 1,000-case deterministic corpus
    (250 accepted derivations and 750 malformed mutations) under a 15-second
    native budget.
  - [x] Add and CI-gate 18 adversarial skewed/balanced/alternating,
    repeated-internal-label, repeated-boundary-label, and reversed-link-order
    cases through 126 formula occurrences and 22 conclusions. Replace eager
    factorial fallback materialization on the fast path with one greedy
    formula-tree/axiom-profile alignment and defer equivalence verification
    until the complete tree.
  - [x] Add `reconstructDerivationWithinLimits`, a structured-error,
    fail-closed API with a qualified 128-formula/96-link/24-conclusion
    envelope. It never enters the exhaustive fallback; prove bounded success
    sound, reference-accepted, and included in the complete unbounded
    decision.
  - [ ] Prove or enforce a user-facing worst-case resource bound for fallback
    backtracking and repeated-label enumeration, or add a step/deadline budget
    below the current input-size envelope; do not infer a polynomial or linear
    guarantee from the bounded stress suite.
- [x] Prove the reverse bridge from structural well-formedness, a connected
  reference switching, and `CuspAcyclic` to full switching correctness. The
  proof uses a finite maximal acyclic extension to derive
  `Bounded ∧ Acyclic ∧ |E| + 1 = |V| → Connected`, proves all switchings have
  the reference edge count, and eliminates
  `AllOccurrenceSwitchingsConnected`.
  - [x] Add `compactCheck`, which evaluates structural well-formedness,
    exhaustive cusp-acyclicity, and one reference connectivity check without
    enumerating switchings; prove `compactCheck = check`.
  - [x] Implement the Figure-5 Guerrini token rules as a deterministic
    derivation-producing fast path, prove successful results sound through
    independent derivation verification, and differentially test 1,500
    positive/reordered/malformed inputs.
  - [x] Expose an exact switching-free `unificationCheck` by using the
    deterministic pass first and the proved checker-free sequentializer only
    as a completeness fallback; prove `unificationCheck = check`.
  - [x] Add a 6,000-case positive counterexample search across 1,000 generated
    derivations, depths zero through five, and six link/boundary storage
    orders; retain its zero-miss result as empirical evidence only.
  - [x] Expose proof-relevant saturation statistics and prove the current
    eager schedule performs at most `|links|²` link-list visits; keep
    frontier, union-find, verification, and fallback costs outside that
    deliberately scoped theorem.
  - [x] Implement an event-driven premise-consumer worklist with a deduplicated
    waiting-par set, verified derivation output, soundness theorem, exact
    fallback wrapper, operational counters, and a conservative proved
    `n(n+4)+1` link-attempt cap.
  - [x] Differentially qualify the worklist on the 1,500-case
    reference/mutation audit and the 6,000-case reordered positive search with
    no observed miss or false positive.
  - [ ] Prove the pure deterministic unification path complete, removing the
    recursive fallback from the logical decision.
  - [ ] Replace the prototype's eager axiom starts and flat waiting requeues
    with the Figures 7--8 sequential stack, formalize
    `NEXTAXIOM`/union-find invariants, prove fuel sufficiency and pure
    completeness, and extend the cost theorem to all implemented operations
    before claiming Guerrini linearity.

## Later research

- indexed/streaming intrinsic encoding to reduce the current repeated-formula
  serialization cost and adversarially qualify the public wire envelope;
- cut links and cut elimination as graph rewriting;
- additives, exponentials/boxes, and unification nets;
- hierarchical proof graphs for dependency-rich mathlib theorems;
- a `proofnet_ai` tactic that treats all model output as untrusted input.

The success criterion is empirical and kernel-checked. A visually appealing
graph or a lower token count without matched proof success is not enough.
