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
  - [x] Add a 7,200-case positive counterexample search across 1,200 generated
    derivations, depths zero through seven, and six link/boundary storage
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
    reference/mutation audit and the 7,200-case reordered positive search with
    no observed miss or false positive.
  - [ ] Prove
    `Certificate.unificationWorklistFastCheck = Certificate.check` for the
    current event-driven worklist path.
    - [x] Prove canonical initialization plus the complete production
      worklist run preserve abstraction, ordered parents, component/formula
      consistency, and exact pending-premise frontier coverage.
    - [x] Prove atomic pop-and-process scheduler coverage for a submitted
      connective head, including the temporary popped-head exception,
      non-head status transport, exact dependency fan-out, tensor
      same-class preservation, and processed-head reclassification.
    - [x] Prove reverse consumer-table, queue-entry, and waiting-par
      provenance; bundle them with core correctness, scheduler coverage,
      sound flags, and exact carriers; and lift the bundle through the
      complete finite production run.
    - [x] Prove exact queue/waiting flag completeness and duplicate-free
      concrete registries through every transition and finite run, with both
      registry lengths bounded by the submitted-link carrier.
    - [x] Prove exact cumulative enqueue-event accounting: from canonical
      initialization, attempts plus the residual queue length equals initial
      plus dependency plus waiting-requeue insertions.
    - [x] Bound cumulative enqueue sources using structural single-consumer
      ownership, distinct successful-firing history, and bounded waiting
      registries; prove that `n(n+4)+1` exhausts the canonical queue.
    - [x] Reduce the remaining quiescent case to explicit semantic witnesses:
      every submitted but unfired connective has an idle premise, is a
      distinct-thread registered par, or is a same-thread tensor deadlock.
    - [x] Refine the incomplete case by selecting a least-complexity
      unassigned conclusion: structural source-link totality and strict
      premise complexity prove both premises assigned, eliminating the idle
      witness and leaving an exact waiting-par or tensor thread obstruction.
    - [x] Prove semantic threads remain connected in the active all-left
      reference subgraph through every abstract step and the canonical
      worklist run; use reference-switching acyclicity to exclude the
      same-thread tensor-deadlock branch on correct inputs.
    - [x] Prove causal marking closure and the converse retained-edge
      invariant through every reachable state, obtaining exact equivalence
      between active components and union-find classes and a no-active-walk
      witness for the remaining waiting par.
    - [x] Flip exactly the remaining submitted par occurrence, apply an
      occurrence-aware tree-edge-exchange theorem, and obtain a reference
      simple path between its premises which avoids the par conclusion.
    - [x] Prove that active-component separation exposes a genuinely unmarked
      internal occurrence on that path, distinct from both marked endpoints
      and the waiting par conclusion.
    - [x] Strengthen the witness to an exact retained edge occurrence on the
      reference path, directed from a marked source into an unmarked target.
    - [x] Choose the first such frontier, retain its entirely active prefix,
      and identify its source token exactly with the waiting par's left token.
    - [x] Select the last inactive frontier from the reversed path, identify
      its target token with the waiting par's right token, and prove an exact
      ordered decomposition with distinct left and right boundary occurrences.
    - [x] Classify that exact boundary by submitted-link lookup: completed
      axiom initialization and causal closure eliminate axiom and reverse
      connective orientations, leaving a forward par/tensor
      premise-to-conclusion occurrence.
    - [x] Derive the classified frontier connective's exact scheduler status:
      omitted-premise/unassigned or registered/distinct-token for par, and
      opposite-premise/unassigned for tensor after deadlock exclusion.
    - [x] Derive the same scheduler classification at the reverse-oriented
      right frontier.
    - [x] Cut at the first unmarked-to-marked reentry and prove that every
      intervening traversed occurrence has two unmarked endpoints, retaining
      exact scheduler classifications at both boundary orientations.
    - [x] Retain the globally minimum-complexity unassigned waiting
      conclusion and normalize each boundary to a strict rank gap above that
      minimum or an exact registered distinct-thread waiting par.
    - [x] Prove by strong induction that every unassigned occurrence reaches
      a concrete registered waiting par through strict formula-complexity
      descent, then retain non-increasing chase endpoints for both
      orientations of the exact first inactive block.
    - [x] Generalize the exact path/frontier/chase dependency to every
      registered waiting par, prove finite-carrier closure, and prove that a
      `formulas.size + 1` dependency chain repeats a waiting conclusion while
      retaining every adjacent dependency witness.
    - [x] Extract one concrete nonempty closed dependency segment with
      `earlier < later ≤ formulas.size`, equal endpoint conclusions, every
      chain vertex registered as waiting, and all interval-edge witnesses.
    - [x] Retain the exact source connective and selected premise at every
      formula-descent step inside each dependency; prove that these paths
      compose, are complexity-nonincreasing, and are strictly decreasing when
      nontrivial.
    - [x] Lift every formula-premise descent to the exact full occurrence-graph
      backward edge; compose nontrivial chases into vertex-simple,
      internally cusp-free paths; retain state-indexed unassigned evidence
      for every visited occurrence; preserve the exact frontier edge; and
      exclude immediate reverse traversal at the dependency boundary.
    - [x] Classify the all-left mask at the exact lifted full-edge index,
      synchronize the first tail through structural typing and unique
      producer ownership, and prove the exhaustive local alternative: a par
      cusp or tensor-colored free turn.
    - [x] Package each dependency as an exact composable complete-graph
      segment from its source waiting conclusion to its target, then
      concatenate the selected finite family into a genuinely nonempty closed
      occurrence-aware `fullGraph` walk.
    - [x] Prove every individual dependency segment has no immediate reversal
      of the same stored edge occurrence, covering the source/prefix junction,
      retained simple prefix, actual classified frontier/tail junction, and
      all-backward tail.
    - [x] Prove the only possible adjacent-segment immediate reversal forces
      the preceding dependency's formula chase to be reflexive.
    - [x] Bind that reversal to the exact retained-frontier/full-edge
      occurrence and the next waiting par's source incidence, and prove a
      single-junction cancellation preserving endpoints, remaining
      occurrences, and the nesting witness.
    - [x] Iterate exact-occurrence cancellation across internal and cyclic
      closing junctions, preserving endpoints and surviving occurrences, and
      derive the exhaustive empty-or-cyclically-nonbacktracking closed normal
      form. Keep the genuinely nested empty case explicit.
    - [x] Retain a proof-relevant internal/rotated-closing cancellation tree
      and prove that an empty trace gives every represented directed-edge
      value an exact-index reverse value in the original obstruction (a
      membership result, not yet a positional bijection).
    - [x] Prove every forward occurrence in the concatenated dependency walk
      is retained by the all-left reference switching; combine this with the
      empty trace to show that every original edge index in the empty branch
      is reference-retained.
    - [x] Package the all-left reference graph's `IsTree` consequence and
      transport the empty branch's original nonempty closed exact-occurrence
      walk into that graph. Keep explicit that nested backtracking makes such a
      closed tree walk possible.
    - [x] Prove exact cyclic-nonbacktracking transport through arbitrary
      occurrence masks, expose arbitrary switching trees, rule out a
      par-pair-sparse nonempty normal form, and retain a concrete surviving par
      pair whose omitted right occurrence is forced backward.
    - [x] Prove cyclically nonbacktracking inputs are fixed points of the
      proof-relevant normalization, extract an exact internal-or-closing
      cancellation site whenever a nonempty traversal normalizes to empty, and
      force any internal cancellation in two appended nonbacktracking pieces
      to their unique junction.
    - [x] Preserve the selected dependency-segment decomposition as an indexed
      finite family, localize the empty branch's exact site to an adjacent or
      cyclic junction, and prove that its exact occurrence is both the
      preceding dependency's retained reflexive end and the following waiting
      par's stored left incidence.
    - [x] Select the first repeated waiting conclusion, retain injectivity of
      every earlier dependency-chain position, and prove that the empty-branch
      family is a simple cycle of at least two segments whose cancellation
      junction crosses two distinct waiting pars.
    - [x] Retain each dependency's exact first marked-to-unmarked frontier and
      assigned prefix, prove that a frontier entering another registered
      waiting par has no nontrivial formula tail, pair every source reverse
      with its unique cyclic predecessor's exact last occurrence, and prove
      every segment of the fully cancelling simple cycle ends reflexively.
    - [x] Preserve the occurrence-indexed full-segment witness through the
      finite family, expose the deterministic residual core after deleting
      each exact source/frontier pair, prove its endpoints share one live
      token, chain it to the cyclic successor, and prove every residual-core
      edge has assigned source and target occurrences.
    - [x] Prove every residual core is nonempty: an empty core would make two
      cyclically adjacent waiting-par source incidences consume the same exact
      premise, contradicting structural one-parent ownership and simple-cycle
      injectivity.
    - [x] Prove every residual core inherits exact no-immediate-reverse from
      its containing dependency segment, and package nonempty internally
      reduced cores in the deterministic active family.
    - [x] Compose the deterministic active core family into a nonempty closed
      full-graph walk with exact cyclic source-premise endpoints.
    - [x] Prove every core-only occurrence is retained by the reference
      switching, force cyclic normalization of the closed core walk to the
      empty normal form, and localize an exact reversal to a cyclic junction
      between two nonempty internally reduced cores.
    - [x] Reindex the cyclic core junction to one exact dependency step,
      preserve both active core witnesses and both complete segment
      decompositions, and expose the strict contiguous nesting word
      `inner, outer, outer.reverse, inner.reverse`; prove the inner and outer
      layers cannot degenerate using the containing segment's exact
      no-immediate-reverse invariant.
    - [x] Reattach both original occurrence-indexed full-segment witnesses at
      that exact step, reconcile each `core ++ frontier` with its retained
      reference-switching prefix pointwise, and prove that the successor
      retained prefix begins with the inner occurrence's exact reverse.
    - [x] Transport the nonempty-branch turn classification through exact
      switching masks, expose a scheduler-located par obstruction, and derive
      a terminal forward retained-left par cusp through well-founded cyclic
      interval descent.
    - [x] Retain the terminal cusp's exact complementary interval, prove it
      nonempty, closed, internally cusp-free, and strictly shorter, then strip
      every exact first/last reverse shell proof-relevantly with its positional
      context and length equation.
    - [x] Recurse through every nonempty cusp-free normalized core while
      retaining occurrence-indexed scheduler provenance and transitive
      cyclic-interval descent; reduce the complete nesting branch to an empty
      shell core or a scheduler-located nontrivial closing-par core.
    - [x] Exclude the empty shell core by the exact midpoint
      occurrence/reverse cusp, contradicting inherited internal cusp-freedom.
    - [x] Bind the surviving closing-par cusp's first/last tags to exact
      scheduler segments and offsets and prove its forward last incidence
      reference-kept.
    - [x] Bind the same tags, par link, normalization core, and exact
      `first :: middle ++ [last]` split in one dependent witness; prove the
      endpoint steps distinct, the last scheduler target unequal to the common
      conclusion, and the artificial seam not an original coordinate
      adjacency.
    - [x] Retain all intermediate tagged states, interval cuts, closed
      cusp-free complements, reverse shells, and recursive searches in a
      state-and-interval ancestry object.
    - [x] Strengthen every backward-search step with a generator-exact semantic
      cut tying the `CyclicIntervalCut`, omitted-right and retained-left tags,
      both cyclic decompositions, and retained suffix to the same positioned
      obstruction.
    - [x] Strengthen the terminal-complement step with a generator-exact indexed
      frame tying the terminal generator, arc, complement, derived strict cut,
      closed walk, source-fixed reverse-shell normalization, and nesting trace
      to the same forward-cusp split; remove the terminal path's first generic
      `CyclicIntervalCut` positional lift.
    - [x] Assemble the terminal base, data-indexed global ancestry, closing
      outcome, and normalized endpoint split into one exact package with common
      base/complement-base/complement/normalized-core indices.
    - [x] Lift the complete `SchedulerTaggedTerminalComplementStepAt` frame into
      a seam-specific indexed object, or destruct and thread its existing
      existential wrapper exactly once, so replay cannot silently select a
      different arc, rotation, link split, occurrence, coordinate, or segment.
    - [x] Replay the artificial closing seam outward through the exact terminal,
      backward, reverse-shell, nesting, and global-ancestry frames as a boundary
      cursor, starting with an empty gap and reaching the initial tagged family
      with a nonempty accumulated candidate gap.
    - [x] Prove pointwise gap containment and old-gap occurrence preservation
      through every exact replay frame; propagate the same terminal omitted
      arc's zero-offset backward head into the initial tagged family with its
      exact par incidence, omitted reference-mask entry, classified segment,
      waiting-dependency semantics, and source conclusion.
    - [x] Enrich the same replay with an occurrence-position endpoint zipper
      whose gap is the complete complementary arc between the fixed tagged
      endpoints; keep it explicitly distinct from the weaker candidate cursor
      gap.
    - [x] Derive nonemptiness of every indexed flipped segment and prove the
      initial scheduler-family exact gap nonempty, since an empty gap would
      force the already-excluded scheduler-coordinate adjacency.
    - [x] Retain the first exact empty-to-nonempty gap-opening frame, including
      its nonempty outside insertion and explicit gap splice; classify it by
      concrete replay index as terminal or ancestry. In the ancestry branch,
      retain a proof that every terminal-phase gap stayed empty.
    - [x] Construct the canonical endpoint replay of the fixed terminal step.
      Prove that it always first-opens in that replay: a nonempty reverse shell
      opens in the first frame, while an empty shell leaves the nonempty omitted
      terminal arc to open in the second frame.
    - [x] Retain the exact reverse-shell equation, the omitted-right
      zero-offset backward anchor, the forward retained-left last occurrence of
      the outer terminal arc, and the canonical base gap
      `closing ++ taggedArc ++ opening`.
    - [x] Retain the erased outer `taggedArc` as a closed `EdgeWalk` at the
      complement base and a `CuspFreeTraversal`, with the exact cyclic closing
      cusp from its outer last occurrence to its anchor and proof that those
      directed occurrences are not reverses.
    - [x] Prove endpoint-gap sublist and membership preservation, and carry the
      complete outer `taggedArc` in its original linear order through exact
      ancestry into the initial scheduler-family gap, retaining its
      omitted-right head and retained-left last occurrence. This ordered
      sublist is not asserted contiguous or cyclically between the closing
      endpoints.
      The first-opening construction internally splits on shell nonemptiness,
      but its returned proposition does not independently expose the selected
      frame together with the omitted-right anchor origin.
    - [x] Derive a generic ordered decomposition from exact `head?` and
      `getLast?` lookups plus the retained sublist. The initial exact gap is
      exhibited as `g0 ++ anchor :: g1 ++ outerLast :: g2`, and the enclosing
      family satisfies
      `CyclicFourPointDisplayAt firstTag lastTag anchor outerLast`. The generic
      relation allows empty intervals and repeated values.
    - [x] Specialize to the complete initial `tagSchedulerFamily`, derive
      `[firstTag, lastTag, anchor, outerLast].Nodup` from its exact-coordinate
      `Nodup`, and retain the boundary that erased edges and vertices need not
      be distinct.
    - [x] Keep the same outer positioned choice in the endpoint replay and lift
      both it and the inner normalized closing witness through ancestry to the
      complete initial family. Return both exact positioned witnesses with the
      four-point display and four-tag `Nodup` fact in one specialized theorem.
    - [x] Audit and reject contiguous token-age/proper-nesting/LIFO as an
      invariant of the actual flat scheduler. A stable small accepted
      three-axiom/two-tensor regression starts ages 0, 1, and 2 and, under
      reverse connective queuing, first joins ages 0 and 2. Its public receipt
      is two attempts, zero waiting requeues, and two firings; the class shape
      follows from the fixed links and scheduler definitions, not from those
      statistics alone. `tagSchedulerFamily.step` is a selected dependency
      segment index rather than firing age. The order
      `firstTag → lastTag → anchor → outerLast` separates the two pairs, which
      ordinary laminarity permits as siblings.
    - [x] Reject two over-strong flat-confluence formulations by explicit
      counterexample: exact concrete-state confluence fails on a
      derivation-generated correct certificate, and structural-only confluence
      fails on a structurally well-formed certificate.
    - [x] Identify marked occurrence domain plus occurrence-thread partition as
      the next candidate quotient. No committed reproducible audit, release
      gate, or theorem exists for it yet.
    - [ ] Prove that the residual parsing witness survives every arbitrary
      successful flat-worklist firing, or establish the required theorem
      modulo the marked-domain/occurrence-thread quotient. Use that
      scheduler-specific result to exclude the closing-par base and
      path-exposed waiting-par obstruction. Closing-par exclusion remains open.
    - [ ] Prove correct-quiescent-state progress.
  - [x] Add the first separate Figures 7--8 primitive: one reusable
    source-incidence index with exact submitted-link-origin proof and a
    structural singleton theorem. `SourceIndex.Sound` alone is provenance, not
    lookup uniqueness: both endpoints of a malformed self-axiom enter the same
    bucket, and structural well-formedness excludes that multiplicity.
  - [x] Add a bounded/globally tagged `NEXTAXIOM` returning the exact axiom
    index/endpoints/tags/trace, with input-unmarked and trace-length bounds,
    tag-array size preservation, old-true-tag monotonicity, trace `Nodup`, and
    input-false/output-true tagging of the trace and endpoints. Define its
    touched carrier as trace plus endpoints.
  - [x] Prove touched-set disjointness for successive successful calls that
    strictly thread `first.tags`. Treat this as the exact scope of the global
    no-revisit discipline; do not extend it to reset or replaced tags. Add a
    dynamic start proved to refine Figure 5 under
    `OrderedParents`. Cover canonical tags/trace, zero fuel, out-of-bounds,
    tagged and marked starts, missing and non-unique sources,
    threaded-result-tags repeat rejection, and dynamic start.
  - [x] Prove every successful trace is an exact oriented source-left route to
    the axiom endpoint actually reached, independently of submitted
    `left`/`right` orientation. Fix the stored-right case by executable and
    theorem regression.
  - [x] Prove initial/local `NEXTAXIOM` totality on the production source index
    under `SearchClearThrough` and fuel strictly greater than the starting
    formula complexity; derive the full-carrier-clear `complexity + 1`
    corollary, test every canonical occurrence, and lock a depth-two fixture
    where rank fuel fails but `rank + 1` succeeds.
  - [ ] Prove later-state `NEXTAXIOM` start selection; do not treat the local
    theorem as totality of the carrier-size wrapper or Figure-7 `new`.
    - [ ] Replace global low-rank freshness with a route-local invariant that
      remains usable after earlier calls have tagged complexity-zero axiom
      endpoints.
    - [ ] Prove the formula-complexity/carrier bound needed for a
      `nextAxiom?` wrapper corollary, if the current carrier-size fuel is to
      become part of the total API contract.
    - [ ] Factor the local theorem's mark-slot requirement from the stronger
      full `Abstractable` runtime invariant when a more reusable interface is
      needed.
  - [x] Formalize the first independent delayed state slice:
    `RawTokenAge` is discovery order rather than a representative;
    `SigmaAgePartition` gives strictly increasing `σ` boundaries below the
    horizon; waiting storage distinguishes out-of-bounds, undefined `⊥`, and
    initialized empty `∅`; strict empty `init` keeps `W(0)` undefined and
    establishes `OperationalWaitingDomain`.
  - [x] Keep the printed Figure-7 fresh-cell `newEnqueue?` as a literal audit
    helper only. Production `operationalNewEnqueue?` initializes the old active
    boundary, leaves the fresh top undefined, and kernel-proves preservation of
    `WellShaped` and `OperationalWaitingDomain` (initialized allocated cells
    exactly `sigma.dropLast`). This resolves the code path by a documented
    project interpretation, not an author-confirmed erratum.
  - [x] Add initial and typed later reservation bridges to production
    `UnificationState`, preserving `RealizesSigma`, the operational waiting
    domain, component/carrier consistency, and complete threaded tags while
    keeping submitted and reached/partner orientations distinct.
  - [x] Add the invariant-bound local Figure-7 pop-before-mark, raw-age mark,
    tensor-mate, post-mark search, and operational `new` pipeline.
  - [x] Add proof-relevant reachability for exactly the
    empty/init/operational-new fragment. Prove current tag iff recorded touch,
    whole-history submitted axiom-slot `Nodup`, and reservation-event count
    alignment. Keep this separate from `ReservationInvariant`, which alone
    still permits reset or forged tag arrays.
  - [x] Add the canonical generic par/tensor consumer view, the exact declared
    conclusion view with local `NodeWellFormed` ownership and an empty
    consumer bucket, the synchronized common prefix, and local executable
    `concl`/`nop` rules with dependent success characterizations and
    reservation-invariant preservation.
  - [ ] State an independent Boolean-free relation for every Figure-7 rule and
    prove executable refinement and valid-guard completeness. This is now
    complete for the common prefix, `concl`, `nop`, local `wait`, local
    `forward`, and the bounded empty-cell `UnifyEmpty`; their
    dependent witnesses remain as exact equation-backed executable
    compatibility records. `WaitRule` states the raw-age guard in
    `before.core.marks` and uses an exact proposition-level
    `sigmaBoundary? = some boundary` equation. `ForwardRule` retains the exact
    submitted par occurrence and non-strict raw-age guard while factoring the
    executable active-ready `Nodup` refinement into a separate predicate.
    Direct soundness and structurally valid completeness/iff/output uniqueness
    are kernel checked for Forward, bounded `UnifyEmpty`, and strict-singleton
    `UnifyOne`; Forward additionally
    has scheduler-invariant completeness/iff. The corresponding direct layer
    for `new` and the arbitrary-payload activation fold remain open.
  - [ ] Replace the prototype's eager axiom starts and flat waiting requeues
    with the complete Figures 7--8 state and transitions. Align the paper-level
    `R` stack with `σ`, prove ready/waiting payload ownership, state
    route-local later-call freshness, integrate the local initialized-cell
    `wait` rule into full history, integrate the successful local `forward` and
    bounded `UnifyEmpty` and strict-singleton `UnifyOne`, implement the
    arbitrary-payload activation fold under the
    operational waiting domain, and integrate the already-local
    `concl`/`nop`/`wait`/`forward`/`UnifyEmpty`/`UnifyOne` rules into a complete
    history/dispatcher. A proof-only exact component/link occurrence
    relation and bidirectional raw-mark ownership predicate are now present;
    the forest is integrated for empty/init and the common prepared prefix,
    so `concl`/`nop` preserve it.
  - [x] Preserve the complete current occurrence-exact state-only
    `SchedulerInvariant` through every successful deterministic `NewStep` and
    successful executable `new?`, including exact fresh-axiom forest extension
    and all ready/queue, causal, waiting-span, pending-premise, and counter
    fields. This does not prove later-state `new?` success or totality.
  - [x] Preserve the complete strengthened invariant through every successful
    local `WaitStep` and executable `wait?`: retain the exact submitted par
    slot, global queue uniqueness/raw-unmarkedness, and strict waiting span
    without constructing or counting the delayed par. This remains
    successful-step preservation, not applicability, reachability, or progress.
  - [x] Implement successful typed `ForwardStep` and executable `forward?` with
    the exact submitted par occurrence and the paper guard
    `selectedRawAge ≤ mateRawAge`. Preserve the complete occurrence-exact
    `SchedulerInvariant`, including the component forest/live frontier,
    ready/waiting queue, waiting spans, pending coverage, and fired counter.
    Keep the extra active-ready `Nodup` guard explicitly as a fail-closed shape
    check, not a paper guard. Lock the non-equality boundary case and a typed
    `init → nop → forward → concl` regression. This remains
    successful-step preservation, not applicability, totality, dispatcher,
    history, reachability, or progress. Its Boolean-free `ForwardRule`,
    executable correspondence, and output uniqueness are complete under the
    documented structural/invariant/shape hypotheses. It does not establish
    pure worklist completeness, fallback removal, faithful `NEXTAXIOM`
    sequencing, or whole-program linearity.
  - [x] Implement the bounded `W(j) = []` `UnifyEmpty` executable and independent
    direct relation. Retain the exact submitted tensor slot/orientation, compare
    only raw ages with `j ≤ μ(mate) < i`, derive exact adjacent representatives
    through `RealizesSigma`, and prove soundness plus structurally valid
    completeness/iff/output uniqueness with the ready-list `Nodup` premise
    explicit. Cover both stored orientations, nonempty-cell rejection, the
    nonadjacent three-age lower-guard regression, and the same-active-age
    strict-upper-guard regression. Every successful bounded
    execution preserves `ReservationInvariant`, including the exact
    `RealizesSigma` transport through the active-boundary pop and
    `parent[i] := j`.
  - [x] Preserve `ComponentForestProvenance` and the complete strengthened
    `SchedulerInvariant` through every successful typed/executable bounded
    `UnifyEmpty`: derive the exact tensor component, merge survivor/retired
    forest ownership, and transport live-frontier, queue/waiting/pending, and
    fired-counter fields. This remains local successful-step preservation, not
    applicability, dispatcher progress, history, or reachability.
  - [x] Implement strict-singleton `W(j) = [c]` `UnifyOne`. Recover `c`'s
    exact submitted par producer/source slot, perform the atomic
    prepare → tensor union → one waiting-par activation → scheduler drain,
    and prove the independent Boolean-free direct relations,
    typed/executable correspondence, output uniqueness, exact `+2` counter
    equation, `ReservationInvariant`, and complete occurrence-exact
    `SchedulerInvariant` preservation. Reject empty and length-at-least-two
    payloads. Treat the explicit par construction as the project's
    derivation/provenance representation refinement of the paper's move of
    `W(j)` into ready, not as a claim about the paper text.
  - [ ] Complete arbitrary-payload `unify` with a typed activation fold
    constructing every drained waiting par and accounting for
    the exact `1 + |W(j)|` counter change; a direct nonempty-payload stack merge
    is insufficient for `ReadyBucketFrontierExact`. The singleton base case is
    complete; the fold for payload length at least two remains open. Establish the
    special union-find invariants, full-rule
    reachability, queue provenance, progress, completeness of that sequential
    executable, and a cost theorem over every implemented operation before
    claiming Guerrini linearity. These stack invariants are false for the flat
    scheduler.
  - [ ] Remove the recursive reconstruction fallback only after pure worklist
    completeness is kernel checked.
- [x] Publish `v0.9.0`, verify release-candidate, automatic tag-push, and
  explicit `release_ref=v0.9.0` CI, and pin a clean consumer to the exact
  public tag.

## Later research

- indexed/streaming intrinsic encoding to reduce the current repeated-formula
  serialization cost and adversarially qualify the public wire envelope;
- cut links and cut elimination as graph rewriting;
- additives, exponentials/boxes, and unification nets;
- hierarchical proof graphs for dependency-rich mathlib theorems;
- a `proofnet_ai` tactic that treats all model output as untrusted input.

The success criterion is empirical and kernel-checked. A visually appealing
graph or a lower token count without matched proof success is not enough.
