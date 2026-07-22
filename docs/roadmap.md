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
- [ ] Prove general sequentialization for the supported representation.
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
- [ ] Define graph edit operations and compare direct sequent generation,
  graph generation, and graph repair in a model-backed experiment.
- [ ] Report validity, repair success, Lean calls, token cost, and redundancy
  collapse without claiming theorem-proving gains before measurement.

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
- [ ] Prove every accepted non-axiom net has a terminal par or splitting tensor.
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
  path extraction, and the one-cusp split arithmetic are now formalized. The
  remaining minimal-cycle rerouting inequality, universal-separation
  conclusion, and generalized-Yeo instantiation are in
  `docs/splitting-theorem-audit.md`.
- [x] Prove the general graph leaf-deletion theorem: boundedness, exact edge
  accounting, simple-walk leaf avoidance, connectedness, and `IsTree` are all
  preserved under vertex compaction.
- [ ] Recursively construct a cut-free derivation modulo explicit exchange.
- [ ] Prove its desequentialization is `ProofNetEquivalent` to the input.

## v0.5 - Persistent LeanProp bridge

- Add a two-context design for persistent and linear hypotheses.
- Make weakening and contraction explicit.
- Support conjunction, implication, equality rewriting, universal
  instantiation, and existential witness nodes.
- Reconstruct Lean proof terms for a generated template corpus.

## Later research

- certified contraction/linear-time correctness checking;
- cut links and cut elimination as graph rewriting;
- additives, exponentials/boxes, and unification nets;
- hierarchical proof graphs for dependency-rich mathlib theorems;
- a `proofnet_ai` tactic that treats all model output as untrusted input.

The success criterion is empirical and kernel-checked. A visually appealing
graph or a lower token count without matched proof success is not enough.
