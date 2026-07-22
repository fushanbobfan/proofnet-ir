# Changelog

## Unreleased

- added `LinkPermutationEquivalent` and the generated `ProofNetEquivalent`
  relation so general sequentialization can ignore semantically irrelevant
  link-list storage order without weakening ordered conclusions or connective
  premises;
- proved in Lean that arbitrary link permutation preserves structural
  well-formedness, all independent par switchings, declarative correctness,
  `Correct`, and the executable checker;
- added a regression certificate that is checker-equivalent under link
  permutation but provably not in the narrower `ReindexEquivalent` class.
- defined the evidence-rich `SequentializationResult` contract and proved it
  transports checker acceptance, ordered boundary labels, and kernel-typed
  derivations;
- added vertex deletion/compaction laws plus a checker-gated terminal-par
  inverse operation, with generated regression coverage over every terminal
  par found in 250 deterministic derivation-first certificates.
- added checker-gated splitting-tensor discovery with full-graph component
  partitioning, cross-link rejection, local renumbering, and two independently
  accepted premises; every one of the 250 generated non-axiom nets exposes at
  least one accepted inverse par or tensor step;
- began the universal graph proof: deleting an in-bounds vertex preserves
  boundedness, has exact incident-edge accounting, preserves the tree
  edge-count equation for leaves, and has an exact adjacency/walk embedding;
- completed the graph theorem that deleting any leaf of an `IsTree` graph
  yields another `IsTree`, including unique incident-edge reasoning,
  simple-walk leaf avoidance, and connectedness preservation.
- proved from certificate ownership and independent `ChoiceSelection`
  semantics that every terminal par conclusion is a degree-one leaf in every
  switching graph; also added the exact `TerminalParReduction` interface that
  turns switching-deletion evidence into checker preservation.
- proved that every proposition-level splitting tensor makes the executable
  candidate return two structurally well-formed certificates, including exact
  restriction/index transport, local link typing, duplicate-free boundaries,
  source ownership, and the root parent-use decrement on both components.
- proved that every switching of either splitting-tensor component lifts to an
  input switching as an exact induced restriction; the restricted graphs are
  bounded and connected because a same-side simple path cannot cross the
  degree-two terminal tensor separator.
- proved the finite connected-graph lower bound `V <= E + 1`, exact tensor
  vertex/edge partitions, and full `IsTree` preservation for both induced
  components; added `TerminalTensorReduction`, declarative/checker preservation,
  and total checker-gated splitting for every accepted splitting input.
- added formula-complexity ranks and proved that every structurally well-formed
  certificate containing a tensor/par link has a terminal connective link;
  the global existence of a splitting tensor remains separate.
- added edge-indexed oriented multigraph edges and composable/reversible
  edge-aware walks, preserving parallel-edge identity and projecting soundly
  to the existing checker-facing vertex walk semantics; this is the base layer
  for the remaining colored-path/Yeo proof.
- added edge-aware simple multigraph cycles, exact full-edge source annotations,
  local switching-incidence colors, cusp semantics, and reversal invariance;
  proved that every stored par link yields two exact indexed incidences aimed
  at its conclusion with the shared par color.
- proved simple-cycle edge indices are duplicate-free and bounded by the
  stored multigraph edge count, including genuine two-parallel-edge cycles.
- strengthened tree counting from edge values to stored occurrences: in every
  `IsTree`, shortest-path parent-edge indices of non-root vertices occupy every
  edge index exactly once, including in multigraphs.
- proved the full occurrence-level acyclicity theorem: `IsTree` excludes every
  edge-aware simple multigraph cycle, by a minimum shortest-path-rank argument;
  added a kernel-checked triangle-cycle regression independent of `isTree`.
- added a full-occurrence switching mask relation, proved it equivalent to the
  independent one-edge-per-par `ChoiceSelection`, and proved its retained
  multiset is exactly the checker switching graph up to edge-list order.
- proved the full correctness-to-colored-acyclicity bridge: a cusp-free exact
  multigraph cycle uses at most one premise occurrence from each par pair,
  admits a switching mask that preserves every cycle edge, and therefore
  contradicts `IsTree`; `DeclarativelyCorrect.cuspAcyclic` now states the
  kernel-checked result for every independent switching.
- added duplicate-free exact-edge simple paths, cusp-free continuations and
  their disjointness-safe concatenation; defined the strengthened directed-edge
  ordering used by generalized Yeo and proved it irreflexive and transitive.
- added both-orientation enumeration of every stored edge occurrence and a
  generic theorem that every nonempty duplicate-free finite list has a maximal
  member under any irreflexive transitive relation.
- added exact-edge simple-cycle reversal and simple prefix extraction; defined
  closing cusps, splitting vertices, cusping edges, and a finite internal-cusp
  count with its cusp-free characterization.
- proved that a cusp-acyclic non-splitting vertex admits a freely closing cycle
  with a nontrivial internal cusp, and that a freely oriented such cycle yields
  a simple cusp-free continuation to its first cusping edge. The universal
  separation condition required by generalized Yeo remains open.
- proved cusp-count additivity with an explicit concatenation boundary and
  invariance under full traversal reversal; minimal freely closing cycles can
  therefore be reoriented without losing minimality.
- added exact simple-path prefixing, truncation of cusp-free continuations at
  their first intersection with a finite vertex list, structural looplessness
  of full proof-net occurrences, and the two cusp-adjacent head-edge exclusion
  lemmas needed by the remaining bungee contradiction.
- proved exact simple-path reversal, suffix extraction, source/target and edge
  occurrence uniqueness, and a constructor closing two oppositely directed
  simple paths into an occurrence-aware simple cycle.
- constructed the normalized first-intersection bungee cycle with verified
  vertex and edge disjointness, and proved cusp-acyclicity forces a cusp at its
  splice from the later prefix into the old return suffix. Minimal-cycle cusp
  arithmetic remains the next bungee obligation.
- proved that normalized intersection cycle has exactly one internal cusp and
  that a one-cusp concatenation split at its cusp has two cusp-free pieces.
- added exact simple-cycle rotation and complementary wrap-around path
  extraction, preserving occurrence identity and vertex simplicity; these are
  the graph constructors needed for the minimal-cycle rerouting step.
- proved cyclic cusp-count invariance under list rotation; strengthened the
  complementary arc with base-vertex and edge-occurrence containment; and
  constructed the first-return bungee splice as an exact simple cycle that can
  be rotated back to the original base. The remaining obligation is to prove
  the rotated splice closes cusp-free and derive the strict minimality
  inequality.
- normalized that same-base splice to an exact traversal formula, proved its
  closing transition is free, and completed the minimal cusp-count inequality;
  for every first intersection strictly away from the old base, the removed
  arc and later path now close into a forbidden cusp-free simple cycle. The
  degenerate first-hit-at-base orientation branch remains before universal
  bungee separation is complete.
- closed both endpoint orientations of the hit-at-base branch with two exact
  same-base replacement cycles. Consequently the oriented bungee
  contradiction is complete for every first hit at or before the selected
  cusp; the symmetric wrap-around case where the first cycle hit lies after
  the cusp remains.
- completed the symmetric after-cusp wrap-around branch: extracted exact old
  wrap/segment paths, built the same-base replacement, proved closing and
  minimal cusp-count constraints, and closed the final forbidden cusp-free
  cycle. What remains is the exhaustive first-intersection position classifier
  and the adjacent hit at the incoming cusp edge's source.
- completed the adjacent incoming-edge branch by reversing the ambient cycle
  when the old prefix is nonempty and by a two-orientation same-base
  minimality argument at the old base; the exhaustive first-intersection
  classifier now covers every source occurrence and excludes the cusp partner
  by simple-path freshness.
- upgraded the minimal first-cusp continuation to a genuine `OrderingPath`,
  proved that every non-splitting target has a strict cusping
  `EdgeOrdering` successor, and closed finite generalized-Yeo maximality to
  obtain a colored `SplittingVertex` in every nonempty cusp-acyclic occurrence
  graph.
- added exact par/tensor annotation-origin lemmas, cusping-occurrence inversion,
  cusping-restricted maximality, and a generic lift from duplicate-free vertex
  walks to exact occurrence-aware simple paths; proved
  `SplittingVertex.toSplittingTensor`, closing the colored-to-deletion splitting
  bridge for terminal tensors without collapsing parallel stored edges.
- defined the representation-specific `SequentializationEdge` carrier and
  proved the exact parent occurrence of every non-boundary carrier target gives
  a strict `EdgeOrdering` successor with the full universal separation field;
  finite parametrized generalized-Yeo maximality now yields a target that is
  both colored-splitting and terminal.
- proved `DeclarativelyCorrect.terminalPar_or_splittingTensor_exists` and the
  checker-facing corollary: every accepted certificate containing a connective
  exposes a mathematical terminal par or splitting tensor. The remaining main
  theorem is well-founded recursive reconstruction plus output equivalence.
- proved strict formula-occurrence decrease for terminal-par peeling and for
  both components of every splitting-tensor restriction, establishing the
  measure obligations needed by well-founded sequentialization.
- completed the axiom-only recursive base: correctness forces exactly two
  occurrences and one axiom; its boundary and endpoint orientation are
  classified exhaustively, and every case now yields a full
  `SequentializationResult` with a kernel-checked derivation tree and explicit
  proof-net equivalence.

## v0.3.1 - Complete order-preserving reindex normal forms

- proved that structural well-formedness makes the first-occurrence traversal
  a duplicate-free enumeration of exactly all formula vertices;
- constructed the explicit bounded `VertexRenaming` induced by that traversal
  and proved normalization is literally an in-class reindexing of every
  structurally well-formed certificate;
- proved the converse theorem: for structurally well-formed certificates,
  equal v0.3 certificate normal forms are equivalent to `ReindexEquivalent`;
- added the executable `reindexEquivalent?` decision procedure with iff
  theorems for structurally well-formed and checker-accepted inputs;
- proved v0.3 normalization preserves checker acceptance for every accepted
  certificate, not only the generated regression corpus.

No JSON field, `reindex-v1` algorithm, or accepted-certificate semantics
changed from v0.3.0.

## v0.3.0 - Checked input and reindex-invariant wire keys

### Included

- added a `VertexRenaming` equivalence layer with inverse round trips and
  kernel-checked invariance of structural validation, switching semantics,
  declarative correctness, and the complete Boolean checker;
- added the versioned v0.3 `reindex-v1` normal-form key and proved that every
  pair of `ReindexEquivalent` certificates has exactly the same serialized
  key;
- retained v0.2 decoding, added v0.3 decoding and a v0.2-to-v0.3 migration API,
  and validated both formats through the checker-gated untrusted-input
  boundary;
- added a v0.3 JSON Schema and fixture, 250 generated Lean round trips, and an
  independent 1,000-record property audit covering deterministic vertex
  permutations, schema validity, idempotence, and link-order sensitivity;
- published an explicit compatibility policy for Lean and wire-format APIs.

### Explicit boundaries

- the proved direction is `ReindexEquivalent -> equal reindex-v1 key`; a
  converse/completeness theorem and a proof that normalization constructs an
  in-class representative for every structurally well-formed certificate are
  still open;
- `reindex-v1` preserves link order, conclusion order, tensor/par premise
  order, and axiom endpoint order. It is not arbitrary graph-isomorphism
  canonical labeling;
- general sequentialization of every checker-accepted net remains open.

- added an independent conclusion-inference pass for first-order derivation
  trees and proved `infer?_sound`: every successful inference denotes a
  kernel-typed `Derivation`;
- strengthened explicit exchange validation with a checked `List.Perm`
  boundary and `reorder?_perm` theorem;
- added `elaborate?`, whose result connects the inferred sequent, a
  kernel-typed derivation, matching proof-net conclusion labels, and checker
  acceptance in one public boundary;
- added honest source-coverage and library-readiness audits so targeted reading
  and research-prototype functionality cannot be presented as completion.
- added a separate downstream Lake consumer that imports the public library,
  exercises certificate checking and `elaborate?`, and runs in CI.
- recorded a representation-level comparison with the primary Rocq proof-net
  formalization to guide sequentialization without silently copying a theorem
  for a different graph model.
- added a native Lean parser for canonical v0.2 JSON, path-aware parse errors,
  canonical-form validation, and a safe checked-input boundary for untrusted
  external certificates.
- formalized loop erasure for arbitrary inductive graph walks and proved the
  uniform `vertexCount` path bound on bounded graphs;
- strengthened the public specification to full iff theorems
  `isTree_iff_isTree`, `check_iff_correct`, and
  `check_iff_declarativelyCorrect` for unbounded walk semantics, and proved
  the unbounded and fuel-indexed correctness contracts equivalent.
- completed a text-and-visual audit of all 33 pages of *Geometry of
  Neuroscience*, with a per-page matrix that classifies it as adjacent
  generated exposition and forbids using it as evidence for proof-net
  correctness, sequentialization, canonicalization, or performance.
- added a lossless certificate-reindexing foundation: bounded bijective vertex
  renamings preserve out-of-bounds status, transport ordered links and
  conclusions, commute with formula lookup, and recover the literal source
  certificate after applying the transported inverse; local link typing and
  node ownership/count predicates are proved invariant;
- completed whole-certificate reindexing invariance for structural validation,
  graph adjacency and walks, boundedness, connectedness, declarative tree
  semantics, switching correctness, and the executable checker; added the
  reflexive, symmetric, and transitive `ReindexEquivalent` relation and proved
  it preserves `Correct` and `DeclarativelyCorrect`. Canonical v0.2 JSON remains
  intentionally numbering-sensitive; v0.3 adds a separate reindex-invariant
  key without changing the v0.2 contract.

## v0.2.0 - Derivation trees, canonical data, and focused baseline

### Included

- first-order arbitrary cut-free MLL derivation trees with explicit resource
  positions and exchange permutations;
- validated general desequentialization from those trees to proof-net
  certificates, plus a checked result that carries `certificate.check = true`;
- a deterministic derivation generator whose first 250 depth-two trees all
  desequentialize and pass the reference checker;
- versioned canonical certificate JSON that normalizes link order, conclusion
  order, and symmetric axiom orientation while preserving formula-array vertex
  identities;
- a committed, deterministic 1,000-record JSONL dataset with 250 valid
  derivation outputs and 750 labeled corruptions, checked again by the
  independent Python oracle;
- a runnable focused cut-free one-sided MLL search baseline with eager par
  decomposition, exhaustive tensor/resource-split search, memoization, and
  search counters;
- schemas, dataset manifest/checksum, regeneration checks, smoke fixtures, and
  GitHub CI coverage for the entire path.

### Explicit boundaries

- canonical serialization is not graph-isomorphism canonicalization;
- desequentialization is general, but reverse sequentialization of every
  checker-accepted proof net is still not implemented;
- the dataset is a correctness/repair substrate, not evidence that graph
  generation outperforms focused proof search.

## v0.1.1 - Mathematical audit hardening

### Changed

- audited the compiled checker against an independent Python oracle on all
  33,868 simple undirected graphs through six vertices and 1,000 generated or
  mutated proof-net certificates;
- added proposition-level link, node, and certificate structural semantics and
  proved `wellFormed_iff_structurallyWellFormed`;
- strengthened `DeclarativelyCorrect` and `FuelDeclarativelyCorrect` so their
  structural premise no longer calls the Boolean checker;
- changed formula Boolean equality to the lawful instance derived from
  `DecidableEq`;
- added multigraph parallel-edge regression coverage and made the audit a
  required CI step.

No v0.1 certificate schema or accepted-fragment semantics changed.

## v0.1.0 - Verified MLL reference core

### Included

- pinned Lean 4.32.0 toolchain and reproducible Lake build;
- unit-free, cut-free MLL formulas, occurrences, axiom/tensor/par links, and
  structural certificate checks;
- exhaustive par-switching enumeration plus an independent inductive
  one-edge-per-par selection semantics;
- finite graph tree checking with independent unbounded and fuel-indexed walk
  semantics;
- checker soundness for declarative switching correctness and soundness/
  completeness for the independent fuel-indexed contract;
- explicit exchange and recursive identity derivations for `A, A-dual`;
- recursive canonical identity-certificate generation and certificate-gated
  reconstruction;
- labeled invalid mutations, 61 compile-time assertions, and a 210-formula
  generated sanity corpus;
- versioned JSON Schema and valid/invalid fixtures;
- CI, architecture, trust-boundary, literature, experiment, and reading-ledger
  documentation.

### Explicit non-goals

- general sequentialization of every accepted MLL proof net;
- a proof that every unbounded walk normalizes within `vertexCount` steps;
- units, Mix, cut, additives, exponentials, quantifiers, or a Lean tactic;
- a claim that graph generation outperforms focused sequent proof search.

These items remain tracked in `docs/roadmap.md` and are not implied by the
v0.1.0 release label.
