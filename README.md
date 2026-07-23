# ProofNet-IR

ProofNet-IR is an experimental, verified proof-geometry intermediate
representation for AI-guided theorem proving in Lean 4.

Current release: `v0.8.0` (a proved non-factorial exact typed key for
the documented `ProofNetEquivalent` relation, a separately versioned bounded
wire contract, and measured qualification through 145 links, without claiming
arbitrary graph isomorphism or general checker/sequentializer scalability). See
[CHANGELOG.md](CHANGELOG.md) for the precise guarantees and non-goals.

The v0.8 release adds a proved non-factorial intrinsic canonical
form and the separate `proofnet-canonical-key-0.2` wire. On
structurally well-formed certificates, equality of the new typed key is proved
equivalent to exactly the existing `ProofNetEquivalent` relation. It does not
change that relation or claim arbitrary graph isomorphism.

The research hypothesis is that a model should sometimes predict proof
geometry before it predicts a tactic sequence. A graph certificate can factor
out arbitrary ordering between independent inferences, expose dependency
structure, and support local repair. The Lean kernel remains the final source
of trust.

> 中文简介：本项目研究能否让 AI 先生成可检查的证明图，再由确定性程序重建
> Lean 证明，从而减少 tactic 顺序造成的搜索冗余。当前版本从无单位、无 cut 的
> multiplicative linear logic (MLL) 开始，不声称已经覆盖普通 Lean/mathlib 证明。

## Current vertical slice

The repository currently contains:

- a unit-free MLL formula language with involutive De Morgan duality;
- explicit formula occurrences and typed `axiom`, `tensor`, and `par` links;
- executable structural well-formedness checks;
- independent proposition-level structural semantics and an iff theorem for
  the executable structural checker;
- exhaustive enumeration of all par switchings;
- an independent inductive `ChoiceSelection` relation and an iff theorem
  proving the enumerator covers exactly all one-edge-per-par switchings;
- a finite undirected graph checker for boundedness, connectedness, and the
  `|E| + 1 = |V|` tree condition;
- a Lean theorem `check_sound` connecting executable acceptance to an
  independent inductive walk semantics;
- kernel-checked loop erasure and a finite-vertex path bound, yielding full
  checker soundness and completeness for that standard unbounded semantics;
- exact soundness and completeness against an independent fuel-indexed path
  semantics: `closureN fuel` iff a path of at most `fuel` steps is available
  when stored edges are in bounds;
- `check_iff_fuelDeclarativelyCorrect`, lifting both the path and switching
  correspondences to the complete certificate checker;
- `check_iff_declarativelyCorrect`, proving the Boolean checker decides the
  public Boolean-free, unbounded switching specification;
- explicit exchange/permutation plus recursive identity expansion proving
  `|- A, A-dual` for every unit-free MLL formula;
- a first-order arbitrary cut-free derivation-tree language with explicit
  resource positions and exchange permutations;
- an exact synchronization theorem proving that formula inference succeeds iff
  occurrence-aware fragment construction succeeds with the same ordered
  formula boundary, including exchanges between duplicate labels;
- a kernel theorem proving that every successfully constructed fragment's
  public certificate lookup recovers exactly that ordered formula boundary;
  separate structural-composition and switching-composition theorems now prove
  every such fragment declaratively correct and executable-checker accepted;
- totality of both `desequentializeChecked?` and `elaborate?` for every rule
  tree accepted by the independent `infer?` pass;
- general validated desequentialization of those trees, with a checked return
  type carrying `certificate.check = true`;
- a deterministic broad-family derivation generator whose first 250
  depth-two trees all produce accepted certificates;
- a derivation-first generator for the corresponding canonical identity
  certificate at arbitrary formula depth, with exact certificate-gated
  reconstruction;
- a finite formula enumerator whose depth-two one-atom corpus checks all 210
  generated identity certificates;
- labeled negative-certificate mutations, compile-time regression assertions,
  and an executable smoke test.
- an independent CI differential audit over 33,868 exhaustive graphs and
  1,000 generated or mutated certificates.
- versioned canonical v0.2 JSON plus a committed deterministic dataset of 250
  positive and 750 negative checker-labeled records;
- a native v0.2/v0.3 JSON parser with path-aware errors, a v0.2-to-v0.3
  migration API, a checker-gated API for untrusted certificates, and a
  deterministic 5,000-case malformed-input fuzz gate;
- a runnable focused cut-free sequent-search baseline with eager invertible par
  steps and exhaustive tensor resource partitions;
- lossless bounded vertex reindexing with inverse round trips, a proved
  equivalence relation, and whole-checker/declarative-correctness invariance.
- a v0.3 `reindex-v1` serialized normal-form key proved invariant under that
  relation, plus an independent 1,000-record permutation/property audit.
- a theorem that this normal form is an in-class representative and a complete
  invariant for structurally well-formed certificates, plus the executable
  `Certificate.reindexEquivalent?` decision procedure.
- a well-founded logical sequentialization theorem: every checker-accepted
  certificate has a kernel `Derivation` whose sequent is exactly the ordered
  list of its conclusion formulas.
- a full well-founded sequentialization theorem: every checker-accepted
  certificate has a concrete first-order `CutFreeDerivation`; its executable
  desequentialization is `ProofNetEquivalent` to the input and carries the
  same ordered formula boundary.
- the v0.5 executable `Certificate.sequentialize` API that searches
  checker-preserving inverse rules and returns a proof-bearing tree, exact
  ordered input boundary, accepted desequentialization, and
  `ProofNetEquivalent` output. `Certificate.sequentialize_complete` proves this
  runtime search succeeds for every checker-accepted certificate; it also
  passes all 250 broad generated regressions, the same 250 nets with every link
  list reversed, and a dedicated repeated-boundary-label regression.
- an executable finite `proofNetCanonicalFamily` whose extensional membership
  equality is proved equivalent to exactly `ProofNetEquivalent` on
  structurally well-formed certificates. This is a factorial specification
  oracle, not a compact wire key or arbitrary unlabeled-graph canonicalizer.
- a released experimental `proofNetCanonicalFingerprint?` value that selects the
  lexicographically least serialized member of that family. Lean proves it is
  total and invariant under `ProofNetEquivalent`; the JSON-string API remains a
  forward-only convenience because no `Json.compress` injectivity theorem is
  assumed;
- an explicitly versioned `proofNetCanonicalCode?` token key.
  Its underlying structural encoder is proved injective, and Lean proves on
  structurally well-formed certificates (hence on checker-accepted inputs) that
  code equality is equivalent to exactly `ProofNetEquivalent`. It still
  materializes the factorial family;
- a released `proofnet-canonical-key-0.1` JSON wire wrapper with a bounded
  parser, structured errors, schema and fixture, v0.3-to-key semantic migration,
  and a safe matcher theorem for untrusted parsed keys. Public generation and
  matching reject inputs above seven links before factorial materialization;
  the exact typed key remains an unbounded specification oracle. Its 1,000-case
  wire property corpus, 5,000-case malformed-key fuzz corpus, and measured
  1/4/7-link benchmark pass, but larger or ordinary pairwise comparisons should
  use `CheckedCertificate.sameProofNet?`;
- an intrinsic canonicalizer that traverses the ordered conclusion
  forest, follows each unique tensor/par producer in premise order, emits every
  orientation-sensitive link exactly once, and then erases submitted vertex
  numbers. Lean proves exact traversal coverage, exact link permutation,
  in-class representation, and equality iff `ProofNetEquivalent` on the
  structurally well-formed domain. The separate
  `proofnet-canonical-key-0.2` wire removes the seven-link ceiling and has been
  differentially checked against the factorial oracle on 1,000 deterministic
  cases and exercised on 1,000 additional mixed derivation-generated accepted
  nets; its direct implementation is polynomial, currently
  `O(VL + V^2)`, and still enforces independent token/character limits;
- a clean downstream Lake consumer pinned to the exact public `v0.7.0` tag,
  exercising bounded-key exactness, safe matching, over-limit
  failure, and executable sequentialization;
- a checked pairwise identity API,
  `CutFreeDerivation.CheckedCertificate.sameProofNet?`, proved to decide
  exactly `ProofNetEquivalent`. Its search enforces the ordered conclusion
  boundary and numeric-free one-hop incident-link roles while generating
  formula-occurrence alignments; a 64-pair
  repeated-label stress case generates one candidate instead of the
  unconstrained label enumerator's theoretical `(64!)^2` orders. This remains
  an exact scoped decision procedure, not a compact canonical wire key or an
  arbitrary graph-isomorphism algorithm;
- a conservative v0.6 LeanProp bridge with judgments
  indexed by separate persistent and linear proposition contexts. Persistent
  weakening/contraction and both exchanges are explicit, while no linear
  weakening/contraction constructors exist. Conjunction, implication,
  equality rewriting, universal instantiation, and existential witnesses are
  interpreted into actual Lean proof terms; a kernel theorem proves that the
  number of linear-axiom leaves equals the linear-context length. The explicit
  exchange syntax represents exactly `List.Perm` under `Nonempty`; every such
  persistent or linear exchange is admissible, and transporting a dependent
  proof environment through exchange and its inverse is identity in both
  directions. A typed normalizer recursively removes every immediate
  persistent contraction-over-weakening redex; Lean proves the result reduced,
  the operation idempotent and size-nonincreasing, and the linear-resource
  count and proof interpretation preserved. This is a noncomputable
  proof-construction API over proposition-indexed derivations, not a runtime
  raw-schema normalizer;
- a proposition-independent schema layer for generated atoms/conjunctions/
  implications. Its 600-template deterministic corpus covers persistent
  duplication/discard, linear pairing/exchange/modus ponens, and projection;
  every packed schema has a universal theorem reconstructing a Lean proof
  under every atom valuation. A separate unindexed checker infers exact
  persistent/linear sequents, returns stable path-aware diagnostics, and has a
  theorem that every erased indexed schema is accepted with its original
  boundary. CI checks all 600 erased positives and 1,000 malformed templates
  covering every error code. A strict `leanprop-schema-0.1` JSON contract,
  native Lean parser, checker-gated entry point, checked fixtures, and separate
  deterministic 5,000-case mutation-fuzz gate now cover untrusted strings. A
  Lean-emitted 1,600-record stream has a CI-checked SHA-256 manifest. Every
  accepted raw/wire schema is now elaborated into an indexed derivation, and
  the checked API exposes universal Lean proof reconstruction;

The universal v0.4 theorem still returns
`Nonempty (SequentializationResult input)` in `Prop`. The new runtime API does
not extract that witness by choice: it performs finite inverse-rule and
occurrence-permutation search, permits semantically irrelevant link-list
permutation, and rechecks its output. Its separate totality theorem is proved
by the terminal-rule dichotomy, checker-gated candidate totality, complete
finite boundary alignment, and well-founded fuel induction. The path-based
downstream consumer executes the API and consumes that theorem, and CI
  separately audits forty-five public MLL logical-boundary theorems against the exact axiom set
`[propext, Classical.choice, Quot.sound]`. LeanProp boundaries are audited
separately: the proof-term interpreter, proposition-level permutation
completeness, and the two exchange-admissibility theorems are axiom-free.
Resource-count, dependent-environment round trips, packed-schema soundness,
permutation elaboration, checked-wire soundness, and six structural-
normalization theorems use exactly `propext`. Exact agreement between
formula-only inference and typed elaboration, its acceptance-lifting
corollary, checked-wire inference, and the normalizer size bound use exactly
`[propext, Quot.sound]`.

This remains a research prototype rather than a mature general-purpose
library. The supported unit-free, cut-free MLL reverse-sequentialization
theorem is now complete, but its certificate model does not include cut
elimination, units, exponentials, additives, or quantifiers. The experimental
LeanProp layer has quantifier proof-template nodes but no claim of proof-net
semantics; its wire layer intentionally covers only named atoms, ordinary
conjunction, and implication, not typed equality/quantifier terms or broad
mathlib expressions. The
repository also lacks canonicalization modulo reordered conclusions or
arbitrary graph isomorphism, a stable release and broader adversarial
qualification of the new non-factorial key, optimized checking and
sequentialization, and a Lean tactic. The API,
diagnostics, compatibility, performance, independent downstream, and
large empirical readiness criteria are tracked separately and are not implied
by the theorem.

## Trust path

```text
untrusted derivation tree or certificate
        |
        v
validated desequentialization (when starting from a derivation)
        |
        v
structural well-formedness + every switching is a tree
        |
        v
Lean theorem: accepted -> declarative correctness
        |
        v
kernel `Derivation` with the exact ordered input sequent
        |
        v
Lean kernel
```

The external AI, JSON input, and future graph proposer are untrusted. Use
`Certificate.checkedFromString` to parse and validate an external canonical
v0.2 or reindex-normalized v0.3 certificate before exposing it to trusted code.
See [docs/trust-model.md](docs/trust-model.md) for the exact boundary.

The separate LeanProp wire API does not expose accepted JSON as mere syntax:
`LeanProp.Schema.Raw.Derivation.checkedFromString` returns an indexed
derivation, `CheckedDerivation.inferred` recovers the exact checked sequent,
and `CheckedDerivation.sound` reconstructs its Lean proposition under every
atom valuation and matching persistent/linear proof environment.

```lean
match Certificate.checkedFromString input with
| .ok checked => -- checked.accepted : checked.certificate.check = true
    useCertificate checked.certificate
| .error error =>
    report error.path error.message
```

## Build

Prerequisites: Git and [Elan](https://github.com/leanprover/elan). The pinned
Lean version is recorded in `lean-toolchain`.

```powershell
lake build
lake exe proofnet_ir_tests
python scripts/generate_dataset.py --check
python scripts/audit_v03_canonical.py
lake exe proofnet_ir_api_docs --check
python scripts/fuzz_malformed_parser.py
lake exe proofnet_ir_benchmark
python scripts/focused_search.py examples/focused-sequent-v0.2.json --require-found
python scripts/run_matched_experiment.py --check-committed
python scripts/run_model_experiment.py --check-preregistered
python scripts/run_model_experiment_amended.py --check-amendment
python scripts/run_model_experiment_amended.py --check-committed
```

Expected smoke-test output:

```text
ProofNetIR: all certificate and v0.3 fixture checks passed
```

## Repository map

```text
ProofNetIR/Formula.lean       MLL formulas and linear negation
ProofNetIR/Certificate.lean   occurrences, links, and structural validation
ProofNetIR/Reindex.lean       lossless bounded vertex renaming and transport
ProofNetIR/Graph.lean         finite graph closure and declarative tree property
ProofNetIR/Checker.lean       switchings, executable checker, soundness/completeness
ProofNetIR/Reconstruct.lean   supported sequent derivation reconstruction
ProofNetIR/Generate.lean      recursive derivation-first identity certificates
ProofNetIR/Mutation.lean      labeled corruptions for negative fixtures
ProofNetIR/DerivationTree.lean arbitrary cut-free trees and desequentialization
ProofNetIR/GraphComposition.lean tree-preserving par/tensor graph composition
ProofNetIR/SwitchingComposition.lean switching correctness under rule composition
ProofNetIR/StructuralComposition.lean structural correctness under rule composition
ProofNetIR/DesequentializationSoundness.lean derivation-to-certificate invariants
ProofNetIR/NetEquivalence.lean semantic equivalence and checker invariance
ProofNetIR/Sequentialization.lean general theorem contract and inverse-rule work
ProofNetIR/LocalIdentity.lean proved local invariants for exact identity pruning
ProofNetIR/ExecutableSequentialization.lean runtime inverse search and diagnostics
ProofNetIR/ProofNetIdentity.lean checked exact pairwise proof-net identity API
ProofNetIR/StructuralCode.lean injective exact-key structural token encoding
ProofNetIR/CanonicalKeyWire.lean bounded exact-key wire and safe matching
ProofNetIR/IntrinsicCanonical.lean non-factorial exact canonical representative
ProofNetIR/IntrinsicCanonicalKeyWire.lean v0.2 intrinsic-key wire and migration
ProofNetIR/Serialization.lean v0.2 fixed-number and v0.3 reindex wire formats
ProofNetIR/Parser.lean        v0.2/v0.3 parser, migration, checked-input boundary
ProofNetIR/LeanPropNormalization.lean typed persistent structural normal form
ProofNetIRTests.lean          positive/negative compile-time and smoke fixtures
ProofNetIRDataset.lean        deterministic 1,000-record dataset emitter
ProofNetIRParserFuzz.lean     stdin driver for native malformed-input fuzzing
ProofNetIRBenchmark.lean      checked depth-2/3/4 runtime regression budget
ProofNetIRAPIDocs.lean        generated public API manifest and reference
ProofNetIRExperimentCorpus.lean deterministic matched-task corpus emitter
ProofNetIRModelExperimentCorpus.lean held-out model-task base emitter
ProofNetIRExperimentVerify.lean Lean checker/sequentializer batch boundary
consumer-smoke/               independent downstream Lake dependency test
consumer-release-smoke/       clean consumer pinned to public v0.5.0 tag
consumer-v06-candidate-smoke/  clean consumer pinned to public v0.6.0 tag
consumer-v07-candidate-smoke/  clean consumer pinned to public v0.7.0 tag
consumer-v08-candidate-smoke/  clean consumer pinned to public v0.8.0 tag
schemas/                      versioned external certificate contract
examples/                     valid and invalid JSON certificates
datasets/v0.2/                committed checker-labeled corpus and manifest
datasets/leanprop-v0.1/       Lean-emitted schema corpus manifest
scripts/focused_search.py     focused cut-free comparison baseline
scripts/run_matched_experiment.py matched generation/repair experiment runner
scripts/run_model_experiment.py preregistered held-out model experiment runner
scripts/run_model_experiment_amended.py hard-timeout protocol amendment runner
scripts/audit_v03_canonical.py independent 1,000-record reindex-key audit
scripts/fuzz_malformed_parser.py deterministic 5,000-case parser fuzz gate
docs/                         architecture, literature map, roadmap, trust boundary
```

## Scientific status

The first deterministic matched experiment is complete: under a fixed
1,000-unit per-method budget on 1,000 positive derivation-generated MLL tasks,
focused search solved 760, while formula-skeleton proof-net generation and
one-edit repair solved all 1,000. Lean rejected every distinct mutation and
accepted plus executably sequentialized every distinct claimed certificate.
The [full report](experiments/matched-v0.1/README.md) explains why this does not
show that proof graphs generally outperform focused search or tactic
generation: most atom labels are unique, the graph method receives the full
formula skeleton, repair starts one edit from a valid net, and no learned model
or ordinary Lean goal is involved.

A second 180-task study is now preregistered across depths 2--4, repeated-label
and unique-label strata, balanced positive/negative tasks, and reference repair
distances two/three. All 360 model calls are frozen, but the original runner's
soft-only wall-clock budget prevented scoring from completing in 120 minutes.
A public amendment preserves the original runner and every response while
adding process-level hard deadlines. Final results are now committed: focused
search 85/180, net generation 160/180, constructed distance-ordered repair
180/180, model direct 117/180, and model repair 2/180. Model direct was only
27/90 on positives despite 90/90 on deliberately atom-imbalanced negatives.
See the [final report](experiments/model-v0.2/report.md) for the exact receipt
and limitations.

The broader plan is in [docs/roadmap.md](docs/roadmap.md). Source screening and
project rationale are recorded in [docs/literature-map.md](docs/literature-map.md).
The current representative workload and its explicit scalability limitation
are recorded in [docs/performance.md](docs/performance.md). The auditable
source-coverage record is in
[docs/reading-ledger.md](docs/reading-ledger.md), and the first matched
evaluation is specified in
[docs/experiment-protocol.md](docs/experiment-protocol.md).
The stricter post-v0.2 coverage and reuse assessments are in
[docs/source-coverage-audit.md](docs/source-coverage-audit.md) and
[docs/library-readiness-audit.md](docs/library-readiness-audit.md). The
scoped v0.6 claims and release evidence are in
[docs/v0.6-release-audit.md](docs/v0.6-release-audit.md), and the exact-key
v0.7 release evidence is in
[docs/v0.7-release-audit.md](docs/v0.7-release-audit.md). The
external-consumer walkthrough is in [docs/tutorial.md](docs/tutorial.md), and
the kernel-environment-generated declaration surface is in
[docs/api-reference.md](docs/api-reference.md). The
representation comparison that guides general sequentialization is in
[docs/formalization-comparison.md](docs/formalization-comparison.md). Completed
page-level source audits, including Pfenning's 168 unique pages, Manin's 389
physical pages, Marcolli et al.'s 75 pages, the 33-page *Geometry of
Neuroscience* audit, and Park's 76 pages, live under
[docs/source-pages/](docs/source-pages/geometry-of-neuroscience.md).
Wire-version stability and migration rules are in
[docs/compatibility.md](docs/compatibility.md), and the exact v0.3 guarantees
are in [docs/v0.3-design.md](docs/v0.3-design.md).

## License

MIT. See [LICENSE](LICENSE).
