# Trust model

## Trusted

- the Lean 4 kernel selected by `lean-toolchain`;
- the compiled definitions and theorems in this repository, after `lake build`;
- the small object-logic derivation type used for supported reconstruction.
- the `CutFreeDerivation` rule syntax only after its occurrence positions and
  explicit exchange have passed `build?`;
- the proof carried by `desequentializeChecked?` that the resulting
  certificate passed the reference checker.

## Untrusted

- an AI model or graph neural network proposing certificates;
- prompts, retrieved text, local-model summaries, and imported papers;
- a future Python/TypeScript dataset generator or visualizer;
- the Python focused-search baseline and dataset regeneration wrapper;
- external JSON and the parsing path; callers should use
  `Certificate.checkedFromString`, whose return value includes the revalidated
  Lean checker acceptance proof;
- generated or external unindexed LeanProp schemas; callers must pass them
  through `LeanProp.Schema.Raw.Derivation.elaborate?` before treating them as
  typed derivations; `infer?` alone exposes only the formula boundary;
- LeanProp schema JSON and its parser; callers should use
  `LeanProp.Schema.Raw.Derivation.checkedFromString`, whose result retains a
  successful indexed elaboration and exposes `CheckedDerivation.sound`;
- benchmark labels not regenerated from checked certificates;
- the high-level claim that proof geometry improves proof search.

## Current theorem boundary

`Certificate.check_sound_declarative` states that executable acceptance
implies:

1. the Boolean-free `StructurallyWellFormed` proposition, including local link
   legality and exact occurrence ownership;
2. every graph satisfying the independent inductive `ChoiceSelection`
   switching relation satisfies `Graph.IsTree`.

`wellFormed_iff_structurallyWellFormed` proves that the executable structural
pass is sound and complete for independent proposition-level definitions of
link, node, conclusion, and resource-use discipline. Formula Boolean equality
is supplied by `DecidableEq`, so Lean also has its `LawfulBEq` proof.

`mem_switchingGraphs_iff` proves that the executable enumeration contains
exactly those independently described switchings, closing the risk that an
enumerator bug could silently omit a par choice from the semantic contract.

`Graph.IsTree` is a proposition over bounded edges, an independent inductive
`Graph.Walk` from vertex zero to every in-bounds vertex, and the edge-count
equation. `reachable_sound` proves that membership in the finite closure really
produces such a walk; the proof proceeds through closure preservation and does
not define a walk to mean "the algorithm returned true."

`WalkN` is a second independent relation indexed by its exact number of edge
steps. `closureN_walkWithin` and `walkN_mem_closureN` prove that finite closure
at depth `fuel` is equivalent to the existence of a path of at most `fuel`
steps, provided stored edges are in bounds. `isTree_iff_fuelTree` and
`check_iff_fuelDeclarativelyCorrect` lifts both independent relations to the
complete certificate checker.

`Walk.toSimple` now erases loops from every arbitrary `Graph.Walk`.
`SimpleWalk.toWalkWithin` uses duplicate-free vertex counting to bound the
result by `vertexCount` when stored edges are bounded. Consequently
`connected_iff_connected`, `isTree_iff_isTree`, `check_iff_correct`, and
`check_iff_declarativelyCorrect` identify the executable checker with the
original unbounded public semantics. None of these results is the proof-net
sequentialization theorem.

An independent differential audit additionally compares the compiled checker
against a Python union-find/certificate oracle on every simple graph through
six vertices and 1,000 generated or mutated certificates. See
`docs/audit-v0.1.0.md`; this is regression evidence, not part of the trusted
kernel proof.

The supported reconstruction boundary is broader than a fixed fixture but
still explicit: `Derivation.identity` and `identityCertificate` cover the
recursive family `A, A-dual`, and `reconstructIdentity?` requires exact
certificate equality. It does not treat checker acceptance alone as permission
to return a preselected derivation.

v0.2 added the derivation-first direction for arbitrary first-order cut-free
trees: validated desequentialization constructs a candidate certificate and
gates the checked API on `Certificate.check = true`. The post-v0.5
`infer?_eq_some_iff_build?_conclusions` theorem proves that formula validation
and occurrence-aware construction succeed together. The subsequent
`desequentialize?_conclusionFormulas?` theorem proves that every successfully
constructed public certificate reads back exactly the inferred ordered
boundary. The composition proofs now additionally establish structural
well-formedness and every-switching tree correctness for every successful
build; `build?_check` and `desequentialize?_check` derive executable checker
acceptance rather than assuming it. The checked gate remains explicit in the
runtime API, while `desequentializeChecked?_exists_of_infer?` and
`elaborate?_exists_of_infer?` prove it cannot fail after successful `infer?`.
Release v0.4.0
also proves the reverse direction for the supported representation:
`sequentialization_of_check` maps every accepted certificate to a concrete
first-order tree whose executable output is `ProofNetEquivalent` to the
input. The theorem preserves the ordered formula boundary and does not identify
arbitrary unlabeled graphs. The v0.5 runtime path is independently tied to
that guarantee: `sequentialize_complete` proves that the public finite search
returns a proof-bearing result on every checker-accepted certificate.
The v0.9 development path separates verification from the reference checker:
`verifyDerivation?` checks a supplied tree through structural validation,
independent inference/desequentialization, and equality of the non-factorial
intrinsic canonicalizations. `reconstructDerivation?` performs fuel-bounded
terminal-rule search and calls that verifier, never `Certificate.check`.
Kernel theorems prove every successful result accepted and prove the exact
total decision equality `reconstructsDerivation = check`. The proof may use
the reference semantics; the compiled search definition does not. No runtime
theorem is claimed for this reconstruction path.

`unificationReconstruct?` adds a deterministic Guerrini-style candidate
producer. It manipulates ordinary runtime token/partition state and partial
derivation trees; none of that state is trusted. A result exists only after
`verifyDerivation?` validates the completed tree, and
`unificationFastCheck_sound` proves the resulting Boolean fast path cannot
accept an invalid certificate. `unificationCheck` is the exact public
decision: it is the sequential Figures 7--8 fast path `sequentialFastCheck`
alone, which accepts only a derivation that `verifyDerivation?` validates and
has no recursive fallback. Lean proves `sequentialFastCheck = check`, hence
`unificationCheck = check`, and a whole-program cost theorem counts every
operation of a run and bounds the count quadratically (D6). Rejection by the
eager or worklist candidates alone is inconclusive, and no linearity claim is
made: the implemented stack, bucket, and consumer-index structures are not
constant-time, and linearity is recorded as the later goal D6-linear.

The separate `SequentialUnification.lean` checkpoint narrows, but does not
close, that requirement. Lean proves exact submitted-link origin for every
entry in its reusable source-incidence index. `SourceIndex.Sound` is only a
provenance property: it does not establish lookup existence or uniqueness, and
both endpoints of a malformed self-axiom are intentionally inserted into one
bucket. Structural well-formedness now proves singleton lookup for every
in-bounds occurrence. Given an exact submitted par lookup, the stronger
positional theorem identifies that singleton with the same submitted link
index and link value; repeated labels or equal-valued links in another slot
cannot replace it. A successful bounded/tagged `NEXTAXIOM` result carries
the exact submitted axiom index/endpoints, final tags, and trace; its proof
fields establish tag-array size preservation, monotonicity of old true tags,
trace `Nodup`, input-false/output-true tagging of every trace occurrence and
both endpoints, input-unmarked endpoints, and `trace.length ≤ fuel`. Its
`Touched` carrier is the trace plus endpoints, and successive successful calls
have disjoint touched carriers when the second uses exactly `first.tags`. This
is the scope of the global no-revisit discipline; no result is claimed after
tags are reset or replaced. A separate oriented-route theorem proves that the
trace is an exact submitted source-left chain to the axiom endpoint actually
reached and relates that endpoint to either stored axiom orientation.
`SearchClearThrough` supports a local totality theorem: structural
well-formedness, state abstraction, freshness through the starting complexity
rank, and fuel greater than that rank imply success on the production index.
Full initial-carrier freshness yields the exact `rank + 1` budget. This does
not prove the carrier-size wrapper total or establish freshness in a later
Figure-7 scheduler state. Because success tags complexity-zero axiom
endpoints, the global low-rank predicate cannot itself be threaded to a second
call; later scheduling requires a route-local freshness invariant.

Its dynamic update immediately allocates and assigns a token and refines one
eager Figure-5 start step under `Abstractable` and `OrderedParents`; it is not
the delayed Figures 7–8 `init`/`new` transition. Missing,
ambiguous, tagged, marked, or malformed sources fail closed, with dedicated
regressions for zero fuel, out-of-bounds, tagged and marked starts, missing and
duplicate sources, stored-right orientation, initial rank-budget coverage, and
repeat rejection after threading the first result's tags. The executable and
its proof fields are trusted only after compilation like any other Lean
declaration; the regression observations remain untrusted evidence.

### Sequential Figure-7 layer

The delayed Figures 7–8 layer described in
[architecture.md](architecture.md#sequential-figure-7-layer) is subject to
the same boundary. The trust-relevant facts are:

- `RawTokenAge` in `SequentialSchedulerState.lean` is the immutable
  discovery-order age and is never a union-find representative. Guards must
  compare raw assigned ages, not representatives. A deliberately arbitrary
  ordered parent forest `#[0, 1, 0]` with `sigma = [0, 1]` refutes any
  automatic derivation of `RealizesSigma` from `WellShaped`, marks/horizon
  alignment, and `OrderedParents`; it is not proved reachable.
- The operational `new` initializes the old active `σ` boundary and leaves the
  freshly pushed top undefined. This is the project's interpretation of the
  paper's prose that defines `W` on nonactive boundaries, not an
  author-confirmed erratum or a uniqueness theorem for the printed display.
  The literal printed `newEnqueue?` is retained only as an audit helper and
  is not used by the production bridge.
- The two-level stack merge deterministically chooses
  `conclusion :: (payload ++ previousReady ++ activeReady)` although the source
  algorithm uses sets. The stored head-to-tail order and explicit provenance
  construction are representation refinements, not paper claims, and imply
  neither commutativity nor the paper's temporal order.
- Every Figure-7 theorem is conditional on its stated hypotheses:
  `SchedulerInvariant`, `DeclarativelyCorrect`, a supplied
  `CanonicalTagHistory`, `NewGuard`, or an already successful typed step.
  Preservation theorems say that a successful rule keeps an invariant that
  the input already satisfied; none proves that its hypotheses are reachable,
  that a rule is enabled, or that a run makes progress. The exact open targets
  are the [goal ledger](goal-ledger.md) items D1–D6.
- `Figure7/TailLaw.lean` proves C12 for correct initializations and its
  `nop`/`wait` implications, and `parHeadGuardTail_not_inductive` is a
  kernel theorem in the standard three-axiom boundary that exhibits a
  `SchedulerInvariant` state satisfying C12 whose canonical `nop` successor
  violates it. It shows that a reachable-state proof must carry more than
  `SchedulerInvariant` and C12; it does not show C12 false on reachable states.
- `Figure7/Termination.lean` bounds an executed history by
  `certificate.formulas.size` successful dispatcher calls. It counts calls and
  says nothing about the state in which a run stops.
- `ConclusionBelow`'s `NodeWellFormed` field is a local ownership check; it
  does not replace a whole-certificate `StructurallyWellFormed` or checked
  gate at a future untrusted dispatcher entry point.
- Fixed counterexample certificates (tensor adjacency, forged future events,
  route orientation, flat-scheduler confluence) live in test executables and
  use `native_decide` for closed certificate facts. They are executable
  regression evidence, not public three-axiom theorems.
- `proofnet_ir_new_progress_audit` and `proofnet_ir_tail_law_search` replay
  finite certificate sets and fail closed on budget exhaustion. Their zero
  failure counts are falsification evidence for the audited sets only.
- The exact trust audit (`scripts/audit_axioms.py`, `ProofNetIRAxiomAudit.lean`
  at `--trust=0`) classifies every maintained public theorem as
  standard-three (`propext`, `Classical.choice`, `Quot.sound`), axiom-free,
  `propext`-only, or `propext`/`Quot.sound`. Rolling totals and the exact
  checkpoint receipt live in [current status](current-status.md).
- The same script imports every library source module and checks every safe
  compiled declaration against the standard-three ceiling, including private
  helpers and modules outside the facade. Selection uses defining modules,
  not declaration namespaces. Placeholders, custom axioms, and native proof
  evaluation fail this gate; unsafe runtime declarations are outside it, and
  so are `example`s, which leave no declaration.

The eager and worklist candidates remain public.
`unificationDerivationCandidateWithStats` and `unificationReconstructWithStats`
certify at most `|links|²` eager link-list visits, and the worklist candidate
carries an axiom-free `n(n+4)+1` link-attempt cap; neither bound covers
frontier search, representative lookup, or verification, none is proved for
the sequential decision (D6), and no whole-program deadline follows. The
worklist receipt also implies no Figure-7 stack discipline: a
three-axiom, two-tensor certificate reconstructs with a noncontiguous age
merge, so callers and proofs must not assume contiguous age intervals,
adjacent stack union, or LIFO behavior for the flat worklist.

### Wire formats and identity keys

For LeanProp wire inputs, `inferAt_eq_elaborateAt` kernel-proves that the
formula-only raw checker and typed elaborator agree on acceptance, rejection,
error category, detail, and child path. `elaborate?_complete` proves every raw
checker acceptance has an indexed witness with the same boundary. The public
wire checker runs the elaborator directly, and `CheckedDerivation.sound`
forwards the resulting indexed term to `Schema.PackedDerivation.sound`. The
trust audit records the exact dependencies: the agreement/completeness
theorems and `CheckedDerivation.inferred` use `[propext, Quot.sound]`; the
permutation-boundary agreement and checked soundness theorem use `[propext]`.
At the typed context layer, permutation completeness and the two exchange-
admissibility theorems are axiom-free; the two dependent-environment inverse
laws use `[propext]`. Six public persistent-normalization theorems use
`[propext]`; the structural-size nonincrease theorem, whose arithmetic proof
uses the kernel-checked omega procedure, uses `[propext, Quot.sound]`.

Canonical v0.2 serialization trusts the formula-array numbering as occurrence
identity. Sorting links/conclusions and orienting axiom endpoints is a stable
wire-format rule, not a graph-isomorphism theorem. Dataset labels are emitted
by Lean and cross-checked by the independent Python oracle; the committed
dataset itself remains untrusted input when consumed by later experiments.

The separate v0.3 `reindex-v1` path first relabels vertices by their ordered
first occurrence in conclusions and links. Lean proves this value unchanged by
every bounded `VertexRenaming`. For structurally well-formed inputs, Lean also
proves traversal coverage, constructs the induced renaming, proves the normal
form is in the original class, and proves normal-form equality iff
`ReindexEquivalent`. The generic parser validates the declared algorithm and
normalized payload; logical acceptance is still rechecked separately.

For checker-accepted values, the supported production pairwise identity API is
`CheckedCertificate.sameProofNet?`. Lean proves its Boolean result is true iff
the two certificates satisfy exactly `ProofNetEquivalent`: bounded vertex
renaming followed by link-list permutation, preserving ordered conclusions,
connective premises, formula labels, and axiom orientation. The optimized
candidate generator enforces the ordered boundary during enumeration, and its
completeness feeds the already-audited exact decision theorem. This is neither
an arbitrary graph-isomorphism oracle nor a canonical serialization theorem.

The released `proofNetCanonicalFingerprint?` takes the lexicographic minimum
of the v0.3 strings in the complete finite canonical family. Lean proves that
the option is always populated, that a selected value belongs to the family
image, and that `ProofNetEquivalent` certificates have equal fingerprints.
This JSON-string result remains forward-only because the project does not
assume `Json.compress` injectivity. The separate `proofNetCanonicalCode?`
uses an explicitly length-framed structural token encoder whose injectivity is
proved in Lean. On structurally well-formed certificates, and therefore on
checker-accepted inputs, equality of this typed code is proved iff exactly
`ProofNetEquivalent`. These public boundary proofs use exactly
`[propext, Classical.choice, Quot.sound]`; no project-specific axiom or
unproved serializer premise is added.

`CanonicalKey.fromString` parses the distinct
`proofnet-canonical-key-0.1` envelope with token-count and aggregate-character
limits. Parsing establishes only wire shape: tokens arriving from outside are
opaque and are not trusted as proof-net evidence. The safe boundary recomputes
the bounded canonical key locally from checker-accepted certificates.
`proofNetEquivalent_of_matchesCanonicalKey` proves that two accepted
certificates matching one parsed key are equivalent. The generator still uses
factorial family materialization, so generation and matching check the
seven-link ceiling before computation and fail closed above it. The unbounded
typed `proofNetCanonicalKey?` remains a specification oracle.

`IntrinsicCanonicalKey.fromString` parses the separate
`proofnet-canonical-key-0.2` envelope. Its tokens are equally untrusted until
compared with a locally generated key. The local generator first requires
structural well-formedness, constructs the proved intrinsic representative,
and checks the token/character envelope. Lean proves that two such local
certificates matching one admissible key are exactly `ProofNetEquivalent`.
The intrinsic construction has no link-count ceiling and does not enumerate
permutations, but parsing a key alone still proves neither origin nor checker
acceptance.

## Failure containment

Even if a future graph proposer, optimized checker, or sequentializer is wrong,
the final Lean proof must still elaborate and pass the kernel. Experimental
metrics must distinguish:

- syntactically valid JSON;
- structurally well-formed certificates;
- switching-valid certificates;
- sequentialization success;
- Lean kernel success.

Collapsing these stages into a single "solved" label would hide the project's
most useful diagnostic signal.
