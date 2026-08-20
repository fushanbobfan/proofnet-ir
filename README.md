# ProofNet-IR

ProofNet-IR is an experimental Lean 4 library for verified proof geometry.
It represents unit-free, cut-free multiplicative linear logic (MLL) as typed
formula occurrences and links, checks proof-net correctness, reconstructs
cut-free derivations, and exposes stable machine-readable boundaries for
research tooling.

The library is designed around one rule: an external model, search procedure,
or serialized certificate may propose structure, but only a Lean-kernel-checked
result crosses the trusted boundary.

## Choose a track

| Track | Use it for | Read first |
| --- | --- | --- |
| Stable `v0.9.0` | Reproducible downstream use of the released MLL model | [Release audit](docs/v0.9-release-audit.md) |
| Rolling `main` / `v0.10.0-dev` | Ongoing Figure-7 scheduler and completeness research | [Current status](docs/current-status.md) |

Pin the release when stability matters. Track `main` only when you need the
latest research surface and are prepared for documented development changes.

<!-- ROLLING_MAIN_SUMMARY_START -->
### Rolling-main summary

The rolling branch now turns history-preserved continuation credit into a
finite, strictly formula-complexity-increasing continuation exit. Each marked
nonconclusion reaches an unmarked raw mate, scheduled future-conclusion work,
or a concretely marked global conclusion.

A separate endpoint-bound locality condition retains only the open raw-mate and
future-conclusion exits and binds their endpoint to the active component. This
condition remains sufficient: with structural well-formedness and queued
vertices unmarked it yields active-top marked-nonconclusion debt; with
declarative correctness, the full scheduler invariant, and a drained active top
it yields all formula occurrences marked.

Every successful typed Wait step from a scheduler-invariant input refutes
unrestricted locality at its output, so the law is not preserved across such
a transition. This does not establish a reachable Wait, nor refute conditional
results, direct debt, or a compatible drained, temporal, or cross-component law.

This checkpoint proves no arbitrary history or locality existence,
unconditional progress, completion, terminality, or totality. The next gate is
direct history-compatible debt, a suitable weakened locality law, or another
sufficient completion route.
[Current status](docs/current-status.md) owns exact revision, verification receipt, and gates.
<!-- ROLLING_MAIN_SUMMARY_END -->

## Scope

The stable mathematical scope is:

- propositional, unit-free, cut-free MLL;
- explicit formula occurrences rather than label-only vertices;
- typed axiom, tensor, and par links;
- ordered conclusions;
- Danos--Regnier switching correctness;
- occurrence-aware multigraph semantics;
- checked desequentialization and general sequentialization;
- canonical identity under the library's explicit equivalence relations.

The project does **not** currently claim support for:

- units or Mix;
- cuts or cut elimination;
- additives;
- exponentials or boxes;
- quantifiers in the proof-net model;
- arbitrary unlabeled graph isomorphism;
- a general Lean tactic for mathlib goals;
- pure-worklist completeness;
- a whole-program Guerrini-linear implementation;
- production reliability or external adoption.

The experimental LeanProp wire layer has a separate, narrower syntax and trust
contract. Its quantifier-shaped template nodes are not a claim of quantified
proof-net semantics.

## Why proof geometry?

A sequent derivation fixes an order between inference steps even when some of
those steps are independent. A proof net records more of the dependency
geometry directly. That makes it useful as an intermediate representation for:

- checking an untrusted graph certificate;
- comparing proofs modulo selected representation choices;
- reconstructing a kernel derivation;
- testing local repair strategies;
- separating search from verification;
- studying executable sequentialization algorithms.

ProofNet-IR treats those advantages as hypotheses to formalize and measure,
not as automatic performance claims. The reference checker is intentionally
simple and exact. Faster paths are admitted only when their outputs are
independently verified, and empirical comparisons retain their task-specific
limitations.

## Quick start

Prerequisites are Git and [Elan](https://github.com/leanprover/elan). The
repository pins its Lean version in `lean-toolchain`.

```powershell
git clone https://github.com/fushanbobfan/proofnet-ir.git
Set-Location proofnet-ir
lake build
lake exe proofnet_ir_tests
```

The expected smoke output is:

```text
ProofNetIR: all certificate and v0.3 fixture checks passed
```

Development commands, targeted consumers, trust checks, experiment gates, and
the release workflow live in [CONTRIBUTING.md](CONTRIBUTING.md).

### Use it as a Lake dependency

For the stable release:

```toml
[[require]]
name = "proofnet-ir"
git = "https://github.com/fushanbobfan/proofnet-ir"
rev = "v0.9.0"
```

For a neighboring development checkout:

```toml
[[require]]
name = "proofnet-ir"
path = "../proofnet-ir"
```

Import the public facade:

```lean
import ProofNetIR

open ProofNetIR
```

The repository continuously compiles both a source-pinned consumer and a
release-pinned consumer. See [the tutorial](docs/tutorial.md) for a complete
downstream walkthrough.

## A minimal certificate

Formula-array indices are occurrence identities. The following certificate is
one axiom link with its endpoints as ordered conclusions:

```lean
def p : Formula := .atom "p" true
def pDual : Formula := .atom "p" false

def axiomCertificate : Certificate where
  formulas := #[p, pDual]
  links := [.axiom 0 1]
  conclusions := [0, 1]

example : axiomCertificate.check = true := by
  native_decide

example : axiomCertificate.DeclarativelyCorrect :=
  axiomCertificate.check_iff_declarativelyCorrect.mp (by native_decide)
```

`check` is executable. The iff theorem connects it to independent structural
and switching-tree semantics.

## Parse untrusted bytes at the checked boundary

Use `checkedFromString` when a certificate comes from a model, file, network,
or other untrusted source:

```lean
def parsed :=
  Certificate.checkedFromString axiomCertificate.canonicalString

example : parsed.isOk = true := by
  native_decide
```

`fromString` validates syntax and canonical wire shape. `checkedFromString`
also runs the reference checker and returns an accepted certificate only on
success. Parse errors retain a JSON path and diagnostic message.

Never treat successful parsing as proof-net correctness unless the checked API
was used.

## Sequentialize an accepted certificate

The public runtime API reconstructs a cut-free derivation:

```lean
def reconstructed := axiomCertificate.sequentialize

example : reconstructed.isOk = true := by
  native_decide

example :
    ∃ result : ExecutableSequentializationResult axiomCertificate,
      axiomCertificate.sequentialize = .ok result :=
  axiomCertificate.sequentialize_complete (by native_decide)
```

The second result is a theorem about the executable search, not just a test:
every certificate accepted by `check` has a successful runtime
sequentialization.

A successful result contains:

- a cut-free derivation tree;
- its inferred ordered sequent;
- checked desequentialization back to an accepted certificate;
- a kernel `Derivation`;
- a proof that output and input satisfy `ProofNetEquivalent`.

## Start from a derivation

The reverse direction is independently executable:

```lean
def tree : CutFreeDerivation := .axiom "p" true

example : tree.infer? = some [p, pDual] := by
  native_decide

example : tree.desequentializeChecked?.isSome = true := by
  native_decide

example : tree.elaborate?.isSome = true := by
  native_decide
```

`desequentializeChecked?` releases a certificate only after checker acceptance.
`elaborate?` connects successful inference to a kernel-typed derivation.

## Stable v0.9.0 guarantees

Within the documented certificate model, the stable release establishes four
principal boundaries.

### 1. Exact graph semantics

Stored edge occurrences remain distinct. In particular, parallel occurrences
can form an exact length-two cycle rather than being collapsed by value.

The graph layer includes:

- boundedness and connectedness;
- occurrence-aware walks, cycles, and acyclicity;
- exact transport under bounded bijective vertex reindexing;
- the forest/tree characterization;
- a sound and complete executable cycle oracle.

### 2. Checker semantics

For structurally well-formed certificates, the compact mathematical criterion
is:

```text
CuspAcyclic ↔ every occurrence-order switching is Acyclic

check = true ↔
  StructurallyWellFormed ∧
  CuspAcyclic ∧
  ReferenceSwitchingConnected
```

The switching-free `compactCheck` is proved equal to `check`. Its colored-cycle
phase remains an exhaustive specification path, not an optimized contraction
algorithm.

### 3. General sequentialization

The supplied-derivation verifier checks formula inference,
desequentialization, and exact proof-net equivalence. Automatic recursive
reconstruction is proved complete for every reference-accepted certificate.

The executable `sequentialize` API performs finite search and rechecks its
output. Its completeness theorem covers all accepted certificates in the
supported model.

### 4. Qualified fast paths

The eager and event-driven worklist unification candidates are independently
verified. Every successful fast-path result is sound.

The exact public wrappers are proved equal to the reference checker because
they retain complete recursive reconstruction after a fast-path miss. The pure
fast path is not yet proved complete, and the fallback prevents a
whole-program linear claim.

For exact release wording and receipts, use the
[v0.9.0 release audit](docs/v0.9-release-audit.md).

## Canonical identity and wire formats

ProofNet-IR uses explicit equivalence relations rather than the phrase
"canonical graph" without a contract.

The principal distinctions are:

- `canonicalString` preserves submitted formula-array numbering;
- `equivalenceCanonicalString` is invariant under the narrower
  order-preserving `ReindexEquivalent` relation;
- `ProofNetEquivalent` permits the documented bounded vertex renaming and
  link-list permutation while preserving ordered conclusions and connective
  premise order;
- `intrinsicCanonicalKey` provides the non-factorial v0.8 key for that exact
  relation;
- external key parsing is not provenance; compare it against a locally
  generated, structurally validated key.

All public formats are versioned and fail closed. Compatibility guarantees,
ceilings, migration rules, and parser tests are documented in
[compatibility.md](docs/compatibility.md).

## Architecture at a glance

```text
untrusted derivation or certificate bytes
                  |
                  v
       versioned parser and validation
                  |
                  v
    structural + switching correctness
                  |
                  v
 checked reconstruction / desequentialization
                  |
                  v
       kernel-typed ordered derivation
                  |
                  v
              Lean kernel
```

The implementation is layered:

1. formulas, occurrences, links, and certificates;
2. finite graph and switching semantics;
3. Boolean checkers and exact proposition-level correspondence;
4. derivation inference, desequentialization, and reconstruction;
5. canonical identity and versioned serialization;
6. unification and worklist fast paths;
7. the rolling Figure-7 scheduler, histories, and progress invariants;
8. generated API, consumers, audits, experiments, and release gates.

The detailed module graph and design rationale live in
[architecture.md](docs/architecture.md). Active proof design and rejected
routes live in [v0.10-design.md](docs/v0.10-design.md).

## Trust model

The trusted base is Lean's kernel plus the explicitly audited standard logical
dependencies of the public theorems. External JSON, models, search heuristics,
finite experiments, and generated candidate proofs are untrusted inputs.

The project checks:

- public theorem axiom dependencies;
- absence of proof placeholders;
- generated API drift;
- source- and tag-pinned downstream compilation;
- parser failure behavior;
- certificate reconstruction and independent output verification;
- deterministic experiment artifacts and publication redaction.

The exact boundary, including the separate LeanProp environment semantics, is
in [trust-model.md](docs/trust-model.md).

## Error handling

Checked parsers return structured paths and messages. Unification and
reconstruction APIs expose stable error categories for malformed input,
incomplete schedules, deadlocks, resource boundaries, and independent output
verification.

A bounded failure is not a logical rejection. Use the complete checked path
when a theorem about every accepted certificate is required, and use bounded
or fast APIs only with their documented inconclusive cases.

For exact declarations, consult the generated
[API reference](docs/api-reference.md).

## Engineering readiness

The stable release is an independently consumable research library for its
exact MLL model. Its engineering surface includes:

- one public umbrella import;
- clean source- and release-pinned consumers;
- versioned canonical formats and migration tests;
- checked error diagnostics;
- property, parser-fuzz, differential, reconstruction, and performance gates;
- generated API documentation;
- exact trust and placeholder audits;
- reproducible experiment artifacts.

This is not the same as broad ecosystem maturity. Optimized algorithms,
long-term compatibility across an expanded logic, external users, publication,
and independent research validation are not claimed. See the
[library-readiness audit](docs/library-readiness-audit.md).

## Scientific evidence

The deterministic matched experiment compares focused sequent search,
formula-skeleton proof-net generation, and one-edit checker-guided repair on
1,000 generated tasks under an equal 1,000-unit method budget. The two
proof-net methods solve all tasks; focused search solves 760.

That result is deliberately qualified. The proof-net methods receive strong
structural information, repair begins one edit from a valid net, atom labels
are usually unique, and no learned model or ordinary Lean goal is involved.
It does not establish a general proof-net advantage.

A separate preregistered 180-task model study, preserved through explicit
runtime and publication amendments, reports method-specific successes and
failure modes without converting them into a broad model claim.

Use the frozen reports rather than restating results from memory:

- [matched experiment report](experiments/matched-v0.1/README.md)
- [model study report](experiments/model-v0.2/report.md)
- [experiment protocol](docs/experiment-protocol.md)
- [performance boundary](docs/performance.md)

## Literature and traceability

The project maintains a file-level inventory and distinguishes:

- file discovery;
- ordered text extraction;
- rendered-page inspection;
- page or chapter relevance;
- duplication;
- claims actually used by the formalization.

A structural scan is never counted as having read a source. The maintained
entry points are:

- [reading ledger](docs/reading-ledger.md)
- [literature map](docs/literature-map.md)
- [source-coverage audit](docs/source-coverage-audit.md)
- Page-level source audits:
  [Pfenning](docs/source-pages/pfenning-linear-logic.md),
  [Manin](docs/source-pages/manin-mathematical-logic.md),
  [Marcolli et al.](docs/source-pages/marcolli-syntax-semantics.md),
  [Geometry of Neuroscience](docs/source-pages/geometry-of-neuroscience.md),
  and [Park](docs/source-pages/park-four-punctured-sphere.md)
- [Guerrini unification audit](docs/guerrini-unification-audit.md)
- [splitting-theorem audit](docs/splitting-theorem-audit.md)
- [formalization comparison](docs/formalization-comparison.md)

The literature establishes correspondence and exposes assumptions. It does not
replace Lean proofs, counterexample search, independent differential tests, or
downstream execution.

## Documentation map

### Start here

- [Tutorial](docs/tutorial.md): dependency setup and executable examples
- [Current status](docs/current-status.md): one replaceable rolling checkpoint
- [API reference](docs/api-reference.md): generated public declarations
- [Contributing](CONTRIBUTING.md): build, tests, audits, and change workflow

### Mathematics and architecture

- [Architecture](docs/architecture.md)
- [v0.10 proof design](docs/v0.10-design.md)
- [Trust model](docs/trust-model.md)
- [Roadmap](docs/roadmap.md)
- [Formalization comparison](docs/formalization-comparison.md)
- [Splitting-theorem audit](docs/splitting-theorem-audit.md)
- [Guerrini unification audit](docs/guerrini-unification-audit.md)

### Engineering and compatibility

- [Library-readiness audit](docs/library-readiness-audit.md)
- [Compatibility and migrations](docs/compatibility.md)
- [Performance](docs/performance.md)
- [Generated API](docs/api-reference.md)
- [External consumer tutorial](docs/tutorial.md)
- [README relocation ledger](docs/readme-relocation-ledger.md)

### Literature and experiments

- [Reading ledger](docs/reading-ledger.md)
- [Literature map](docs/literature-map.md)
- [Source-coverage audit](docs/source-coverage-audit.md)
- [Experiment protocol](docs/experiment-protocol.md)
- [Matched experiment](experiments/matched-v0.1/README.md)
- [Model experiment](experiments/model-v0.2/report.md)

### Releases and history

- [Changelog](CHANGELOG.md)
- [v0.9.0 release audit](docs/v0.9-release-audit.md)
- [v0.9 design](docs/v0.9-design.md)
- [v0.8 release audit](docs/v0.8-release-audit.md)
- [v0.7 release audit](docs/v0.7-release-audit.md)
- [v0.6 release audit](docs/v0.6-release-audit.md)

## Repository map

```text
ProofNetIR/                 Lean library modules
ProofNetIR.lean             public umbrella import
ProofNetIR*Tests.lean       runnable consumer-style tests
consumer-smoke/                 current-source downstream consumer
consumer-release-smoke/         legacy v0.5.0 compatibility consumer
consumer-v09-candidate-smoke/   stable v0.9.0 tag consumer
docs/                       design, status, audits, API, and literature
examples/                   checked inputs and search examples
experiments/                frozen protocols, artifacts, and reports
scripts/                    deterministic audits and experiment runners
```

The conceptual graph belongs in [architecture.md](docs/architecture.md); the
authoritative build target registry is `lakefile.toml`.

## Contributing

Contributions are welcome when they preserve the exact claim boundary. In
particular:

- state conditional hypotheses rather than implying global availability;
- preserve minimal counterexamples to false invariants;
- add real runnable consumers for public APIs;
- keep generated API and trust manifests synchronized;
- separate proof changes from broad documentation restructuring;
- keep rolling details out of this README.

Read [CONTRIBUTING.md](CONTRIBUTING.md) before changing public Lean code,
formats, experiments, or release claims.

## Project status and provenance

ProofNet-IR is a public, substantially agent-assisted research-engineering
project directed, reviewed, tested, released, and maintained by Jiayi (Bob)
Fan. That provenance does not weaken the kernel-checked results, but it matters
for authorship and research-process claims. The project does not claim fully
manual implementation, independent external validation, or external adoption.

The persistent objective is larger than any intermediate version: a
mathematically complete, reusable, empirically honest Lean library with
traceable literature coverage, stable interfaces, independent downstream use,
and release evidence. Intermediate checkpoints remain intermediate.

## License

MIT. See [LICENSE](LICENSE).
