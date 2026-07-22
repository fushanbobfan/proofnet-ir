# ProofNet-IR

ProofNet-IR is an experimental, verified proof-geometry intermediate
representation for AI-guided theorem proving in Lean 4.

Current release: `v0.2.0` (derivation/data/search baseline). See
[CHANGELOG.md](CHANGELOG.md) for the precise guarantees and non-goals.

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
  independent inductive walk semantics, plus completeness/iff theorems for the
  exact finite-computation contract;
- exact soundness and completeness against an independent fuel-indexed path
  semantics: `closureN fuel` iff a path of at most `fuel` steps is available
  when stored edges are in bounds;
- `check_iff_fuelDeclarativelyCorrect`, lifting both the path and switching
  correspondences to the complete certificate checker;
- explicit exchange/permutation plus recursive identity expansion proving
  `|- A, A-dual` for every unit-free MLL formula;
- a first-order arbitrary cut-free derivation-tree language with explicit
  resource positions and exchange permutations;
- general validated desequentialization of those trees, with a checked return
  type carrying `certificate.check = true`;
- a deterministic broad-family derivation generator whose first 250
  depth-two trees all produce accepted certificates;
- a derivation-first generator for the corresponding canonical identity
  certificate at arbitrary formula depth, with exact certificate-gated
  reconstruction;
- a finite formula enumerator whose depth-two one-atom corpus checks all 210
  generated identity certificates;
- labeled negative-certificate mutations, 69 positive/negative compile-time
  assertions, and an executable smoke test.
- an independent CI differential audit over 33,868 exhaustive graphs and
  1,000 generated or mutated certificates.
- versioned canonical v0.2 JSON plus a committed deterministic dataset of 250
  positive and 750 negative checker-labeled records;
- a native canonical-v0.2 JSON parser with path-aware errors and a
  checker-gated API for untrusted certificates;
- a runnable focused cut-free sequent-search baseline with eager invertible par
  steps and exhaustive tensor resource partitions.

This is a research prototype. It does not yet include general reverse
sequentialization of every accepted net, cut elimination, exponentials, additives,
quantifiers, or a Lean tactic.

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
supported sequential reconstruction
        |
        v
Lean kernel
```

The external AI, JSON input, and future graph proposer are untrusted. Use
`Certificate.checkedFromString` to parse and validate an external canonical
v0.2 certificate before exposing it to trusted code.
See [docs/trust-model.md](docs/trust-model.md) for the exact boundary.

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
python scripts/focused_search.py examples/focused-sequent-v0.2.json --require-found
```

Expected smoke-test output:

```text
ProofNetIR: all compile-time certificate checks passed
```

## Repository map

```text
ProofNetIR/Formula.lean       MLL formulas and linear negation
ProofNetIR/Certificate.lean   occurrences, links, and structural validation
ProofNetIR/Graph.lean         finite graph closure and declarative tree property
ProofNetIR/Checker.lean       switchings, executable checker, soundness/completeness
ProofNetIR/Reconstruct.lean   supported sequent derivation reconstruction
ProofNetIR/Generate.lean      recursive derivation-first identity certificates
ProofNetIR/Mutation.lean      labeled corruptions for negative fixtures
ProofNetIR/DerivationTree.lean arbitrary cut-free trees and desequentialization
ProofNetIR/Serialization.lean canonical v0.2 certificate JSON
ProofNetIR/Parser.lean        v0.2 JSON parser and checked-input boundary
ProofNetIRTests.lean          positive/negative compile-time and smoke fixtures
ProofNetIRDataset.lean        deterministic 1,000-record dataset emitter
consumer-smoke/               independent downstream Lake dependency test
consumer-release-smoke/       clean consumer pinned to public v0.2.0 tag
schemas/                      versioned external certificate contract
examples/                     valid and invalid JSON certificates
datasets/v0.2/                committed checker-labeled corpus and manifest
scripts/focused_search.py     focused cut-free comparison baseline
docs/                         architecture, literature map, roadmap, trust boundary
```

## Scientific status

No performance result is claimed yet. In particular, this repository has not
shown that proof graphs outperform tactic generation. The first meaningful
experiment will compare direct sequent-proof generation with graph generation
and checker-guided repair on controlled MLL tasks.

The broader plan is in [docs/roadmap.md](docs/roadmap.md). Source screening and
project rationale are recorded in [docs/literature-map.md](docs/literature-map.md).
The auditable source-coverage record is in
[docs/reading-ledger.md](docs/reading-ledger.md), and the first matched
evaluation is specified in
[docs/experiment-protocol.md](docs/experiment-protocol.md).
The stricter post-v0.2 coverage and reuse assessments are in
[docs/source-coverage-audit.md](docs/source-coverage-audit.md) and
[docs/library-readiness-audit.md](docs/library-readiness-audit.md). The
representation comparison that guides general sequentialization is in
[docs/formalization-comparison.md](docs/formalization-comparison.md).

## License

MIT. See [LICENSE](LICENSE).
