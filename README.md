# ProofNet-IR

ProofNet-IR is an experimental, verified proof-geometry intermediate
representation for AI-guided theorem proving in Lean 4.

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
- exhaustive enumeration of all par switchings;
- a finite undirected graph checker for boundedness, connectedness, and the
  `|E| + 1 = |V|` tree condition;
- a Lean theorem `check_sound` connecting executable acceptance to an
  independent inductive walk semantics, plus completeness/iff theorems for the
  exact finite-computation contract;
- a converse theorem showing each bounded inductive walk appears at some
  finite closure depth (the uniform `vertexCount` bound remains open);
- kernel-checked sequent derivations for canonical two- and three-axiom net
  families, with certificate-gated reconstruction for the first family;
- labeled negative-certificate mutations, 40 positive/negative compile-time
  assertions, and an executable smoke test.

This is a research prototype. It does not yet include a general
sequentialization theorem, cut elimination, exponentials, additives,
quantifiers, or a Lean tactic.

## Trust path

```text
untrusted certificate
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

The external AI, future JSON parser, and future graph proposer are untrusted.
See [docs/trust-model.md](docs/trust-model.md) for the exact boundary.

## Build

Prerequisites: Git and [Elan](https://github.com/leanprover/elan). The pinned
Lean version is recorded in `lean-toolchain`.

```powershell
lake build
lake exe proofnet_ir_tests
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
ProofNetIR/Mutation.lean      labeled corruptions for negative fixtures
ProofNetIRTests.lean          positive/negative compile-time and smoke fixtures
schemas/                      versioned external certificate contract
examples/                     valid and invalid JSON certificates
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

## License

MIT. See [LICENSE](LICENSE).
