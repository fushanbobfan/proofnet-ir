# Contributing to ProofNet-IR

ProofNet-IR is a Lean research library with a deliberately narrow trust
boundary. Contributions are expected to preserve mathematical claim scope,
public API discipline, runnable consumption, and exact auditability.

This file is the maintained home for development commands and contributor
workflow. The [README](README.md) is an entry point, not a rolling build log.

## Prerequisites

- Git
- [Elan](https://github.com/leanprover/elan)
- Python 3 for dataset, parser, experiment, and audit scripts
- PowerShell on Windows for the repository's local CI-equivalent workflow
- [ripgrep](https://github.com/BurntSushi/ripgrep) for fast registry discovery
  (optional; a PowerShell fallback is shown below)

The exact Lean toolchain is pinned in `lean-toolchain`. Do not silently update
it as part of an unrelated proof change.

Clone and build:

```powershell
git clone https://github.com/fushanbobfan/proofnet-ir.git
Set-Location proofnet-ir
lake build
```

The project uses `warningAsError`. A warning is a failed gate.

## Fast feedback

For one edited module, prefer the narrowest useful loop:

```powershell
lake build ProofNetIR.YourModule
lake env lean --trust=0 ProofNetIR/YourModule.lean
lake env lean --trust=0 --run ProofNetIRYourModuleTests.lean
```

Use the Lean language server while developing. The command-line checks above
are the final authority when a newly created import leaves an editor document
with a stale `Imports are out of date; Restart File` cache message.

For the base library smoke test:

```powershell
lake exe proofnet_ir_tests
```

For every default target and dependency:

```powershell
lake build
```

`lakefile.toml` is the authoritative target registry. Do not maintain another
hand-copied exhaustive target list in prose. To inspect executable names and
roots:

```powershell
rg -n '^\[\[lean_exe\]\]|^name =|^root =' lakefile.toml
```

Without ripgrep, use the built-in PowerShell command:

```powershell
Select-String -Path lakefile.toml -Pattern '^\[\[lean_exe\]\]|^name =|^root ='
```

The runtime order used by GitHub is authoritative in
`.github/workflows/ci.yml`.

## Core validation commands

Run these when their surface is affected:

```powershell
lake exe proofnet_ir_tests
lake exe proofnet_ir_api_docs --check
python scripts/audit_axioms.py
python scripts/generate_dataset.py --check
python scripts/audit_v03_canonical.py
python scripts/fuzz_malformed_parser.py
lake exe proofnet_ir_benchmark
lake exe proofnet_ir_reconstruction_audit
lake exe proofnet_ir_reconstruction_stress
```

The current Figure-7 regression and finite-audit entry points include:

```powershell
lake exe proofnet_ir_figure7_primitives_tests
lake exe proofnet_ir_new_progress_audit
lake exe proofnet_ir_new_progress_audit --extended
lake exe proofnet_ir_new_progress_audit --cross-representative-search
```

The precise module-specific consumers are default Lake targets. A new public
module should add and run its own consumer rather than relying on a broad
facade build.

## Experiment and publication gates

The committed deterministic and model-assisted studies are reproducible
artifacts, not informal benchmarks. Use their frozen checks:

```powershell
python scripts/focused_search.py examples/focused-sequent-v0.2.json --require-found
python scripts/run_matched_experiment.py --check-committed
python scripts/validate_model_publication_redaction.py
python scripts/test_model_publication_redaction.py
python scripts/run_model_experiment.py --check-preregistered
python scripts/run_model_experiment_amended.py --check-amendment
python scripts/run_model_experiment_amended.py --check-committed
```

Do not regenerate or reinterpret a preregistered artifact as part of an
unrelated theorem change. If an amendment is necessary, preserve the original
runner, requests, hashes, responses, and reason for the amendment.

## Trust and placeholder audits

Public theorem additions must be checked against the intended axiom boundary.
The normal MLL boundary permits only:

```text
propext
Classical.choice
Quot.sound
```

Some declarations are intentionally audited against narrower subsets. Update
both `ProofNetIRAxiomAudit.lean` and `scripts/audit_axioms.py` when a new public
theorem belongs in the audit.

The repository must remain free of actual `sorry` and `admit`. Comments that
describe those words are not proof placeholders, so use the repository's Lean
source-aware analyzer rather than an unqualified text count.

For a public theorem, also check:

- Lean language-server diagnostics;
- `#print axioms` or the inline axiom helper;
- minimal explicit hypotheses;
- `--trust=0` compilation of the defining module;
- `--trust=0 --run` for its consumer;
- import direction and absence of a reverse dependency;
- source width, whitespace, and `git diff --check`.

## Windows application-control fallback

On Windows systems that explicitly block a generated audit executable with
application-control error 4551, use:

```powershell
python scripts/audit_v010_windows.py
```

This opt-in wrapper runs the same two Lean audit sources through
`lake env lean --run`. The byte-frozen `scripts/audit_v010.py` remains the
preregistration authority. Every non-4551 failure still fails closed.

## Adding a public Lean module

Use a small, reviewable checkpoint. A typical public module change needs:

1. the core module under `ProofNetIR/`;
2. one runnable consumer that imports the narrow module and actually invokes
   every new public declaration;
3. an umbrella import in `ProofNetIR.lean` at the correct dependency layer;
4. a default target and `lean_exe` entry in `lakefile.toml`;
5. a matching runtime command in `.github/workflows/ci.yml`;
6. public names in `ProofNetIRAPIDocs.lean`;
7. public theorem entries in `ProofNetIRAxiomAudit.lean` and
   `scripts/audit_axioms.py`;
8. regenerated `docs/api-reference.md`;
9. architecture, trust, readiness, design, roadmap, and changelog updates at
   the scope actually changed;
10. a replace-in-place update to `docs/current-status.md` if this checkpoint
    becomes the rolling authority.

Keep helper lemmas private unless a second real consumer justifies a public
surface. A consumer that only contains `#check` is insufficient: include an
actual theorem call, project or destructure the result, and execute a smoke
`main` where appropriate.

## Proof and API discipline

- State exact hypotheses and keep them load-bearing.
- Do not turn a conditional preservation theorem into a global availability
  claim.
- Do not describe an inclusive disjunction as exclusive.
- A callback-failure witness does not prove that an avoiding path is absent.
- Distinguish immutable raw age, current union-find representative, sigma
  position, ledger order, and scheduler time.
- Distinguish executable finite evidence from a kernel theorem.
- Do not promote a runtime fixture, `native_decide` test, or bounded audit to a
  universal mathematical claim.
- Preserve occurrence identity when graph values can repeat.
- Avoid widening imports to the umbrella facade inside library modules.
- Keep generated API documentation generated; never hand-edit it.

If a proposed invariant is false, preserve a minimal certified counterexample,
state exactly what it refutes, and replace the invariant with the strongest
honest theorem rather than weakening the final research objective.

## Documentation ownership

Each document has one job:

| Document | Responsibility |
| --- | --- |
| `README.md` | Entry point, quick use, stable/current distinction, navigation |
| `docs/current-status.md` | One replaceable rolling checkpoint, receipts, open gates |
| `CHANGELOG.md` | Historical checkpoint sequence |
| `docs/v0.10-design.md` | Active proof design and rejected routes |
| `docs/architecture.md` | Module and data-flow architecture |
| `docs/trust-model.md` | Trust boundary and axiom model |
| `docs/library-readiness-audit.md` | Maturity and reuse limitations |
| `docs/api-reference.md` | Generated public declarations |
| `docs/compatibility.md` | Wire/API compatibility and migrations |
| `docs/roadmap.md` | Research and release plan |
| `docs/reading-ledger.md` | Source inventory and reading state |
| `docs/source-coverage-audit.md` | Claim-to-source coverage |
| `CONTRIBUTING.md` | Developer workflow and commands |
| `docs/readme-relocation-ledger.md` | Audited ownership map for the 2026 README reorganization |

Ordinary proof checkpoints must not append another theorem narrative, command
list, CI receipt, or historical state to the README. Its rolling current-state
summary should remain approximately 5–20 lines. Put details in the owner above.

When restructuring documentation, preserve information by recording where each
old section moved. Do not use Git history as the only copy of still-relevant
material.

## Updating current status

`docs/current-status.md` is replaced in place:

- keep exactly one rolling `main` revision and receipt;
- keep stable release information separate;
- remove superseded current language instead of appending another checkpoint;
- move the superseded checkpoint to `CHANGELOG.md`;
- update open gates from the actual theorem boundary;
- link to detailed design rather than copying the proof narrative;
- never describe a provisional worktree as committed or CI-verified.

## Repository layout

The main layers are:

```text
ProofNetIR/                 Lean library modules
ProofNetIR.lean             public umbrella import
ProofNetIR*Tests.lean       runnable downstream-style consumers
ProofNetIRAPIDocs.lean      generated API manifest
ProofNetIRAxiomAudit.lean   Lean trust manifest
consumer-smoke/             current-source dependency consumer
consumer-release-smoke/     legacy v0.5.0 compatibility consumer
consumer-v09-candidate-smoke/ stable v0.9.0 tag consumer
docs/                       design, audits, API, literature, and status
examples/                   checked certificate and search examples
experiments/                frozen protocols, artifacts, and reports
scripts/                    deterministic audits and experiment runners
lakefile.toml               authoritative build and executable registry
```

For the conceptual module graph, use
[docs/architecture.md](docs/architecture.md). For exact public declarations,
use the generated [API reference](docs/api-reference.md).

## Compatibility

Do not change a canonical wire format or public identity relation implicitly.
For any incompatible representation change:

- define the new schema/version explicitly;
- keep the old parser or provide a bounded migration path when feasible;
- add round-trip, malformed-input, and migration tests;
- update `docs/compatibility.md`;
- update source- and tag-pinned consumers;
- document which equivalence relation is preserved;
- never relabel arbitrary graph isomorphism as the existing ordered-conclusion
  `ProofNetEquivalent` contract.

## Pull requests

Keep mathematics, generated artifacts, experiments, and information-architecture
refactors in separable commits or pull requests. A normal proof checkpoint
should not carry a broad README rewrite, and a documentation reorganization
should not change Lean semantics.

A pull request should report:

- exact mathematical or documentation outcome;
- explicit non-claims and remaining gates;
- focused and full validation performed;
- public API additions/removals;
- compatibility impact;
- generated files refreshed;
- exact commit tested by CI.

## Release flow

Release claims are stronger than rolling-main claims. Before a tag:

1. freeze the exact commit and versioned schemas;
2. run the complete local matrix;
3. pass exact-head GitHub CI;
4. test a clean source-pinned downstream consumer;
5. test a clean tag-pinned downstream consumer;
6. verify generated API and trust manifests;
7. freeze experiment and performance receipts used by public wording;
8. publish a release audit that states guarantees and non-goals;
9. verify the annotated tag resolves to the audited commit;
10. rerun CI with the explicit release reference.

Do not use an intermediate version number as a substitute for the persistent
mathematical, engineering, empirical, and literature goals.
