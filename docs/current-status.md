# Current status

> **Replacement policy:** this page contains one rolling mathematics
> checkpoint. Update it in place; do not append checkpoint history here.

This page is the replaceable status record for the rolling research branch.
It is updated in place when a new mathematics checkpoint supersedes the
previous one.
Historical checkpoints belong in [CHANGELOG.md](../CHANGELOG.md), proof design
belongs in [v0.10-design.md](v0.10-design.md), and stable release guarantees
belong in the corresponding release audit.

Status date: 2026-08-18

## Version tracks

| Track | Revision | Status | Authority |
| --- | --- | --- | --- |
| Stable library | `v0.9.0` / `9b7dc3d104af8f57ea9123aab2e61b42e05d2216` | Released | [v0.9.0 release audit](v0.9-release-audit.md) |
| Rolling research | `v0.10.0-dev`; latest proof checkpoint `5e59d120d55fa1f2125b0edc37c374dda3739642` | Active | This page and the exact commit |

Documentation-only commits may descend from the proof checkpoint without
changing its mathematical authority. The stable release and rolling branch
make different claims. A downstream consumer that needs reproducibility should
pin `v0.9.0`. The `main` branch is the integration surface for ongoing Figure-7
scheduler and completeness work.

## Stable v0.9.0 result

For the documented unit-free, cut-free MLL certificate model, v0.9.0 provides:

- occurrence-aware graph semantics, including parallel stored-edge identity;
- an executable Boolean checker proved equivalent to independent structural
  and switching-tree correctness;
- checked desequentialization from cut-free derivations;
- complete checker-free sequentialization for every accepted certificate;
- ordered-conclusion `ProofNetEquivalent` canonical identity and stable wire
  formats;
- sound eager and worklist unification fast paths whose exact wrappers retain
  the complete recursive sequentializer as fallback;
- generated API documentation, checked consumers, compatibility contracts,
  property/fuzz/differential/performance gates, and release-pinned consumption.

The exact release guarantees, receipts, and non-goals are frozen in the
[v0.9.0 release audit](v0.9-release-audit.md).

## Rolling main result

The current checkpoint is the commitment-blocker maximality layer in the
delayed Figure-7 scheduler development.

Public theorem:

```text
ProofNetIR.SequentialFigure7.CanonicalTagHistory.strictOlder_commitmentPath_or_equalCallbackFailure
```

Under all of the following supplied inputs:

- `Certificate.DeclarativelyCorrect`;
- the complete state-only `SchedulerInvariant`;
- an authentic `CanonicalTagHistory`;
- an active `NewGuard`;
- membership of the starting event in the reservation ledger; and
- strict current-representative order from that event to the active head;

Lean proves the inclusive alternative:

1. there is an exact commitment/reference path to the active head that avoids
   the active tensor conclusion; or
2. the equal-boundary child event has stored-left orientation and carries the
   exact adjacent conclusion-to-head callback-failure trace witness.

The proof filters the finite authentic ledger for mate-touch blockers between
the starting representative and active head, maps them to current
representatives, and takes a maximum. A maximal blocker's path alternative
would combine historical source-left geometry, the blocker component route,
the commitment path, and the active component route into a tensor bypass
forbidden by reference-switching acyclicity. A further representative advance
contradicts maximality.

The disjunction is inclusive. The callback-failure branch does **not** prove
that an avoiding path is absent.

## What the rolling theorem does not prove

This checkpoint does not establish any of the following:

- unconditional elimination of the stored-left equal-boundary branch;
- queue-origin geometry sufficient to eliminate that branch;
- global mate-source-region separation for every history;
- global availability of `OlderRawMarkedRegionSeparated`;
- any of the explicit New/Wait/Forward/UnifyPayload created-candidate raw
  seams;
- `NewEnabled` for every active reachable guard;
- exhaustive enabledness of the canonical dispatcher;
- dispatcher progress or later-state totality;
- pure-worklist completeness;
- removal of the complete recursive fallback;
- faithful whole-program `NEXTAXIOM`/token-age scheduling; or
- a Guerrini-style whole-program linear bound.

These are research gates, not undocumented assumptions. Their current proof
plan is maintained in [v0.10-design.md](v0.10-design.md) and
[roadmap.md](roadmap.md).

## Verification receipt

The exact rolling checkpoint is:

```text
commit  5e59d120d55fa1f2125b0edc37c374dda3739642
tree    3005e03015476a5e9d1f1277665dad4bc320d583
stage   commitment blocker finite maximality
delta   17 files, +606/-64
```

Local verification on the committed bytes:

- full `lake build`: 403/403 jobs;
- Lean source audit: zero `sorry`/`admit` findings;
- generated API reference: current;
- runnable maximality consumer: passed under `--trust=0`;
- facade, API manifest, and axiom-audit entry points: passed under `--trust=0`;
- public declaration audit: 881 declarations total;
- audit classes: 599 full-classical, 25 axiom-free, 122 `propext`-only,
  and 135 `propext` plus `Quot.sound`;
- the new public theorem depends only on
  `[propext, Classical.choice, Quot.sound]`;
- all six explicit theorem inputs are load-bearing under the minimal-hypothesis
  audit;
- independent proof and integrated-checkpoint reviews reported no actionable
  P0, P1, P2, or P3 findings.

Exact-head GitHub verification:

- workflow: `Lean CI`;
- run: [32214065414](https://github.com/fushanbobfan/proofnet-ir/actions/runs/32214065414);
- build job: [95952157976](https://github.com/fushanbobfan/proofnet-ir/actions/runs/32214065414/job/95952157976);
- exact head: `5e59d120d55fa1f2125b0edc37c374dda3739642`;
- result: 36 successful steps, zero failures, one expected release-ref-only
  skip.

## Current library-readiness position

The stable v0.9.0 surface is independently consumable for its exact model.
The rolling branch retains and continuously checks:

- one public umbrella import, `import ProofNetIR`;
- a generated declaration reference;
- source and tag-pinned downstream consumers;
- compatibility and migration contracts for public wire formats;
- checked parsing of untrusted certificate and LeanProp data;
- deterministic unit, property, fuzz, differential, reconstruction, and
  performance gates;
- exact trust-boundary and no-placeholder audits;
- preregistered experiment artifacts and publication-boundary checks.

This does not make the project a mature broad proof-net library. The supported
logic remains unit-free, cut-free MLL; there is no claim for units, Mix, cuts
or cut elimination, additives, exponentials, quantifiers, a general Lean
tactic, arbitrary graph-isomorphism canonicalization, external adoption, or
independent research validation.

## Empirical status

The committed deterministic matched experiment uses 1,000 generated tasks and
an equal 1,000-unit method budget:

| Method | Solved |
| --- | ---: |
| Focused sequent search | 760/1000 |
| Formula-skeleton proof-net generation | 1000/1000 |
| One-edit checker-guided repair | 1000/1000 |

The methods receive deliberately different structural help, consume zero model
tokens, and do not establish a general proof-net advantage.

The amended 180-task model study reports:

| Method | Solved |
| --- | ---: |
| Focused search | 85/180 |
| Net generation | 160/180 |
| Constructed distance-ordered repair | 180/180 |
| Model direct | 117/180 |
| Model repair | 2/180 |

The exact protocols, frozen artifacts, timing amendments, costs, failure modes,
and limitations live under `experiments/` and in
[experiment-protocol.md](experiment-protocol.md). These finite studies are
not ordinary Lean theorem-proving benchmarks and are not evidence of external
deployment.

## Open macro gates

The project goal remains open. The principal outstanding gates are:

1. resolve or correctly accommodate the equal-boundary stored-left callback
   branch;
2. derive the remaining queue-origin, mate-region, and raw-mark separation
   facts from authentic certified histories;
3. close the New/Wait/Forward/UnifyPayload created-candidate raw seams;
4. derive reachable active-guard enabledness and exhaustive nonterminal
   dispatcher progress;
5. prove pure-worklist completeness and remove the recursive fallback without
   weakening the accepted-certificate theorem;
6. implement and verify faithful `NEXTAXIOM`/token-age scheduling and its
   whole-program complexity;
7. continue the traceable, page/chapter-level literature matrix without
   treating file discovery or structural scans as completed reading;
8. preserve public API, migration, downstream, experiment, and release gates
   as the mathematical surface grows.

## Navigation

- Proof design: [v0.10-design.md](v0.10-design.md)
- Architecture: [architecture.md](architecture.md)
- Trust boundary: [trust-model.md](trust-model.md)
- Readiness limits: [library-readiness-audit.md](library-readiness-audit.md)
- Research roadmap: [roadmap.md](roadmap.md)
- Literature inventory: [reading-ledger.md](reading-ledger.md)
- Source coverage: [source-coverage-audit.md](source-coverage-audit.md)
- Generated API: [api-reference.md](api-reference.md)
- Stable release: [v0.9-release-audit.md](v0.9-release-audit.md)
- Historical checkpoints: [CHANGELOG.md](../CHANGELOG.md)
