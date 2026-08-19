# Current status

> **Replacement policy:** this page contains one rolling mathematics
> checkpoint. Update it in place; do not append checkpoint history here.

This page is the replaceable status record for the rolling research branch.
It is updated in place when a new mathematics checkpoint supersedes the
previous one.
Historical checkpoints belong in [CHANGELOG.md](../CHANGELOG.md), proof design
belongs in [v0.10-design.md](v0.10-design.md), and stable release guarantees
belong in the corresponding release audit.

Status date: 2026-08-19

## Version tracks

| Track | Revision | Status | Authority |
| --- | --- | --- | --- |
| Stable library | `v0.9.0` / `9b7dc3d104af8f57ea9123aab2e61b42e05d2216` | Released | [v0.9.0 release audit](v0.9-release-audit.md) |
| Rolling research | `v0.10.0-dev`; latest proof checkpoint `1040e0ef267788eb7264aa542c9f2b7cd16c6dfb` | Active | This page and the exact commit |

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

The current checkpoint closes the input-availability theorem for an already
established, history-indexed active Figure-7 `NewGuard`.

Primary public theorem:

```text
ProofNetIR.SequentialFigure7.CanonicalTagHistory.active_newEnabled
```

Under all of the following supplied inputs:

- `Certificate.DeclarativelyCorrect`;
- the complete state-only `SchedulerInvariant`;
- an authentic `CanonicalTagHistory`;
- and an already established active `NewGuard`;

Lean now derives all of the following locally for that guard:

1. every authentic reservation-ledger event is touch-separated from the
   complete source-left region of the active tensor mate;
2. that region contains no concrete raw mark and no exact marked occurrence
   owner, while every region tag is `false`;
3. there is a complete `NewSourceRegionInput`; and
4. the input-only predicate `NewEnabled` holds.

The reusable `ActiveMateEventAnchor` stores an exact conclusion-avoiding path
from the active mate to one event's stored-left axiom endpoint. Finite blocker
maximality and exact reference-tree edge identity exclude every strictly older
anchored event: the commitment-path branch forms the forbidden active-tensor
bypass, while the stored-left callback branch forms an alternate walk around
the same exact tensor edge. Any event touch inside the active mate region
constructs such an anchor.

A concrete raw mark supplies its same-age authentic event and final owned
component. The active-region path and the event's owned path therefore build
the same forbidden anchor. Exact-owner absence follows from raw-mark absence;
canonical touch provenance gives tag freshness; and the structural
run-or-blocker theorem can return only the run branch. This proof does not
assume either global `OlderEventTouchSeparated` or global
`OlderRawMarkedRegionSeparated`. It also preserves the earlier claim boundary:
the equal-boundary callback witness is contradicted only when the strict-old
active-mate anchor is present, not in isolation.

## What the rolling theorem does not prove

This checkpoint does not establish any of the following:

- construction or existence of a canonical history or active `NewGuard`;
- a proof that every relevant nonterminal state presents that guard;
- selection of an exhaustive priority branch or a stored executor equation;
- global preservation of the mate-region or older-raw-mark invariant families;
- any of the explicit New/Wait/Forward/UnifyPayload created-candidate raw seams
  or the queue-origin laws that would discharge them;
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
commit  1040e0ef267788eb7264aa542c9f2b7cd16c6dfb
tree    23409edf2bf63f8513b625bfe0befcca2edb3823
stage   active-region touch separation and input-only New enabledness
delta   19 files, +2022/-68
```

Local verification on the committed bytes:

- full `lake build`: 413/413 jobs;
- Lean source audit: zero `sorry`/`admit` findings across 201 Lean files;
- generated API reference: current;
- both runnable active-region consumers: passed under `--trust=0` and invoke
  every new public API;
- facade, API manifest, and axiom-audit entry points: passed under `--trust=0`;
- public declaration audit: 888 declarations total;
- audit classes: 606 full-classical, 25 axiom-free, 122 `propext`-only,
  and 135 `propext` plus `Quot.sound`;
- all seven new public theorems depend only on
  `[propext, Classical.choice, Quot.sound]`;
- every detected explicit theorem input is load-bearing under the
  minimal-hypothesis audit;
- independent proof and integrated-checkpoint reviews reported no actionable
  P0, P1, P2, or P3 findings.

Exact-head GitHub verification:

- workflow: `Lean CI`;
- run: [32230579133](https://github.com/fushanbobfan/proofnet-ir/actions/runs/32230579133);
- build job: [95999296136](https://github.com/fushanbobfan/proofnet-ir/actions/runs/32230579133/job/95999296136);
- exact head: `1040e0ef267788eb7264aa542c9f2b7cd16c6dfb`;
- result: 36 successful steps, zero failures, one expected release-ref-only
  skip; run duration 10m47s and build-job duration 10m42s.

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

1. classify every relevant nonterminal certified state into the applicable
   priority branch, including existence of the active guard when New is next;
2. close the queue-origin and New/Wait/Forward/UnifyPayload created-candidate
   laws needed by the global mate-region and raw-mark preservation families;
3. derive exhaustive nonterminal dispatcher progress and later-state totality;
4. prove pure-worklist completeness and remove the recursive fallback without
   weakening the accepted-certificate theorem;
5. implement and verify faithful `NEXTAXIOM`/token-age scheduling and its
   whole-program complexity;
6. continue the traceable, page/chapter-level literature matrix without
   treating file discovery or structural scans as completed reading;
7. preserve public API, migration, downstream, experiment, and release gates
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
