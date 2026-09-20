# Current status

> **Replacement policy:** this page contains one rolling mathematics
> checkpoint. Update it in place; do not append checkpoint history here.

This page is the replaceable status record for the rolling research branch.
It is updated in place when a new mathematics checkpoint supersedes the
previous one.
Historical checkpoints belong in [CHANGELOG.md](../CHANGELOG.md), proof design
belongs in [v0.10-design.md](v0.10-design.md), and stable release guarantees
belong in the corresponding release audit.

Status date: 2026-09-20

## Version tracks

| Track | Revision | Status | Authority |
| --- | --- | --- | --- |
| Stable library | `v0.9.0` / `9b7dc3d104af8f57ea9123aab2e61b42e05d2216` | Released | [v0.9.0 release audit](v0.9-release-audit.md) |
| Rolling research | `v0.10.0-dev`; proof `ea64f0b`; audit `1e46573` | Active | This page/commits |

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

The C12 checkpoint reduces the `nop` and `wait` branches of the history-tail
law to one state predicate. `ParHeadGuardTailNonconclusion` (C12) says that
when the active ready bucket's head is a par premise whose mate is unmarked or
marked below the active raw age, the rest of the bucket holds a non-conclusion.
Every correct initialization satisfies C12
(`InitialReservationStep.parHeadGuardTail`), and C12 on the pre-state
discharges the exact remaining-top obligation of a `nop` or `wait` step
(`NopStep.tailNonconclusion_of_parHeadGuard`,
`WaitStep.tailNonconclusion_of_parHeadGuard`). C12 is not a state-only
inductive invariant: `parHeadGuardTail_not_inductive` exhibits a correct
certificate and a `SchedulerInvariant` state satisfying C12 whose canonical
`nop` successor violates it, and proves that pre-state canonically
unreachable. The finite probe reports C12 at every one of 1,217,664 default
and 1,071,360 wait-focus reachable states.

The route to this checkpoint, in dependency order, is:

1. the canonical six-rule dispatcher `dispatch?` with its typed
   `DispatchStep` witnesses and the occurrence-exact `SchedulerInvariant`,
   preserved by every successful rule;
2. `ReachableByImplementedDispatcher.dispatch_or_activeTopDrained`: a
   reachable state either dispatches or its active top is drained, which
   reduces Figure-7 progress (ledger item D3) to draining;
3. `CanonicalTagHistory.ActiveTopDebtTailLaw`, the exact remaining
   obligation along a canonical history: every `nop` or `wait` leaves a
   non-conclusion in its remaining bucket, `new` resets the law, and a
   `forward` or `unifyPayload` either creates a non-conclusion head or,
   when marked non-conclusion debt is present afterwards, keeps a
   non-conclusion in the merged bucket;
   `activeTopMarkedNonconclusionDebt_of_tailLaw` turns the law into the
   debt that drains the active top;
4. the conditional classifications of the `nop`/`wait` re-entry target under
   ready-tail failure (the commitment-interval, raw-return, and waiting-mate
   families of August 2026), none of which discharges the obligation;
5. the termination bound `dispatch_stops` (ledger item D4, closed);
6. C12 above, which is the `nop`/`wait` half of item 3 as a state predicate.

Exact statements are in the [goal ledger](goal-ledger.md); declarations are
in the generated [API reference](api-reference.md).

### Finite ready-head boundary audit

A separately committed bounded replay classifies each visited state after
successful initialization as marking-incomplete or fully marked and checks
exact typed ready-head reconstruction before invoking the dispatcher. In the
default replay, all 22,590 incomplete states had a ready head and a successful
dispatch, while all 594 dispatch-none stops were fully marked; the extended
replay classified 95,190 incomplete states and 1,254 fully marked stops, and
the cross-variant replay 1,172,208 and 10,608. Across all three modes the
incomplete-without-head, incomplete-dispatch-none, cycle, and truncation
counters were zero. Any future violation produces a replayable certificate,
state, event history, and rule trace. These results are bounded falsification
evidence, not a proof of progress; exact counters are maintained in
[performance.md](performance.md).

## What the rolling theorem does not prove

This checkpoint does not establish any of the following:

- C12 at every canonically reachable state, the history-tail law, the
  created-head obligations of the `forward` and `unifyPayload` branches, or
  unconditional progress; the certified obstruction shows that any proof must
  carry reachability information beyond `SchedulerInvariant` and C12;
- progress, later-state totality, or terminal-state completeness from the
  termination bound, which counts successful calls and says nothing about the
  state in which a run stops;
- construction or existence of a relevant `ExecutedHistory`, reachable state,
  `CanonicalTagHistory`, `ReadyHeadInput`, or successful `nop` or `wait`
  transition, or that any reachable canonical history contains a `wait`;
- elimination or payer conversion of the surviving re-entry targets classified
  by the August 2026 families: their receipts are conditional on exact
  ready-tail failure and supplied reference-switching connectedness, and none
  yields the non-conclusion the tail law requires;
- an unconditional reachable-state proof that `ActiveTopDrained` implies
  `core.allMarked = true`, semantic completion, or terminality;
- exhaustive enabledness of the canonical dispatcher, or that every relevant
  semantic nonterminal state presents a ready head;
- pure-worklist completeness (D1) or removal of the recursive fallback (D2);
- later-state `NEXTAXIOM` start selection and completion of the Figures 7–8
  executable (D5); or
- a Guerrini-style whole-program linear bound (D6).

These are research gates, not undocumented assumptions. Their exact target
statements are in the [goal ledger](goal-ledger.md); the proof plan is in
[v0.10-design.md](v0.10-design.md).

## Verification receipt

The exact rolling proof checkpoint is:

```text
commit    ea64f0b03b93ab556958162741c5bb591c618f5a
tree      2d73c39aef2d332604cbdf683695221ef1caff20
parent    b769d1d0ddc4b7624e612585fcce6ebee20684dd
stage     certify the C12 preservation obstruction
delta     12 paths, +603/-2
manifest  EA32864D0381C05F4E54493F592561AF1A792F7A54446C18581399EFFB026830
```

The manifest hashes canonical
`path<TAB>UPPER_SHA256<TAB>blob<LF>` records for the committed delta.

The checkpoint source receipts are:

```text
tail-law source    571FC55B2B76AB15641D883FAAF4B9186DA0D017A328E26A54AAA6B3F1FC223D
tail-law consumer  2E6E5B8B5F80E072DC5DE5A186DE6E4A835AC28BA7CCAAA526330FC5B9A36BCF
generated API      27B2A5716ED6908E8C654C9B9CEED0D63B051D6956A330BA3D385F26898CBC91
```

The separately committed finite-audit evidence is:

```text
commit    1e46573141a8ad683cc539480f18c92992bda60c
tree      e953ef9fe8ef185cea4b5ac5399c6396ca25643b
parent    e7983468736a8a156c2a51985a68828efe26dfae
stage     finite ready-head and dispatch-none replay classification
delta     3 files, +369/-48
manifest  4BBAB7FC99D03D2612459A0FD9291990313A05A184F2572A581BC93C6E49DFDD
```

Local verification of the committed checkpoint:

- full `lake build`: 722/722 jobs;
- the four public declarations of the checkpoint report exactly `propext`,
  `Classical.choice`, and `Quot.sound`; the module and its consumer compile
  under `--trust=0`, and the consumer printed
  `C12 consumer passed: initialization, nop/wait implications, preservation
  obstruction`;
- public theorem audit: 1119 entries total: 821 standard-three, 25 axiom-free,
  132 `propext`-only, and 141 `propext`/`Quot.sound` boundaries;
- generated API reference current; convergence check passed (one new module,
  four new public theorems, 306 library lines, 7 prose lines);
- `--invariant-probe`: C12 holds at all 1,217,664 default and 1,071,360
  wait-focus reachable states; the C13 suffix strengthening fails at 173,226
  and 474,336 of them;
- `git diff --check` clean on the staged delta.

Exact-head proof GitHub verification:

- workflow: `Lean CI`;
- event/ref: `push` / `main`;
- run: [35487810755](https://github.com/fushanbobfan/proofnet-ir/actions/runs/35487810755);
- build job: [106017290541][proof-job];
- title/attempt: `docs: record the C12 obstruction in the goal ledger` / 1
  (the run covers head `4d1c6bd`, whose only change over `ea64f0b` is the
  ledger row);
- exact head: `4d1c6bd3e37df1ae3b2718d3b26724301e694873`;
- result: 40 successful steps, zero failures, and one expected
  release-ref-only skip;
- run: `2026-09-20T03:55:09Z`-`2026-09-20T04:11:04Z` (15m55s);
- build job: `2026-09-20T03:55:12Z`-`2026-09-20T04:11:03Z`
  (15m51s).

[proof-job]: https://github.com/fushanbobfan/proofnet-ir/actions/runs/35487810755/job/106017290541

Exact-head finite-audit GitHub verification:

- workflow: `Lean CI`;
- run: [32273794767](https://github.com/fushanbobfan/proofnet-ir/actions/runs/32273794767);
- build job: [96136251609](https://github.com/fushanbobfan/proofnet-ir/actions/runs/32273794767/job/96136251609);
- exact head: `1e46573141a8ad683cc539480f18c92992bda60c`;
- result: 36 successful steps, zero failures, one expected release-ref-only
  skip; run duration 11m21s (`16:04:18Z`-`16:15:39Z`) and build-job duration
  11m17s (`16:04:21Z`-`16:15:38Z`).

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

The project goal remains open. The principal outstanding gates, with exact
target statements in the [goal ledger](goal-ledger.md), are:

1. prove C12 at every canonically reachable state through a history-carrying
   invariant of the active bucket (the finite probe shows the bucket is a run
   of connective conclusions followed by paired atoms), close the `nop` and
   `wait` branches of `ActiveTopDebtTailLaw`, then the `forward` and
   `unifyPayload` created-head branches; the law combined with
   `dispatch_or_activeTopDrained` gives Figure-7 progress (D3);
2. derive exhaustive nonterminal dispatcher enabledness and later-state
   totality, and the later-state `NEXTAXIOM` start selection needed to
   complete the Figures 7–8 executable (D5);
3. prove pure-worklist completeness and remove the recursive fallback without
   weakening the accepted-certificate theorem (D1, D2);
4. prove a whole-program cost theorem over every implemented operation (D6);
5. continue the traceable, page/chapter-level literature matrix without
   treating file discovery or structural scans as completed reading;
6. preserve public API, migration, downstream, experiment, and release gates
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
