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
| Rolling research | `v0.10.0-dev`; proof `8ee8053`; audit `1e46573` | Active | This page/commits |

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

The region-closure checkpoint derives C12 from an order-free state predicate
and switching connectedness. `RegionClosure` places every marked vertex in the
class of the sigma boundary below its raw mark and requires the marked part of
each region (a class plus its ready bucket) to be closed under the link
structure except at pars whose other premise lies outside, with no tensor
premise of the active class waiting for its `new`.
`RegionClosure.guardedParHeadTail` proves that closure, `SchedulerInvariant`,
and `DeclarativelyCorrect` give `ParHeadGuardTailNonconclusion` (C12): cutting
every boundary par of the active region yields a switching whose boundary edge
(`boundary_edge_of_correct`) must start at a raw non-conclusion of the bucket.
`RegionClosure.ofInitialReservation` proves closure after every correct
initialization. The finite probe reports the executable form of the predicate
at all 1,217,664 default and 1,071,360 wait-focus reachable states, preserved
by every rule on 15,405,918 closure-satisfying snapshot edges, and implying C12
at each of them. Its preservation by the six rules is unproved.

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
6. C12, the `nop`/`wait` half of item 3 as a state predicate, proved after
   every correct initialization and certified not state-only inductive;
7. `RegionClosure` above, from which C12 follows by connectedness.

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

- preservation of `RegionClosure` by any dispatcher rule, hence C12 at every
  canonically reachable state, the history-tail law, the created-head
  obligations of the `forward` and `unifyPayload` branches, or unconditional
  progress; the probe's zero failures are finite evidence only;
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
commit    8ee80533f8e8a0f3283b1d5fe8c83a28a052a8f7
tree      8a5e30688ecc70c5b5fa76f132064542797e9880
parent    4d337aaba62a7c0bcf051a62ff637023a172b555
stage     derive C12 from region closure and switching connectedness
delta     11 paths, +988/-1
manifest  96BA3817F8E699914964F46461EAF36CCDC0A3B4D2A797F89DB6B840DCA1003E
```

The manifest hashes canonical
`path<TAB>UPPER_SHA256<TAB>blob<LF>` records for the committed delta.

The checkpoint source receipts are:

```text
closure source     36E14DDF990C1561AFD50049A42BFC0F3008675249EE87F0B035340907E2ADD1
closure consumer   D0FE2C317572A9C589475726CF0B55F93E754C9EE2F54A6ADCBA450ECC49131A
generated API      8CCB27E18C50B50ACE3142BB80E02710975D2FD0F4BE53B252DB8412C157B329
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

- full `lake build`: 727/727 jobs;
- the three public theorems of the checkpoint report exactly `propext`,
  `Classical.choice`, and `Quot.sound`; the module and its consumer compile
  under `--trust=0`, and the consumer printed
  `Region-closure consumer passed: initialization, C12 from closure, switching
  boundary`;
- public theorem audit: 1122 entries total: 824 standard-three, 25 axiom-free,
  132 `propext`-only, and 141 `propext`/`Quot.sound` boundaries;
- generated API reference current; convergence check passed (one new module,
  three new public theorems, 746 library lines, 12 prose lines);
- `--inductiveness-probe`: CLOSURE preserved by all six rules with zero
  failures on both sets and `CLOSURE-implies-C12 c12-fails=0` at 6,613,062
  default and 8,792,856 wait-focus closure states (12m29s locally);
- `git diff --check` clean on the staged delta.

Exact-head proof GitHub verification:

- workflow: `Lean CI`;
- event/ref: `push` / `main`;
- run: [35505402791](https://github.com/fushanbobfan/proofnet-ir/actions/runs/35505402791);
- build job: [106064234866][proof-job];
- title/attempt: `feat: derive C12 from region closure and switching connectedness` / 1;
- exact head: `8ee80533f8e8a0f3283b1d5fe8c83a28a052a8f7`;
- result: 41 successful steps, 0 failures, and 1 expected
  release-ref-only skip;
- run: `2026-09-20T10:33:21Z`-`2026-09-20T10:46:15Z` (12m54s);
- build job: `2026-09-20T10:33:24Z`-`2026-09-20T10:46:14Z`
  (12m50s).

[proof-job]: https://github.com/fushanbobfan/proofnet-ir/actions/runs/35505402791/job/106064234866

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
