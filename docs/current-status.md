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
| Rolling research | `v0.10.0-dev`; proof `43b0dd0`; audit `1e46573` | Active | This page/commits |

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

The sequential fast path exists and is sound; its completeness (ledger item
D1) rests on the numbering correspondence of the desequentializer.
`ProofNetIR/Figure7/Sequential.lean` defines `runDispatcher` (a bounded loop
of the canonical dispatcher threading the scheduler invariant),
`Certificate.sequentialReconstruct?` and `Certificate.sequentialFastCheck`
(initialize at the first conclusion, run the formula-carrier budget, exchange
the final component's frontier into the conclusion order, accept only after
`verifyDerivation?`), and proves `sequentialFastCheck_sound`.
`runDispatcher_spec` shows that from a started reachable state of a correct
certificate the run ends reachable, fully marked, and unable to dispatch, by
Figure-7 progress D3 (`CanonicalTagHistory.dispatch_or_allMarked`, from the
order-free `RegionClosure` invariant and switching connectedness) and
termination D4. `StructurallyWellFormed.initializeReservation?_isSome` shows
initialization succeeds at every in-bounds start. At a fully marked reachable
state, `finalComponents_eq_singleton` and `finalFrontier_perm` give one live
component owning every occurrence with frontier equal to the conclusions up
to order, `sequentialFinalTree?_eq_some` extracts it with a duplicate-free
exchange, and `sequentialFinalTree?_infer_eq` proves that the extracted
derivation infers the input sequent and desequentializes to an accepted
certificate. What remains for D1 is that this output is proof-net equivalent
to the input: the par and tensor cases of the fresh-index correspondence
`OccurrenceBuildMatch` (its axiom and exchange cases are proved) and the
bounded vertex renaming they yield over the full carrier. Separately, the
ledger's D5 was refuted as stated by the reachable empty scheduler of one
axiom (`priorityEnabled_not_allReachable`) and closed in corrected form
(`figure7Enabledness_started_and_sequentialize`: reachable `new` guards
suffice, and a reachable nonterminal state has a priority branch exactly when
initialized).

The route to this checkpoint, in dependency order, is:

1. the canonical six-rule dispatcher `dispatch?` with its typed
   `DispatchStep` witnesses and the occurrence-exact `SchedulerInvariant`,
   preserved by every successful rule;
2. `ReachableByImplementedDispatcher.dispatch_or_activeTopDrained`: a
   reachable state either dispatches or its active top is drained, which
   reduces Figure-7 progress to the drained case;
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
6. C12, the `nop`/`wait` half of item 3 as a state predicate, certified not
   state-only inductive;
7. `RegionClosure`: initial, preserved, and sufficient by connectedness
   both for C12 (nonempty bucket) and for the drained case of item 2 (empty
   bucket), which closes D3 without items 3 to 5;
8. `runDispatcher_spec` and `initializeReservation?_isSome`, the executable
   half of D1;
9. the final structure and inference theorems above, leaving only the
   numbering correspondence and equivalence of the desequentialized output.

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

- the created-head obligations of the `forward` and `unifyPayload` branches
  of the history-tail law, hence the law itself; they are no longer needed for
  progress and are stated exactly in `ProofNetIR/Figure7/Closure.lean`;
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
- exhaustive enabledness beyond `dispatch_or_allMarked`: a reachable state
  that is not fully marked dispatches, but which rule fires is not classified;
- completeness of `sequentialFastCheck` (D1): the par and tensor cases of
  the fresh-index correspondence and proof-net equivalence of the
  desequentialized final derivation; or removal of the recursive fallback
  (D2);
- later-state `NEXTAXIOM` start selection and completion of the Figures 7–8
  executable (D5); or
- a Guerrini-style whole-program linear bound (D6).

These are research gates, not undocumented assumptions. Their exact target
statements are in the [goal ledger](goal-ledger.md); the proof plan is in
[v0.10-design.md](v0.10-design.md).

## Verification receipt

The exact rolling proof checkpoint is:

```text
commit    43b0dd0f6e6b8f7e5f755b0f2e6cbff8d36c5753
tree      f2a730c4ace9045e703740d37d2a4ecc95b0cc78
parent    9134f0093c0fb5a2511e6fb378d27e684bd86921
stage     prove sequential final structure and inference
delta     10 paths, +714/-9
manifest  BB5F195DB35681C4DE97FDCCB62E086DDBD43A9BE33A70D5C8F32AD07346BAC1
```

The manifest hashes canonical
`path<TAB>UPPER_SHA256<TAB>blob<LF>` records for the committed delta.

The checkpoint source receipts are:

```text
sequential source  4C4180CB48A01FBA4C76021864E48054B4A302780130F6259F19BAD9470C43E5
sequential consumer 80BB24F434B2E53C1F05EFBB0CF0C81872C065997870062BA496DDA325684C26
generated API      F84B2BC1687CB62659ECFA19A55845E010933C71C711A74FCA80D2411A0D7DAE
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

- full `lake build`: 737/737 jobs;
- the seven new public theorems report exactly `propext`, `Classical.choice`,
  and `Quot.sound`; the module and its consumer compile under `--trust=0`,
  and the consumer printed `Sequential consumer passed: final structure,
  inference, axiom/exchange numbering, repeated-label tensor`;
- public theorem audit: 1150 entries total: 852 standard-three, 25 axiom-free,
  132 `propext`-only, and 141 `propext`/`Quot.sound` boundaries;
- generated API reference current; convergence check passed (no new module,
  seven new public theorems, 453 library lines, 12 prose lines);
- `git diff --check` clean on the staged delta.

Exact-head proof GitHub verification:

- workflow: `Lean CI`;
- event/ref: `push` / `main`;
- run: [35537842224](https://github.com/fushanbobfan/proofnet-ir/actions/runs/35537842224);
- build job: [106149962486][proof-job];
- title/attempt: `feat: prove sequential final structure and inference` / 1;
- exact head: `43b0dd0f6e6b8f7e5f755b0f2e6cbff8d36c5753`;
- result: 41 successful steps, 0 failures, and 1 expected
  release-ref-only skip;
- run: `2026-09-20T21:10:00Z`-`2026-09-20T21:26:33Z` (16m33s);
- build job: `2026-09-20T21:10:03Z`-`2026-09-20T21:26:33Z`
  (16m30s).

[proof-job]: https://github.com/fushanbobfan/proofnet-ir/actions/runs/35537842224/job/106149962486

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

1. prove completeness of the sequential fast path (`sequentialFastCheck =
   check`): the par and tensor cases of the fresh-index correspondence and
   proof-net equivalence of the desequentialized final derivation (D1); then
   make it the public decision without the recursive fallback (D2); both
   retargeted from the flat worklist on 2026-09-20;
2. replace the prototype's eager starts and flat requeues with the sequential
   executable once D1 and D2 close (the remaining part of D5);
3. prove a whole-program cost theorem over every implemented operation (D6);
4. continue the traceable, page/chapter-level literature matrix without
   treating file discovery or structural scans as completed reading;
5. preserve public API, migration, downstream, experiment, and release gates
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
