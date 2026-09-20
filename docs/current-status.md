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
| Rolling research | `v0.10.0-dev`; proof `31b6f8e`; audit `1e46573` | Active | This page/commits |

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

The sequential fast path is complete: `Certificate.sequentialFastCheck =
Certificate.check` (ledger item D1, `sequentialFastCheck_eq_check` in
`ProofNetIR/Figure7/Sequential.lean`). The executable initializes at the first
conclusion, runs the canonical dispatcher `runDispatcher` for the
formula-carrier budget, exchanges the final component's frontier into the
conclusion order, and accepts only after `verifyDerivation?`, so soundness is
by construction (`sequentialFastCheck_sound`). Completeness
(`sequentialFastCheck_complete`) composes: initialization totality at every
in-bounds start (`StructurallyWellFormed.initializeReservation?_isSome`); the
run's endpoint (`runDispatcher_spec`: reachable, fully marked, unable to
dispatch, by Figure-7 progress D3 `CanonicalTagHistory.dispatch_or_allMarked`
from the order-free `RegionClosure` invariant and switching connectedness,
and termination D4); final structure (`finalComponents_eq_singleton`,
`finalFrontier_perm`, `sequentialFinalTree?_eq_some`: one live component owns
the carrier and exposes the conclusions, extracted with a duplicate-free
exchange); inference (`sequentialFinalTree?_infer_eq`); and equivalence of the
desequentialized final derivation to the input (`occurrenceBuild_exists`,
the fresh-index correspondence `OccurrenceBuildMatch` proved for every
constructor of an occurrence derivation, and `occurrenceBuild_equivalent`,
which turns a covering linear derivation into a bounded vertex renaming and
a link permutation). Separately, the ledger's D5 was refuted as stated by the
reachable empty scheduler of one axiom (`priorityEnabled_not_allReachable`)
and closed in corrected form (`figure7Enabledness_started_and_sequentialize`:
reachable `new` guards suffice, and a reachable nonterminal state has a
priority branch exactly when initialized).

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
9. the final structure, inference, numbering-correspondence, and equivalence
   theorems above, which close D1.

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
- removal of the recursive fallback from the public decision
  `unificationCheck` (D2); the sequential fast path is complete but is not
  yet the public decision;
- later-state `NEXTAXIOM` start selection and completion of the Figures 7–8
  executable (D5); or
- a Guerrini-style whole-program linear bound (D6).

These are research gates, not undocumented assumptions. Their exact target
statements are in the [goal ledger](goal-ledger.md); the proof plan is in
[v0.10-design.md](v0.10-design.md).

## Verification receipt

The exact rolling proof checkpoint is:

```text
commit    31b6f8ea96fc2f80197278bbbabbe62debbf10fa
tree      0b92ccc21ffb3868ae859ca6bec98897c4215f6b
parent    2cffa2d2b6ca52cd71a377010e4c5610e0c24e69
stage     prove sequential fast-path completeness and close D1
delta     9 paths, +898/-38
manifest  5859DB0EFDBFFF2A93184EAC5A7D86DFB6F4EE70DB43FB05EAE9587F8166DB40
```

The manifest hashes canonical
`path<TAB>UPPER_SHA256<TAB>blob<LF>` records for the committed delta.

The checkpoint source receipts are:

```text
sequential source  A4BF89EF782ED3A9CDD0A5CA429F46CD60A7720F5A3F9EB01B8D910B47A09FA1
sequential consumer 9BEC834A342432F9CE34717AB184677DE27C2972277E22F68A4E511DB3144317
generated API      66C7375049694E59DBE81ABC5BA7A7CD1D8A60F4514B64079ABB4F72901E1DC5
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
- the six new public theorems report exactly `propext`, `Classical.choice`,
  and `Quot.sound`; the module and its consumer compile under `--trust=0`,
  and the consumer printed `Sequential consumer passed: final structure,
  inference, par/tensor numbering, equivalence, completeness`;
- public theorem audit: 1156 entries total: 858 standard-three, 25 axiom-free,
  132 `propext`-only, and 141 `propext`/`Quot.sound` boundaries;
- generated API reference current; convergence check passed (no new module,
  six new public theorems, 684 library lines, 17 prose lines);
- `git diff --check` clean on the staged delta.

Exact-head proof GitHub verification:

- workflow: `Lean CI`;
- event/ref: `push` / `main`;
- run: [35541146265](https://github.com/fushanbobfan/proofnet-ir/actions/runs/35541146265);
- build job: [106158921187][proof-job];
- title/attempt: `feat: prove sequential fast-path completeness and close D1` / 1;
- exact head: `31b6f8ea96fc2f80197278bbbabbe62debbf10fa`;
- result: 41 successful steps, 0 failures, and 1 expected
  release-ref-only skip;
- run: `2026-09-20T22:16:08Z`-`2026-09-20T22:32:01Z` (15m53s);
- build job: `2026-09-20T22:16:11Z`-`2026-09-20T22:32:01Z`
  (15m50s).

[proof-job]: https://github.com/fushanbobfan/proofnet-ir/actions/runs/35541146265/job/106158921187

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

1. make the complete sequential fast path the public decision without the
   recursive fallback (D2; D1 closed on 2026-09-20 after both were
   retargeted from the flat worklist);
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
