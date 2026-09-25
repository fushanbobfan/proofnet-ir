# Current status

> **Replacement policy:** this page contains one rolling mathematics
> checkpoint. Update it in place; do not append checkpoint history here.

This page is the replaceable status record for the rolling research branch.
It is updated in place when a new mathematics checkpoint supersedes the
previous one.
Historical checkpoints belong in [CHANGELOG.md](../CHANGELOG.md), proof design
belongs in [v0.10-design.md](v0.10-design.md), and stable release guarantees
belong in the corresponding release audit.

Status date: 2026-09-24

## Version tracks

| Track | Revision | Status | Authority |
| --- | --- | --- | --- |
| Stable library | `v0.10.0` / `f0fd97f8592938165dbffd91656d226b6102adcc` | Released | [v0.10.0 release audit](v0.10-release-audit.md) |
| Rolling research | `v0.11.0-dev`; proof `33ebfd5`; audit `1e46573`; trust gate `34cd793` | Active | This page/commits |

Documentation-only commits may descend from the proof checkpoint without
changing its mathematical authority. The stable release and rolling branch
make different claims. A downstream consumer that needs reproducibility should
pin the release. The `main` branch is the integration surface for ongoing Figure-7
scheduler and completeness work.

## Stable v0.10.0 result

For the documented unit-free, cut-free MLL certificate model, v0.10.0
provides:

- occurrence-aware graph semantics, including parallel stored-edge identity;
- an executable Boolean checker proved equivalent to independent structural
  and switching-tree correctness;
- checked desequentialization from cut-free derivations;
- complete checker-free sequentialization for every accepted certificate;
- ordered-conclusion `ProofNetEquivalent` canonical identity and stable wire
  formats;
- the sequential Figures 7–8 executable as the public decision, proved
  equal to the reference checker with no fallback, terminating within
  `formulas.size + 1` dispatcher calls, with a quadratic whole-program
  operation bound; the eager and worklist candidates stay public and sound;
- generated API documentation, checked consumers, compatibility contracts,
  property/fuzz/differential/performance gates, and release-pinned consumption.

The exact release guarantees, receipts, and non-goals are frozen in the
[v0.10.0 release audit](v0.10-release-audit.md).

## Rolling main result

The public decision is exact, fallback-free, and cost-bounded. Its cost
theorem (ledger item D6, `ProofNetIR/Figure7/CostBound.lean`) counts every
operation of a run of `unificationCheck`, phase by phase, through the
instrumented twin `sequentialDecisionWithStats` of `ProofNetIR/Figure7/Cost.lean`
(Boolean equal to the decision), and bounds the count by
`152 * (formulas.size + 1) * (formulas.size + links.length +
conclusions.length + 1)` on structurally well-formed certificates
(`decisionStats_total_le_of_structural`) and by `152 * inputSize²` on all
certificates (`decisionStats_total_le`), `inputSize` adding the symbols of the
submitted formulas. The model charges each list traversal by its length, each
array access by one, each formula by its symbols with an atom name as one
symbol, and each early-failing rule attempt in full. The bound rests on the
carrier bounds of the stack structures, the linear duplicate guard
`nodupGuard`, a waiting potential that pays each payload activation with the
`wait` that stored the occurrence, the absence of exchange nodes in live
component trees, and the duplicate-free raw canonical traversal; the verifier
compares intrinsic canonicalizations rather than their string codes, whose
unary length framing is cubic. The bound is quadratic, not linear, because
the stack is list-based with tail access, buckets are rebuilt by append, and
the consumer index is recomputed per rule attempt (D6-linear, later goal).

The decision itself is the sequential fast path alone:
`Certificate.unificationCheck` is `sequentialFastCheck` (D2,
`unificationCheck_eq_sequentialFastCheck` by `rfl`), with no eager scan,
worklist tier, or recursive reconstruction fallback, and the fast path is
complete: `sequentialFastCheck = check` (D1, `sequentialFastCheck_eq_check`
in `ProofNetIR/Figure7/Sequential.lean`). The executable initializes at the first
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
   theorems above, which close D1;
10. the public decision redefined as the sequential fast path, which closes
    D2 and realizes the Figures 7–8 replacement of the eager prototype;
11. the operation counters of the decision, the linear duplicate guards, the
    dispatcher-phase bound with its waiting potential, and the bounds of the
    remaining phases, which close D6.

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
- Guerrini-style linearity (D6-linear): the proved bound is quadratic in the
  operation model above, wall-clock time is measured by the benchmark
  (`sequential_decision_ms`) and is not a theorem, and the model's charging
  conventions are stated in `ProofNetIR/Figure7/Cost.lean`, not derived from
  the compiled code.

These are research gates, not undocumented assumptions. Their exact target
statements are in the [goal ledger](goal-ledger.md); the proof plan is in
[v0.10-design.md](v0.10-design.md).

## Verification receipt

The exact rolling proof checkpoint is:

```text
commit    33ebfd52543b443b52115f940c5e8ec736faa46e
tree      986afeddae35a23c04b4ac8a3f53432f2fdd9818
parent    cf797aa3ef85efa1ea91cf47d3659f3505df132d
stage     bound every phase of the public decision and close D6
delta     17 paths, +1936/-139
manifest  95DCAA9DC7183B403F0268E9E037AAF23BF893151F5EE80659862B0ECB408F9B
```

The manifest hashes canonical
`path<TAB>UPPER_SHA256<TAB>blob<LF>` records for the committed delta.

The checkpoint source receipts are:

```text
cost source        1CE7C175602133979AEBFE0F4510C71368D57284278A231735EBCD4C0BE40C58
cost-bound source  8BE210E4D6E9E949003A58E6776D408DD0B5B58DCDC36FE5121E82BFBB1205C1
sequential consumer BB33887BF1958C9FAB214720E31E4EEF1752897344578688B58A24590B88B3EA
generated API      E1199EA836EB48CFADF1EA8205FEA7225C13C6E7AD3F2CD47A8716741BC64023
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

- full `lake build`: 741/741 jobs;
- the 17 new public theorems report exactly `propext`, `Classical.choice`,
  and `Quot.sound`, except two arithmetic bounds that use `propext` and
  `Quot.sound` only; the module and its consumer compile under `--trust=0`,
  and the consumer printed `Sequential consumer passed: final structure,
  inference, par/tensor numbering, equivalence, completeness, public
  decision; repeated-label tensor counters: calls 6, total 1512`;
- public theorem audit: 1191 entries total: 889 standard-three, 25 axiom-free,
  132 `propext`-only, and 145 `propext`/`Quot.sound` boundaries;
- every CI executable that calls the changed verifier passed locally: the
  main tests, the reconstruction audit (1,000 cases) and stress (18 cases),
  the unification audit (1,500 cases, decision equal to the reference), and
  the benchmark (291 inputs: sequential decision 47 ms, reference check
  532 ms; the decision no longer serializes canonical codes);
- generated API reference current; convergence check passed (one new module,
  17 new public theorems, 1,371 library lines, 14 prose lines net growth);
- `git diff --check` clean on the staged delta.

Library trust gate: `34cd793` imports every library module at trust zero and
checks every safe compiled declaration. At that head it passes 14,477
declarations in 191 modules, all within `propext`, `Classical.choice`, and
`Quot.sound` (run [35899598850](https://github.com/fushanbobfan/proofnet-ir/actions/runs/35899598850);
rerun locally with its 11 rejection tests). The head before the gate,
`5be735c`, passes the same gate unchanged: no declaration had depended on
anything else.

Exact-head proof GitHub verification:

- workflow: `Lean CI`;
- event/ref: `push` / `main`;
- run: [35557157288](https://github.com/fushanbobfan/proofnet-ir/actions/runs/35557157288);
- build job: [106202906142][proof-job];
- title/attempt: `feat: bound every phase of the public decision and close D6` / 1;
- exact head: `33ebfd52543b443b52115f940c5e8ec736faa46e`;
- result: 41 successful steps, 0 failures, and 1 expected
  release-ref-only skip;
- run: `2026-09-21T03:19:51Z`-`2026-09-21T03:32:58Z` (13m07s);
- build job: `2026-09-21T03:19:54Z`-`2026-09-21T03:32:57Z`
  (13m03s).

[proof-job]: https://github.com/fushanbobfan/proofnet-ir/actions/runs/35557157288/job/106202906142

Exact-head finite-audit GitHub verification:

- workflow: `Lean CI`;
- run: [32273794767](https://github.com/fushanbobfan/proofnet-ir/actions/runs/32273794767);
- build job: [96136251609](https://github.com/fushanbobfan/proofnet-ir/actions/runs/32273794767/job/96136251609);
- exact head: `1e46573141a8ad683cc539480f18c92992bda60c`;
- result: 36 successful steps, zero failures, one expected release-ref-only
  skip; run duration 11m21s (`16:04:18Z`-`16:15:39Z`) and build-job duration
  11m17s (`16:04:21Z`-`16:15:38Z`).

## Current library-readiness position

The stable v0.10.0 surface is independently consumable for its exact model.
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

The program's six completion conditions are met at `v0.10.0`; the
[goal ledger](goal-ledger.md) records each with its evidence. The v0.11
program ([v0.11-design.md](v0.11-design.md)) answers the founding question by
measurement. Step 1 is done: on the committed corpora the median number of
plain sequent derivations per proof net is 2, 36, and 170,734 at 8, 16, and
32 atoms, and the strictly focused calculus still has more than one
derivation per net on 81.8% of tasks (`experiments/redundancy-v0.1`). Step 2
is done: under equal information and one budget, net-space search decides
every unique-label task where sequent search times out, and times out on
every one-label 32-atom task that pruned sequent search proves in
milliseconds (`experiments/matched-search-v0.1`); at 32 atoms, which family
wins is decided by label repetition. Step 3 is done: the same local model, given one
rendering and asked for either a sequent proof or a proof net, produced no
Lean-verified proof in 180 answers and seven verified nets, all on the
smallest tasks, six of them with unique labels (`experiments/representation-v0.1`). The three
preregistered steps of the program are complete. Beyond MLL, the question
was taken to Lean's scale in [proof-graphs](https://github.com/fushanbobfan/proof-graphs): Lean's first-goal
convention already absorbs rule-order redundancy, and searching over goals
gains nothing at equal budget. A linear whole-program bound (D6-linear)
stays optional.

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
