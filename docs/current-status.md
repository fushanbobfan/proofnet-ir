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
| Rolling research | `v0.10.0-dev`; latest proof checkpoint `fe7786f83d2df795df2e20e40b02d4f4535615ec`; latest finite-audit evidence `1e46573141a8ad683cc539480f18c92992bda60c` | Active | This page and the exact commits |

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

The current checkpoint characterizes the four remaining branch-local
obligations for `ActiveTopMarkedNonconclusionDebt` exactly. It retains the
full-history indexed marked-tensor predecessor invariant, the ready-head
classification, and the conditional bridge from the exact active-top residual
to marking completion. In every started scheduler-invariant state, absence of
`ReadyHeadInput` is equivalent to `ActiveTopDrained`, meaning that the live
component at the last sigma boundary has no raw-unmarked frontier occurrence.
A started, declaratively correct, dispatcher-reachable state therefore still
satisfies the non-exclusive disjunction of one exact successful dispatcher
result and that explicit residual.

`ActiveTopMarkedNonconclusionDebt certificate state` is the additional state
predicate. For the component at the last sigma boundary, every frontier
occurrence whose mark lookup is concrete and which is not a certificate
conclusion must have a raw-unmarked, nonconclusion witness on that same
frontier. It is concrete state data: the definition quantifies over the exact
sigma lookup, component lookup, frontier memberships, conclusion memberships,
and mark-array lookups.

Primary public declarations:

```text
ProofNetIR.SequentialFigure7.ActiveTopMarkedNonconclusionDebt
ProofNetIR.SequentialFigure7.empty_activeTopMarkedNonconclusionDebt
ProofNetIR.SequentialFigure7.InitialReservationStep.activeTopMarkedNonconclusionDebt
ProofNetIR.SequentialFigure7.NewStep.activeTopMarkedNonconclusionDebt
ProofNetIR.SequentialFigure7.ConclStep.activeTopMarkedNonconclusionDebt
ProofNetIR.SequentialFigure7.ForwardStep.activeTopMarkedNonconclusionDebt_of_created_not_conclusion
ProofNetIR.SequentialFigure7.UnifyPayloadStep.activeTopMarkedNonconclusionDebt_of_created_not_conclusion
ProofNetIR.SequentialFigure7.SchedulerInvariant.allMarked_of_activeTopDrained_of_nonconclusionDebt
ProofNetIR.SequentialFigure7.PreparedStep.SelectedAwayRawNonconclusionWitness
ProofNetIR.SequentialFigure7.ActiveTopMarkedNonconclusionPresent
ProofNetIR.SequentialFigure7.PreparedStep.activeTopMarkedNonconclusionDebt_iff_selectedAway
ProofNetIR.SequentialFigure7.NopStep.activeTopMarkedNonconclusionDebt_iff_selectedAway
ProofNetIR.SequentialFigure7.WaitStep.activeTopMarkedNonconclusionDebt_iff_selectedAway
ProofNetIR.SequentialFigure7.ForwardStep.activeTopMarkedNonconclusionDebt_iff_tailLaw_of_created_conclusion
ProofNetIR.SequentialFigure7.UnifyPayloadStep.activeTopMarkedNonconclusionDebt_iff_tailLaw_of_created_conclusion
```

The empty theorem establishes debt vacuously because there is no active sigma
boundary. `InitialReservationStep.activeTopMarkedNonconclusionDebt` requires
only the exact initial-reservation witness and holds because the new raw mark
array has no concrete mark. `NewStep.activeTopMarkedNonconclusionDebt` requires
only a successful New step: the fresh active axiom component has two
raw-unmarked frontier endpoints. Neither theorem assumes a prior debt instance,
and New needs no additional `SchedulerInvariant` premise.

`ConclStep.activeTopMarkedNonconclusionDebt` preserves a supplied prior debt
through a successful Concl step. The Forward and UnifyPayload theorems each
require the successful rule witness, the complete `SchedulerInvariant` for the
input state, and proof that the rule's created conclusion is not a global
certificate conclusion. Under those hypotheses, the new raw ready head pays
every active marked-nonconclusion debt; these two theorems do not require a
prior debt instance.

The final theorem has four exact hypotheses: declarative correctness, the
complete scheduler invariant, `ActiveTopDrained`, and
`ActiveTopMarkedNonconclusionDebt`. Draining makes every occurrence on the
active frontier concretely marked. Debt then excludes any active-frontier
nonconclusion, and correctness plus scheduler ownership closes the connected
certificate carrier. The result is exactly `state.core.allMarked = true`.

`PreparedStep.SelectedAwayRawNonconclusionWitness` records the exact extra
witness needed when the common prefix marks its selected nonconclusion: a
distinct raw-unmarked nonconclusion remains on the same component frontier.
With prior debt fixed, debt after the prepared prefix, Nop, or Wait is
equivalent to this witness. These are necessary-and-sufficient branch
characterizations, not merely sufficient preservation lemmas.

`ActiveTopMarkedNonconclusionPresent` records that the active live frontier
actually contains a concretely marked nonconclusion. If Forward creates a
global conclusion, the prior-state complete scheduler invariant makes
post-debt equivalent to presence implying a non-global vertex in
`step.prependStep.activeReady`. For a global-created UnifyPayload step, the
corresponding exact tail is
`payload ++ previousReady ++ activeReady`. The presence antecedent is needed
because debt is vacuous when no marked nonconclusion is present.

These equivalences expose the remaining proof obligations but do not discharge
them. Bare `CanonicalTagHistory` and correctness hypotheses do not provide the
selected-away or exact-tail witnesses through the current public theory.
Consequently the debt is not yet packaged over complete canonical histories,
and a dispatcher-reachable drained state does not automatically carry it. The
checkpoint therefore does not prove the unconditional reachable-state
implication from `ActiveTopDrained` to `core.allMarked = true` or unconditional
progress.

### Finite ready-head boundary audit

A separately committed bounded replay now classifies each visited state after
successful initialization as marking-incomplete or fully marked and checks
exact typed ready-head reconstruction before invoking the dispatcher. In the
default replay, all 22,590 incomplete states had a ready head and a successful
dispatch, while all 594 dispatch-none stops were fully marked. The extended
replay classified 95,190 incomplete states and 1,254 fully marked stops in the
same way. The cross-variant replay classified 1,172,208 incomplete states and
10,608 fully marked stops.

Across all three modes, the incomplete-without-head,
incomplete-dispatch-none, cycle, and truncation counters were zero. Any future
violation produces a replayable certificate, state, event history, and rule
trace rather than only an aggregate count. These results are bounded
falsification evidence, not a proof of semantic nonterminal-to-ready-head
coverage or progress. Exact counters and scope are maintained in
[performance.md](performance.md).

Exact signatures are maintained in the generated API reference for the
[branch-prefix declarations](api-reference.md#older-marked-tensor-predecessor-branch-prefix)
and the
[full-history declarations](api-reference.md#full-history-older-marked-tensor-predecessor-invariant),
followed by the
[active-top residual](api-reference.md#active-top-ready-head-residual) and the
[active-top marked-nonconclusion debt](api-reference.md#active-top-marked-nonconclusion-debt),
and then the
[active-top debt branch residuals](api-reference.md#active-top-debt-branch-residuals).
The structural no-head classifier and the conditional drained-to-all-marked
reduction are kernel-checked. Deriving the selected-away and global-created
exact-tail laws, then packaging complete canonical-history preservation of the
debt, is the first open proof step.

## What the rolling theorem does not prove

This checkpoint does not establish any of the following:

- construction of a relevant `ExecutedHistory`, reachable state, or
  `ReadyHeadInput`;
- the selected-away witness for Nop or Wait from bare canonical history and
  correctness;
- the exact non-global tail law for global-created Forward or UnifyPayload from
  bare canonical history and correctness;
- complete canonical-history preservation of
  `ActiveTopMarkedNonconclusionDebt`;
- an unconditional reachable-state proof that `ActiveTopDrained` implies
  `core.allMarked = true`, semantic completion, or terminality without the
  debt hypothesis;
- an exclusivity theorem for the exact-dispatch / active-top-drained
  disjunction;
- a proof that every relevant semantic nonterminal state presents a ready head;
- unconditional elimination of `ReadyHeadMarkedTensorPredecessorGap` without
  the invariant and complete scheduler hypotheses;
- global preservation of the mate-region or older-raw-mark invariant families;
- the remaining global created-candidate raw seams or queue-origin laws needed
  by those separate invariant families;
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

The exact rolling proof checkpoint is:

```text
commit    fe7786f83d2df795df2e20e40b02d4f4535615ec
tree      073b742bb1aeb4dd54f9c706c71148d78a7ea504
parent    c5f19c8c57e1a02d035ca41c3a5ae9ca93047422
stage     active-top debt exact branch residuals
delta     17 paths, +936/-46
manifest  CE6601D205F8B9F8B1696E213E76BE2B7948335E450EDBF97916D2CD0EFBFD2F
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

Local verification on the committed bytes:

- full `lake build`: 460/460 jobs;
- Lean source audit: zero actual `sorry`/`admit` findings across 220 Lean
  files;
- generated API reference: current;
- the default, extended, and cross-variant progress audits passed with every
  incomplete visited state carrying an exact ready head and successful
  dispatch, every dispatch-none stop fully marked, and zero missing-head,
  incomplete-dispatch-none, cycle, or truncation findings;
- the runnable predecessor consumer: passed under `--trust=0`, invokes the nine
  branch-prefix declarations, constructs the indexed carrier, and derives
  `False` from an actual gap's `no_predecessor` field;
- the runnable Wait-preservation consumer: passed under `--trust=0`, invokes
  the tenth public declaration, applies the preserved invariant, destructures
  `SigmaImmediatePredecessorAt`, and consumes all four carrier fields;
- the runnable Forward-preservation consumer: passed under `--trust=0`, invokes
  the public bridge and Forward theorem, applies the preserved invariant, and
  consumes all four indexed predecessor fields;
- the runnable UnifyPayload-preservation consumer: passed under `--trust=0`,
  invokes the raw touch theorem, compatibility wrapper, and preservation
  theorem, then consumes all four indexed predecessor fields;
- the existing UnifyPayload touch consumer directly exercises the new
  carrier-free raw touch theorem as well as the compatibility wrapper;
- the runnable full-history consumer: passed under `--trust=0`, invokes all
  three new history declarations, projects all four indexed predecessor
  fields, and destructures the exact dispatcher result into its kind and state;
- the runnable active-top residual consumer: passed under `--trust=0`, invokes
  both directions of the no-ready-head equivalence, destructures the exact
  dispatcher witness, and consumes every residual field;
- the runnable active-top marked-nonconclusion debt consumer: passed under
  `--trust=0`, invokes all seven public theorems, checks the empty,
  initial-reservation, New, Concl, non-global-created Forward and UnifyPayload
  cases, and applies the exact drained-to-all-marked reduction;
- the runnable active-top debt branch-residual consumer: passed under
  `--trust=0`, invokes both directions of all five exact equivalences and
  consumes both new public definitions by destructuring and reconstructing
  their witnesses;
- facade, API manifest, and axiom-audit entry points: passed under `--trust=0`;
- public declaration audit: 919 declarations total;
- audit classes: 634 full-classical, 25 axiom-free, 125 `propext`-only,
  and 135 `propext` plus `Quot.sound`;
- `empty_olderMarkedTensorPredecessorInvariant` depends exactly on `[propext]`;
- the other six original branch-prefix theorems and the Wait, bridge, and
  Forward, raw UnifyPayload touch, and UnifyPayload preservation theorems
  depend exactly on `[propext, Classical.choice, Quot.sound]`;
- the three full-history declarations depend exactly on
  `[propext, Classical.choice, Quot.sound]`;
- both active-top residual theorems depend exactly on
  `[propext, Classical.choice, Quot.sound]`;
- `empty_activeTopMarkedNonconclusionDebt` depends exactly on `[propext]`;
- the other six active-top marked-nonconclusion debt theorems depend exactly on
  `[propext, Classical.choice, Quot.sound]`;
- `PreparedStep.activeTopMarkedNonconclusionDebt_iff_selectedAway` depends
  exactly on `[propext]`;
- the Nop, Wait, Forward, and UnifyPayload exact branch-residual equivalences
  depend exactly on `[propext, Classical.choice, Quot.sound]`;
- independent proof, API, and documentation reviews reported no actionable P0,
  P1, P2, or P3 findings.

Exact-head proof GitHub verification:

- workflow: `Lean CI`;
- event/ref: `push` / `main`;
- run: [32301049304](https://github.com/fushanbobfan/proofnet-ir/actions/runs/32301049304);
- build job: [96223401596](https://github.com/fushanbobfan/proofnet-ir/actions/runs/32301049304/job/96223401596);
- exact head: `fe7786f83d2df795df2e20e40b02d4f4535615ec`;
- result: 36 successful steps, zero failures, one expected release-ref-only
  skip; run duration 12m37s (`20:54:07Z`-`21:06:44Z`) and build-job duration
  12m33s (`20:54:10Z`-`21:06:43Z`).

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

The project goal remains open. The principal outstanding gates are:

1. derive the selected-away witnesses for Nop and Wait and the exact non-global
   tail laws for global-created Forward and UnifyPayload; then package
   `ActiveTopMarkedNonconclusionDebt` through complete canonical histories,
   derive the unconditional reachable-state
   `ActiveTopDrained → core.allMarked = true` corollary, and use marking
   incompleteness to exclude the residual;
2. close the separate queue-origin and remaining created-candidate laws needed
   by the global mate-region and raw-mark preservation families;
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
