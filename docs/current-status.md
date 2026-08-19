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
| Rolling research | `v0.10.0-dev`; latest proof checkpoint `88b13b5db6177c438d8047c038da1c526306997d`; latest finite-audit evidence `1e46573141a8ad683cc539480f18c92992bda60c` | Active | This page and the exact commits |

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

The current checkpoint builds on the full-history indexed marked-tensor
predecessor invariant and isolates the remaining structural ready-head shape.
In every started scheduler-invariant state, absence of `ReadyHeadInput` is
equivalent to `ActiveTopDrained`: the live component at the last sigma boundary
has no raw-unmarked frontier occurrence. A started, declaratively correct,
dispatcher-reachable state therefore satisfies the non-exclusive disjunction
of one exact successful dispatcher result and that explicit residual.

Primary public declarations:

```text
ProofNetIR.SequentialFigure7.SigmaImmediatePredecessorAt
ProofNetIR.SequentialFigure7.OlderMarkedTensorPredecessorInvariant
ProofNetIR.SequentialFigure7.OlderMarkedTensorPredecessorInvariant.readyHead_predecessor_of_boundary_lt
ProofNetIR.SequentialFigure7.empty_olderMarkedTensorPredecessorInvariant
ProofNetIR.SequentialFigure7.InitialReservationStep.olderMarkedTensorPredecessorInvariant
ProofNetIR.SequentialFigure7.PreparedStep.olderMarkedTensorPredecessorInvariant
ProofNetIR.SequentialFigure7.ConclStep.olderMarkedTensorPredecessorInvariant
ProofNetIR.SequentialFigure7.NopStep.olderMarkedTensorPredecessorInvariant
ProofNetIR.SequentialFigure7.CanonicalTagHistory.new_olderMarkedTensorPredecessorInvariant
ProofNetIR.SequentialFigure7.CanonicalTagHistory.wait_olderMarkedTensorPredecessorInvariant
ProofNetIR.SequentialFigure7.CanonicalTagHistory.markedMate_sigmaImmediatePredecessor_of_childAnchor
ProofNetIR.SequentialFigure7.CanonicalTagHistory.forward_olderMarkedTensorPredecessorInvariant
ProofNetIR.SequentialFigure7.UnifyPayloadStep.createdConclusionTouchSeparated
ProofNetIR.SequentialFigure7.CanonicalTagHistory.unifyPayload_olderMarkedTensorPredecessorInvariant
ProofNetIR.SequentialFigure7.CanonicalTagHistory.olderMarkedTensorPredecessorInvariant
ProofNetIR.SequentialFigure7.ExecutedHistory.olderMarkedTensorPredecessorInvariant
ProofNetIR.SequentialFigure7.ReachableByImplementedDispatcher.readyHead_dispatch
ProofNetIR.SequentialFigure7.ActiveTopDrained
ProofNetIR.SequentialFigure7.SchedulerInvariant.no_readyHead_iff_activeTopDrained
ProofNetIR.SequentialFigure7.ReachableByImplementedDispatcher.dispatch_or_activeTopDrained
```

`OlderMarkedTensorPredecessorInvariant` quantifies over every `FutureWorkAt`,
including every member of every retained ready bucket and every initialized
waiting payload. When a marked tensor mate's current representative is strictly
below the work's current representative, `SigmaImmediatePredecessorAt` records
adjacent sigma positions ending at the work boundary together with the exact
mate-boundary lookup.

The empty state satisfies the predicate vacuously, and every successful initial
reservation establishes it because the raw-mark array remains empty. Prepared,
`concl`, and `nop` preserve a supplied prior invariant under the input
`SchedulerInvariant`. Canonical `new` preservation additionally requires
`Certificate.DeclarativelyCorrect` and an authentic `CanonicalTagHistory`; old
work transports across the fresh append, while a created endpoint's already
marked tensor mate is forced to the prior active boundary immediately below the
fresh boundary.

Canonical `wait` preservation uses the same correctness, scheduler, history,
typed dispatch, and `WaitStep` witnesses. Retained work transports through the
prepared middle state. For the inserted par conclusion, private Wait-specific
geometry internal to the module constructs the destination anchor, closes the
strict commitment interval by finite maximality, and proves that any strictly
older marked tensor mate occupies the immediate predecessor boundary. No
`FutureNewCandidateAt.mate_unmarked` premise is used.

The source-visible child-anchor bridge packages the common maximality argument:
given strict older-event separation and an exact child-event anchor, it returns
the marked mate's indexed immediate predecessor. It does not establish either
premise or any rule's applicability. Canonical `forward` preservation supplies
those premises privately for the inserted par conclusion and transports
retained work through the prepared prefix. It requires declarative correctness,
the complete scheduler invariant, canonical history, typed dispatch and
`ForwardStep` witnesses, and a supplied prior predecessor invariant.

Canonical `unifyPayload` preservation handles all three provenance cases.
Retained work transports across retirement of the active sigma boundary; the
moved case would force a surviving boundary to be strictly below itself; and
the created conclusion uses the carrier-free
`UnifyPayloadStep.createdConclusionTouchSeparated`, final component provenance,
and the child-anchor bridge to recover the indexed predecessor. The theorem
requires declarative correctness, the complete scheduler invariant, canonical
history, typed dispatch and `UnifyPayloadStep` witnesses, and a supplied prior
predecessor invariant. It does not prove that the branch is applicable.

`CanonicalTagHistory.olderMarkedTensorPredecessorInvariant` now packages the
empty, initial-reservation, and all six successful later dispatcher branches
into one exact-history theorem. The `ExecutedHistory` wrapper obtains the same
invariant from the canonical tag history carried by every executed history.
Finally, `ReachableByImplementedDispatcher.readyHead_dispatch` combines that
invariant with the ready-head dichotomy: an enabled priority branch yields an
exact `dispatch?` result, while the marked-tensor gap contradicts the indexed
predecessor. The theorem retains `ReadyHeadInput` as an explicit argument; it
does not construct a ready head or assert unconditional progress.

`ActiveTopDrained` stores the last sigma boundary, the live component at that
boundary, and a proof that every occurrence on its frontier is not raw-unmarked.
For a started state, stack well-shapedness aligns the final sigma and ready
buckets, while `ReadyBucketFrontierExact` identifies the last ready bucket with
exactly the raw-unmarked active frontier. Splitting that bucket proves
`SchedulerInvariant.no_readyHead_iff_activeTopDrained` in both directions.

The reachable wrapper derives the complete scheduler invariant from the
supplied history. If a `ReadyHeadInput` exists, the full-history predecessor
theorem gives an exact `dispatch?` result; otherwise the equivalence gives the
drained witness. The exported theorem states only this disjunction. It does not
claim exclusivity or identify `ActiveTopDrained` with `core.allMarked = true`,
semantic completion, terminality, or progress.

For a supplied `ReadyHeadInput`, the projection combines the new invariant with
the complete `SchedulerInvariant`. The fields of
`ReadyHeadMarkedTensorPredecessorGap` provide the tensor consumer, mate mark,
exact `sigmaBoundary?` lookup, and strict active-boundary inequality. The
projection therefore constructs `SigmaPredecessorInput`, contradicting the
gap's own `no_predecessor` field. This is a consumer-level consequence of the
public declarations; no unconditional gap-elimination premise is hidden in the
state invariant.

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
[active-top residual](api-reference.md#active-top-ready-head-residual).
The exact structural no-head classifier is now kernel-checked. Proving from
authentic dispatcher history that `ActiveTopDrained` implies
`core.allMarked = true` is the first open proof step.

## What the rolling theorem does not prove

This checkpoint does not establish any of the following:

- construction of a relevant `ExecutedHistory`, reachable state, or
  `ReadyHeadInput`;
- a proof that `ActiveTopDrained` implies `core.allMarked = true`, semantic
  completion, or terminality;
- an exclusivity theorem for the exact-dispatch / active-top-drained
  disjunction;
- a proof that every relevant semantic nonterminal state presents a ready head;
- unconditional elimination of `ReadyHeadMarkedTensorPredecessorGap` without
  the invariant and complete scheduler hypotheses;
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

The exact rolling proof checkpoint is:

```text
commit  88b13b5db6177c438d8047c038da1c526306997d
tree    49a391febcb1a6f5023019e9a6e96aca542c7c5b
stage   active-top ready-head structural residual
delta   17 files, +546/-121
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

- full `lake build`: 450/450 jobs;
- Lean source audit: zero `sorry`/`admit` findings across 216 Lean files;
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
- facade, API manifest, and axiom-audit entry points: passed under `--trust=0`;
- public declaration audit: 907 declarations total;
- audit classes: 624 full-classical, 25 axiom-free, 123 `propext`-only,
  and 135 `propext` plus `Quot.sound`;
- `empty_olderMarkedTensorPredecessorInvariant` depends exactly on `[propext]`;
- the other six original branch-prefix theorems and the Wait, bridge, and
  Forward, raw UnifyPayload touch, and UnifyPayload preservation theorems
  depend exactly on `[propext, Classical.choice, Quot.sound]`;
- the three full-history declarations depend exactly on
  `[propext, Classical.choice, Quot.sound]`;
- both active-top residual theorems depend exactly on
  `[propext, Classical.choice, Quot.sound]`;
- independent proof and integrated-checkpoint reviews reported no actionable
  P0, P1, P2, or P3 findings.

Exact-head proof GitHub verification:

- workflow: `Lean CI`;
- run: [32278608858](https://github.com/fushanbobfan/proofnet-ir/actions/runs/32278608858);
- build job: [96151771289](https://github.com/fushanbobfan/proofnet-ir/actions/runs/32278608858/job/96151771289);
- exact head: `88b13b5db6177c438d8047c038da1c526306997d`;
- result: 36 successful steps, zero failures, one expected release-ref-only
  skip; run duration 12m33s (`16:54:41Z`-`17:07:14Z`) and build-job duration
  12m29s (`16:54:44Z`-`17:07:13Z`).

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

1. prove from authentic canonical dispatcher history that
   `ActiveTopDrained → core.allMarked = true`, then use marking incompleteness
   to exclude the residual;
2. close the separate queue-origin and New/Wait/Forward/UnifyPayload
   created-candidate laws needed by the global mate-region and raw-mark
   preservation families;
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
