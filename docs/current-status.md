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
| Rolling research | `v0.10.0-dev`; latest proof checkpoint `016dab9813192f0a2119eed4cf4ed73be4c1f164`; latest finite-audit evidence `1e46573141a8ad683cc539480f18c92992bda60c` | Active | This page and the exact commits |

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

The current checkpoint establishes a full supplied-history invariant for
branch-local continuation credit. Every concretely raw-marked nonconclusion in
the final state of an exact `CanonicalTagHistory` has one of three concrete
receipts: its opposite connective premise is still raw-unmarked, work for its
connective conclusion remains scheduled, or that conclusion is already
raw-marked. The history theorem assumes neither declarative correctness nor a
separate complete scheduler invariant; it inducts over the structural and
branch evidence already carried by the supplied canonical history.

`ContinuationCredit certificate state vertex` is the three-constructor receipt
carrier. `MarkedNonconclusionContinuation certificate state` requires such a
receipt for every vertex whose exact mark lookup is concrete and which is not a
global certificate conclusion. These carriers record causal continuation data,
not an active-frontier reserve. The checkpoint's public surface is exactly two
carriers and 21 theorem boundaries.

Primary public declarations:

```text
ProofNetIR.SequentialFigure7.ContinuationCredit
ProofNetIR.SequentialFigure7.MarkedNonconclusionContinuation
ProofNetIR.SequentialFigure7.empty_markedNonconclusionContinuation
ProofNetIR.SequentialFigure7.InitialReservationStep.markedNonconclusionContinuation
ProofNetIR.SequentialFigure7.FutureWorkAt.afterPreparedOrSelected
ProofNetIR.SequentialFigure7.NopStep.selectedContinuationCredit
ProofNetIR.SequentialFigure7.WaitStep.createdConclusionFutureWorkAt
ProofNetIR.SequentialFigure7.WaitStep.selectedContinuationCredit
ProofNetIR.SequentialFigure7.NewStep.selectedContinuationCredit
ProofNetIR.SequentialFigure7.ForwardStep.createdConclusionFutureWorkAt
ProofNetIR.SequentialFigure7.ForwardStep.selectedContinuationCredit
ProofNetIR.SequentialFigure7.UnifyPayloadStep.createdConclusionFutureWorkAt
ProofNetIR.SequentialFigure7.UnifyPayloadStep.selectedContinuationCredit
ProofNetIR.SequentialFigure7.DispatchTagEvidence.newlyMarkedContinuationCredit
ProofNetIR.SequentialFigure7.ConclStep.continuationCredit
ProofNetIR.SequentialFigure7.NopStep.continuationCredit
ProofNetIR.SequentialFigure7.NewStep.continuationCredit
ProofNetIR.SequentialFigure7.WaitStep.continuationCredit
ProofNetIR.SequentialFigure7.ForwardStep.continuationCredit
ProofNetIR.SequentialFigure7.UnifyPayloadStep.continuationCredit
ProofNetIR.SequentialFigure7.DispatchTagEvidence.oldContinuationCredit
ProofNetIR.SequentialFigure7.DispatchTagEvidence.markedNonconclusionContinuation
ProofNetIR.SequentialFigure7.CanonicalTagHistory.markedNonconclusionContinuation
```

The empty and initial-reservation theorems establish the state predicate before
any raw-mark event. Exact fresh-event lemmas then supply credit across all six
dispatcher constructors: Nop and New retain a raw mate, while Wait, Forward,
and UnifyPayload schedule the selected occurrence's connective conclusion;
the Concl case is excluded by the nonconclusion premise at the dispatcher
boundary.

The six branch transports and two dispatcher-level transports require only
structural well-formedness. Nop and New additionally consume the old owner's
concrete mark to rule out their selected-mate residual; the old-credit
dispatcher theorem carries that mark uniformly. Concl rules the same residual
out by its exact conclusion view. Wait, Forward, and UnifyPayload convert it
into scheduled conclusion work. Combining old-credit transport with exact
fresh-event coverage gives one-step preservation, and induction over supplied
`CanonicalTagHistory` gives the full-history state invariant without a
declarative-correctness hypothesis.

This closes continuation credit, not active-top marked-nonconclusion debt. None
of the three receipt forms necessarily supplies a distinct raw-unmarked
nonconclusion on the current active frontier. The earlier exact branch
residuals therefore remain open: Nop and Wait still need selected-away
witnesses, while global-created Forward and UnifyPayload still need non-global
vertices in their exact ready tails. The checkpoint proves neither full debt
preservation nor the unconditional implication from `ActiveTopDrained` to
`core.allMarked = true`, and it makes no progress or history-existence claim.

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
the
[active-top debt branch residuals](api-reference.md#active-top-debt-branch-residuals),
and now
[branch-local continuation credit](api-reference.md#branch-local-continuation-credit)
with its
[full preservation surface](api-reference.md#continuation-credit-preservation).
The structural no-head classifier, conditional drained-to-all-marked reduction,
and supplied-history continuation-credit invariant are kernel-checked. The
first open proof step is to turn the causal credit chain plus the available
correctness and frontier geometry into the selected-away and global-created
exact-tail witnesses, or directly into complete canonical-history preservation
of the active-top debt.

## What the rolling theorem does not prove

This checkpoint does not establish any of the following:

- construction of a relevant `ExecutedHistory`, reachable state, or
  `ReadyHeadInput`;
- conversion of continuation credit into
  `ActiveTopMarkedNonconclusionDebt`;
- the selected-away witness for Nop or Wait from supplied canonical history,
  continuation credit, and correctness;
- the exact non-global tail law for global-created Forward or UnifyPayload from
  supplied canonical history, continuation credit, and correctness;
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
commit    016dab9813192f0a2119eed4cf4ed73be4c1f164
tree      87d0cadaee5ba467772aaece496bb7817569ba11
parent    aba3d5000aeceb1a4e450260ccf913a01269c8ad
stage     full-history continuation-credit preservation
delta     18 paths, +2379/-35
manifest  B1D6965F7FC77AB13DD74B5F4B32D85DCA43C9FF11EC53DC6A2018CADA05BB39
```

The three continuation-credit source receipts are:

```text
base          09967E0F0CDBC1831714538E9256DBDC3791630CD2B832E435B7222957BD8F50
preservation  8A6A9A43F6773BB964D38DCBD3CBB701CE65E7520FD370F61AF4FB568D1A11E7
consumer      FD0B2F204AA163D8820345E4E943880838BA58901282857D2BB1A3FFA2B1B294
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

- full `lake build`: 467/467 jobs;
- Lean source audit: zero actual `sorry`/`admit` findings across 223 Lean
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
- the runnable continuation-credit preservation consumer: passed under
  `--trust=0`, invokes both public carriers and all 21 theorem boundaries,
  case-splits all three receipt constructors, and consumes the raw-mate,
  future-conclusion, and marked-conclusion evidence;
- facade, API manifest, and axiom-audit entry points: passed under `--trust=0`;
- public declaration audit: 940 declarations total;
- audit classes: 653 full-classical, 25 axiom-free, 126 `propext`-only,
  and 136 `propext` plus `Quot.sound`;
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
- `empty_markedNonconclusionContinuation` depends exactly on `[propext]`;
- `FutureWorkAt.afterPreparedOrSelected` depends exactly on
  `[propext, Quot.sound]`;
- the other 19 continuation-credit theorem boundaries depend exactly on
  `[propext, Classical.choice, Quot.sound]`.

Exact-head proof GitHub verification:

- workflow: `Lean CI`;
- event/ref: `push` / `main`;
- run: [32310550692](https://github.com/fushanbobfan/proofnet-ir/actions/runs/32310550692);
- build job: [96252468617](https://github.com/fushanbobfan/proofnet-ir/actions/runs/32310550692/job/96252468617);
- exact head: `016dab9813192f0a2119eed4cf4ed73be4c1f164`;
- result: 36 successful steps, zero failures, one expected release-ref-only
  skip; run duration 10m51s and build-job duration 10m46s.

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

1. convert the full-history continuation-credit chain plus correctness and
   active-frontier geometry into the selected-away witnesses for Nop and Wait
   and the exact non-global tail laws for global-created Forward and
   UnifyPayload, or derive the debt directly; then package
   `ActiveTopMarkedNonconclusionDebt` through complete canonical histories,
   derive the unconditional reachable-state `ActiveTopDrained →
   core.allMarked = true` corollary, and use marking incompleteness to exclude
   the residual;
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
