# Current status

> **Replacement policy:** this page contains one rolling mathematics
> checkpoint. Update it in place; do not append checkpoint history here.

This page is the replaceable status record for the rolling research branch.
It is updated in place when a new mathematics checkpoint supersedes the
previous one.
Historical checkpoints belong in [CHANGELOG.md](../CHANGELOG.md), proof design
belongs in [v0.10-design.md](v0.10-design.md), and stable release guarantees
belong in the corresponding release audit.

Status date: 2026-08-20

## Version tracks

| Track | Revision | Status | Authority |
| --- | --- | --- | --- |
| Stable library | `v0.9.0` / `9b7dc3d104af8f57ea9123aab2e61b42e05d2216` | Released | [v0.9.0 release audit](v0.9-release-audit.md) |
| Rolling research | `v0.10.0-dev`; proof `093c620`; audit `1e46573` | Active | This page/commits |

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

The preceding temporal checkpoint specializes the normalized parent escape to actual Nop
and Wait failures. The preceding source and continuation-credit normalizers
remain valid: when the prepared non-global ready-tail witness is absent, they
map a correct, canonically recorded parent escape to
`ActiveCarrierParentTemporalOutcome`. The new typed-step theorems then rule out
the selected-head raw case. Nop uses its unmarked-mate guard; Wait uses the
strict raw-age order of its concretely marked mate.

The strengthened `ActiveCarrierParentExternalTemporalOutcome` therefore has
only three cases. An unmarked raw endpoint lies outside the active owned
carrier. Future parent work lies outside that carrier at a strictly older raw
boundary. A concretely marked parent conclusion lies outside the carrier and
has a strictly older representative. The last case can continue a connective
chain, and “outside” is component-local rather than global. The carrier is a
failure reduction, not re-entry, a ready-tail witness, residual elimination,
history-tail proof, or derivation of `ActiveTopDebtTailLaw`.

The preceding commitment checkpoint locates each strictly older future or marked endpoint
on the exact retained `sigma` interval ending at the active top. Its
`ActiveCarrierParentExternalCommitmentOutcome` retains the final adjacent
predecessor-to-active edge together with the canonical commitment reference
path already carried by that edge. The external raw branch remains unchanged.
This does not construct a path from the external endpoint to the commitment
edge, prove first re-entry, or produce a distinct ready-tail payer.

The preceding crossing checkpoint connects the active owned carrier to each
strictly older external endpoint and retains one exact owned-to-outside edge.
The preceding re-entry checkpoint then composes every adjacent canonical
commitment path across the complete positive retained `sigma` interval. Ready
future work and older marked endpoints carry an exact path from the endpoint
back into the active owned carrier and one concrete outside-to-inside edge.
Waiting work keeps its exact waiting cell without invented ownership, and
external raw work remains unchanged.

The preceding checkpoint classifies the exact re-entry target. Three reusable
occurrence-geometry theorems first show that owned submitted conclusions own
their premises, internal owned premises retain their conclusion, and every
submitted premise is non-global. An outside-to-inside re-entry edge is
therefore the reverse of an exact submitted connective-parent edge whose
target lies on the active component frontier and whose conclusion remains
outside the occurrence carrier. Exact ready-bucket accounting then gives three
target states: the selected raw head, a raw ready-tail occurrence, or a prior
concrete mark. Under explicit absence of a non-global ready-tail witness, only
the selected-raw and concretely-marked alternatives remain. Neither is yet
eliminated, and the waiting/raw outcome branches remain unresolved.

The preceding re-entry-target checkpoint adds the first history-sensitive reduction of those
two alternatives. Canonical raw-mark history authenticates every concrete
target and proves that its representative is the active boundary. If the
retained re-entry path additionally avoids the current submitted par
conclusion, parent-link uniqueness rules out the selected target. Under the
same explicit no-tail premise, the remaining target is therefore distinct
from the selected head, concretely marked, authenticated by an exact
`RawMarked` event, and represented at the active boundary. The theorem does
not derive the path-avoidance premise or turn that historical mark into a
distinct raw ready-tail payer.

The preceding checkpoint advances that exact avoidance seam. For any adjacent
retained commitment edge, an explicit child-event untouched callback now
produces a reference-switching path that avoids the supplied ready-head par
conclusion. At the active equal-boundary edge, an inclusive dichotomy returns
that avoiding path or an authentic same-age ledger event whose trace contains
the exact par-conclusion step to the selected premise or its mate. This neither
derives the callback nor eliminates either trace orientation.

The preceding checkpoint classifies the complete positive retained commitment
interval against that par conclusion. If every local edge has an avoiding
path, the interval compositor yields one endpoint path. Otherwise the theorem
identifies an exact parent/child edge with no such local path and an authentic
event at the child age whose trace contains the conclusion-to-selected or
conclusion-to-mate step. Strict sigma ordering places that child strictly
before or at the interval's final boundary. The endpoint-path and localized
failed-edge alternatives remain inclusive. The theorem does not discharge the
failed edge, eliminate either trace orientation, or produce a payer or tail
law.

The preceding checkpoint sharpens that failed branch against the active
occurrence carrier. A strictly older authentic trace cannot end at the
selected head or at a mate owned by the active carrier: exact live-carrier
disjointness would place the event's axiom endpoint in two distinct component
carriers. Therefore every strictly older failure is stored-right and traces
to a mate outside the active owned carrier. A failure at the final active
boundary retains both exact conclusion-to-selected and conclusion-to-mate
orientations. The outer alternatives remain inclusive. The theorem does not
localize the external older mate further, eliminate either equal-final trace,
derive a distinct payer or history-tail law, or prove progress.

The current checkpoint specializes that localized interval outcome to actual
Nop and Wait guards. Its common four-case carrier retains the avoiding
endpoint path, equal-final selected trace, equal-final mate trace, and the
strictly older stored-right mate. In the Nop theorem the older mate lies
outside the active carrier and is raw-unmarked. In the Wait theorem it lies
outside, is concretely marked at the exact mate age, and has a representative
strictly below the active boundary. The equal-final cases and inclusive outer
alternatives remain. Neither theorem returns the external endpoint to a
distinct payer, derives the history-tail law, or proves progress.

The preceding queue/history-tail checkpoint remains valid. For supplied typed
Nop and Wait steps, its iff theorems identify post-step debt with the exact
non-global `remainingTop` witness, assuming the input scheduler invariant and
prior debt. Its reset-aware `CanonicalTagHistory.ActiveTopDebtTailLaw` still
packages all six branch obligations, and its endpoint theorem still derives
debt only from a supplied instance of that law. Correctness plus canonical
history has not yet been proved to produce the law.

The earlier Wait obstruction also remains valid: every successful typed Wait
from a scheduler-invariant input refutes unrestricted
`ActiveTopContinuationExitLocalized` at its output. It rules out that unchanged
same-component locality carrier, but neither refutes direct debt nor supplies
the required queue-tail or elimination of the classified re-entry failure.

The checkpoint's accumulated public surface is exactly twenty-two declaration
boundaries:

```text
Certificate.OccurrenceDerivation.connectivePremises_owned_of_conclusion_owned
Certificate.OccurrenceDerivation.connectiveConclusion_owned_of_premise_owned_not_frontier
SequentialFigure7.submittedPremise_not_conclusion
SequentialFigure7.ActiveCarrierInboundParentEdge
SequentialFigure7.ActiveCarrierExternalReentryTargetStatus
SequentialFigure7.ActiveCarrierExternalReentryFailureTargetStatus
SequentialFigure7.ActiveCarrierExternalEndpointReentryAvoiding
SequentialFigure7.ActiveCarrierExternalReentryFailureHistoricalStatus
SequentialFigure7.ActiveCarrierExternalReentryMarkedHistoricalTarget
SequentialFigure7.ActiveCarrierExternalEndpointReentry.targetStatus
SequentialFigure7.ActiveCarrierExternalEndpointReentry.targetFailureStatus
SequentialFigure7.ActiveCarrierExternalEndpointReentry.targetFailureHistoricalStatus
SequentialFigure7.ActiveCarrierExternalEndpointReentryAvoiding.markedHistoricalTarget
SequentialFigure7.CanonicalTagHistory.commitmentEdge_referencePath_avoiding_parConclusion
SequentialFigure7.ReservationEvent.touched_parConclusion_decomposition
SequentialFigure7.ReservationEvent.touched_parConclusion_cases
SequentialFigure7.CanonicalTagHistory.commitmentEdge_parConclusion_dichotomy
SequentialFigure7.CanonicalTagHistory.commitmentInterval_parConclusion_dichotomy
SequentialFigure7.CanonicalTagHistory.commitmentInterval_parConclusion_localizedDichotomy
SequentialFigure7.CanonicalTagHistory.CommitmentIntervalParTraceOutcome
SequentialFigure7.NopStep.commitmentInterval_parTraceOutcome
SequentialFigure7.WaitStep.commitmentInterval_parTraceOutcome
```

The earlier parent-escape, source-temporal, debt, history-tail,
continuation-exit, common and external temporal-outcome, commitment/re-entry,
and conditional all-marked results remain valid. The re-entry reduction
identifies the exact parent-edge, scheduler status, and canonical raw-mark
provenance of each retained target. The current results provide one adjacent
par-conclusion avoiding path from an explicit callback, classify the active
edge as avoidance or one exact trace step, and lift that inclusive
classification across the complete positive interval. The preceding
localization theorem also rules out strictly older selected and
active-owned-mate traces, leaving only a stored-right external mate in that
branch. The new typed-step theorems classify that mate as exact raw-unmarked
work for Nop or exact
older-representative marked work for Wait. They do not make any conditional
implication unconditional.

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
[active-top marked-nonconclusion debt](api-reference.md#active-top-marked-nonconclusion-debt),
[active-top debt branch residuals](api-reference.md#active-top-debt-branch-residuals),
[active-top debt ready-tail normalization](api-reference.md#active-top-debt-ready-tail-normalization),
[active-top debt history-tail law](api-reference.md#active-top-debt-history-tail-law),
[active-top debt parent escape](api-reference.md#active-top-debt-parent-escape),
[parent-escape temporal residual](api-reference.md#active-top-debt-parent-escape-temporal-residual),
[parent temporal outcome](api-reference.md#active-top-debt-parent-temporal-outcome),
[external parent outcome](api-reference.md#active-top-debt-parent-external-temporal-outcome),
[external parent commitment outcome](api-reference.md#active-top-debt-parent-external-commitment-outcome),
[endpoint crossing](api-reference.md#active-top-debt-parent-external-endpoint-crossing),
[commitment re-entry](api-reference.md#active-top-debt-parent-external-commitment-re-entry),
[re-entry target status](api-reference.md#active-top-debt-parent-external-re-entry-target),
[adjacent avoidance](api-reference.md#adjacent-commitment-edge-target-avoidance),
[equal-boundary avoidance](api-reference.md#equal-boundary-commitment-target-avoidance),
[interval par dichotomy](api-reference.md#commitment-interval-par-conclusion-dichotomy),
[interval par-trace localization](api-reference.md#commitment-interval-par-trace-localization),
[interval par-guard outcome](api-reference.md#commitment-interval-par-guard-outcome),
[branch-local continuation credit](api-reference.md#branch-local-continuation-credit),
[continuation-credit preservation](api-reference.md#continuation-credit-preservation),
[endpoint-localized continuation exits](api-reference.md#endpoint-localized-continuation-exits),
and the retained
[Wait endpoint-locality obstruction](api-reference.md#wait-endpoint-locality-obstruction).
The first open proof step is now to return the external raw Nop endpoint to the
active ready tail or descend the external older-representative marked Wait
endpoint to a distinct active payer, and to eliminate both equal-final trace
orientations.
The waiting and external-raw outcome alternatives also remain unresolved.
The remaining global-created Forward/UnifyPayload alternatives must also be
derived.
Together these are the missing implication from correctness plus canonical
tag history to `ActiveTopDebtTailLaw`. Only after that law is established can
the debt and drained reductions contribute to an unconditional progress or
completion argument.

## What the rolling theorem does not prove

This checkpoint does not establish any of the following:

- construction or existence of a relevant `ExecutedHistory`, reachable state,
  `CanonicalTagHistory`, `ReadyHeadInput`, or successful Nop or Wait transition;
- impossibility of `ActiveCarrierParentEscape`, exclusivity between an escape
  and a valid non-global ready-tail witness, or a proof that every escaped raw
  or waiting endpoint re-enters the active carrier;
- elimination of `ActiveCarrierParentExternalTemporalOutcome`, including a
  theorem that external raw or waiting work re-enters the active carrier, or
  that any branch supplies a distinct ready-tail payer;
- return of the exact external raw Nop endpoint or older-representative marked
  Wait endpoint to the active frontier, elimination of either equal-final
  conclusion-to-selected or conclusion-to-mate trace, or conversion of the
  distinct authenticated marked target into a distinct active raw payer;
- terminality of the temporal outcome; in particular, its marked case may
  continue through another submitted connective;
- the ordered distinct-payment or history re-entry law needed to turn the
  classified failure status into the missing queue-tail result;
- derivation of `ActiveTopDebtTailLaw` from declarative correctness,
  reachability, or the matching canonical tag history;
- existence of the exact non-global `remainingTop` witness for Nop or Wait, or
  the exact global-created tail alternative for Forward or UnifyPayload, from
  supplied correctness and history;
- endpoint debt from canonical history alone, without the explicit tail-law
  premise;
- that any reachable canonical history contains a Wait, or that the output of a
  supplied Wait is active-top drained;
- necessity of `ActiveTopContinuationExitLocalized`, or its derivation from
  declarative correctness, reachability, or supplied canonical history;
- preservation of another Wait-compatible drained, temporal, or
  cross-component locality law;
- an unconditional reachable-state proof that `ActiveTopDrained` implies
  `core.allMarked = true`, semantic completion, or terminality without a
  compatible sufficient completion premise;
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
commit    093c620a6aa5f0b21ed2be0433cd7b37af79c7af
tree      7ddfafd41e22364cfaef0fec89072c745415ff2d
parent    82b614b9759d9307ae921c06e911ba9a36046a4c
stage     commitment-interval par-guard outcome
delta     17 paths, +503/-21
manifest  B44A74DF169CC9BBAB9A8E57F4B7D0D2D2FC9523548C21FC46FB69354B7F104D
```

The manifest hashes canonical
`path<TAB>UPPER_SHA256<TAB>blob<LF>` records for the committed delta.

The checkpoint source receipts are:

```text
guard-outcome source    AB84F4F68DFE77795D85BA43B59A60A771D7D062B8F786E4FC34EDB832E44E55
guard-outcome consumer  E6BAE380B0A4EAAA4C8AACB7C56615294E55E2B8005BEF509839F8F3483DC1DB
generated API           1C26CC36E9349BF40889DC475C5D9DC8568D3D178BA5A3EA153BD9EA81542E12
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

- full `lake build`: 539/539 jobs;
- Lean source audit: zero actual `sorry`/`admit` findings across 252 Lean
  files;
- generated API reference: current at 66 sections and 1,644 declarations;
- the runnable guard-outcome consumer called both typed-step theorems,
  reconstructed all four carrier cases, and consumed the exact Nop raw-mate
  and Wait older-representative marked-mate fields before emitting its
  kernel-green marker;
- public theorem audit: 979 entries total: 687 full-classical, 25
  axiom-free, 128 `propext`-only, and 139 `propext` plus `Quot.sound`;
- the default, extended, and cross-variant progress audits passed with every
  incomplete visited state carrying an exact ready head and successful
  dispatch, every dispatch-none stop fully marked, and zero missing-head,
  incomplete-dispatch-none, cycle, or truncation findings;
- facade, generated API, consumer, and axiom-audit entry points passed under
  the checkpoint's trust-zero and warnings-as-errors gates.

Exact-head proof GitHub verification:

- workflow: `Lean CI`;
- event/ref: `push` / `main`;
- run: [32373881611](https://github.com/fushanbobfan/proofnet-ir/actions/runs/32373881611);
- build job: [96440510913][proof-job];
- exact head: `093c620a6aa5f0b21ed2be0433cd7b37af79c7af`;
- result: 36 successful steps, zero failures, and one expected release-ref-only
  skip;
- run: `2026-08-20T13:22:17Z`-`2026-08-20T13:35:44Z` (13m27s);
- build job: `2026-08-20T13:22:21Z`-`2026-08-20T13:35:43Z`
  (13m22s).

[proof-job]: https://github.com/fushanbobfan/proofnet-ir/actions/runs/32373881611/job/96440510913

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

1. return the exact external raw Nop endpoint to the active ready tail, descend
   the older-representative marked Wait endpoint to a distinct active payer,
   and eliminate the equal-final conclusion-to-selected/mate trace
   obstructions over the retained commitment interval;
   resolve the waiting/raw outcome alternatives; then derive the remaining
   global-created Forward/UnifyPayload alternatives;
   equivalently, prove that correctness plus `CanonicalTagHistory` implies
   `ActiveTopDebtTailLaw`. Only after that gate may endpoint debt combine with
   active-top drainedness and marking incompleteness in an unconditional
   progress argument. The unrestricted `ActiveTopContinuationExitLocalized`
   law remains refuted after every supplied successful typed Wait from a
   scheduler-invariant input, so it cannot replace the tail law. Reachable Wait
   existence, post-Wait drainedness, unconditional `allMarked`, progress,
   completion, terminality, later-state totality, and arbitrary history
   existence remain open;
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
