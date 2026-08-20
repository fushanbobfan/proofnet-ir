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
| Rolling research | `v0.10.0-dev`; proof `55dd6a2`; audit `1e46573` | Active | This page/commits |

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

The preceding checkpoint specializes that localized interval outcome to actual
Nop and Wait guards. Its common four-case carrier retains the avoiding
endpoint path, equal-final selected trace, equal-final mate trace, and the
strictly older stored-right mate. In the Nop theorem the older mate lies
outside the active carrier and is raw-unmarked. In the Wait theorem it lies
outside, is concretely marked at the exact mate age, and has a representative
strictly below the active boundary. The equal-final cases and inclusive outer
alternatives remain. Neither theorem returns the external endpoint to a
distinct payer, derives the history-tail law, or proves progress.

The preceding checkpoint uses supplied reference-switching connectedness to
return that strictly older external mate through the exact active-carrier
re-entry path. Its target status is the selected raw head, a non-global raw
ready-tail occurrence, or a prior concrete mark. Thus the ready-tail branch is
an immediate payer, while the selected and marked targets remain unresolved.
The equal-final selected/mate traces and inclusive outer split are unchanged.
These theorems do not eliminate the selected or marked target, derive the
history-tail law, or prove progress.

The preceding checkpoint specializes the strictly older stored-right Nop and
Wait branches to exact failure of the non-global ready-tail obligation. The
all-left reference switching retains the stored-left par edge. Parent-link
uniqueness, the stored-right selected premise, and strict formula complexity
therefore rule out the selected head as the inbound target. Exact no-tail
failure already removes the raw ready-tail case. The surviving target is
distinct from the selected head, concretely marked, authenticated by canonical
raw-mark history, and represented at the active boundary. Nop retains its
external raw-unmarked mate; Wait retains its exact external marked mate and
strictly older representative. The avoiding path and both equal-final trace
branches remain inclusive. The theorem does not eliminate the marked target,
derive the history-tail law, or prove progress.

The preceding checkpoint separates that surviving marked re-entry target from
the current mate. Freshness of the retained simple path already makes its
inbound target distinct from the path's external starting mate. If an exact
connective view rooted at the target had the current selected head as its
mate, structural parent uniqueness would swap the two connective views and
identify the target with the path start. The contradiction rules out that
selected raw-sibling alternative. The new carrier records both vertex
separations and requires every exact connective view rooted at the target to
have a mate distinct from the selected head. The typed Nop and Wait theorems
lift this refinement only through the strictly older stored-right branch.
They do not eliminate the marked target, choose its parent source kind, derive
a ready-tail witness or history-tail law, or prove progress.

The preceding checkpoint binds that same target to the unique submitted parent
represented by the inbound edge. Canonical continuation credit then gives a
target-indexed temporal trichotomy. The target consumer's raw mate is
raw-unmarked outside the active occurrence carrier, its parent conclusion is
queued at a strictly older raw boundary, or that conclusion is concretely
marked with a strictly older representative. The generic theorem retains the
same exact target, edge, consumer, raw-mark event, and active representative;
the typed Nop and Wait theorems refine only the strictly older stored-right
branch of the existing inclusive interval outcome. No trichotomy case is
eliminated, and the avoiding and equal-final branches remain open. The result
does not derive a ready-tail payer, `ActiveTopDebtTailLaw`, or progress.

From that exact target, the preceding checkpoint follows each marked non-global
parent through its finite continuation chain. Its terminal receipt is
raw-unmarked work outside the active carrier, an exact raw return to the
current selected/mate pair, future work at a strictly older boundary, or a
marked global conclusion at a strictly older representative. The raw-return
branch retains the complete chain,
identifies the terminal consumer with the current conclusion, and proves
strict formula-complexity growth from the marked re-entry target to the
current mate. No terminal alternative is eliminated, and the avoiding and
equal-final branches remain inclusive. The result derives neither a distinct
ready-tail payer nor `ActiveTopDebtTailLaw`, completion, or progress.

The preceding checkpoint orders that proof-relevant cyclic normal form. The
retained switching prefix and strictly forward continuation tail remain
individually nonbacktracking. If cyclic normalization removes the splice
completely, either both segments are empty or both are nonempty. In the
nonempty case the exact cancellation site is one of the two cyclic segment
junctions. Every retained-prefix edge is backward, has its exact reverse in
the continuation tail, and targets a concrete marked non-global chain vertex;
every continuation-tail edge has its exact reverse in the prefix. Both
edge-index lists are duplicate-free. Simple-path source uniqueness now orders
the complete-cancellation tail as exactly
`Graph.EdgeWalk.reverseTraversal retainedPrefix`, rather than leaving only an
unordered mutual pairing. If a nonempty remainder survives, declarative
correctness still exposes the kept and omitted premise occurrences of an exact
par. The omitted-right occurrence lies in the continuation tail, and its
source is retained as a concrete marked non-global vertex from the finite
continuation chain. The target-level adapter refines only the exact raw-return
branch and leaves raw-outside, older-future, and older-marked-global exits
unchanged. The exact out-and-back traversal and marked par-pair residual are
not eliminated. Avoiding and equal-final branches, the history-tail law, and
progress remain open.

The current checkpoint eliminates the exact raw return specifically from the
typed Nop marked re-entry target. Every nontrivial marked-conclusion chain ends
at a concretely marked vertex. A successful Nop instead keeps its current
opposite premise raw-unmarked, so a nontrivial chain cannot terminate at that
mate. The refined Nop target retains raw work outside the active occurrence
carrier, future work at a strictly older boundary, and a marked global
conclusion at a strictly older representative. The generic cyclic reduction
and the corresponding Wait exact-return branch remain valid and unresolved.
The result supplies no ready-tail witness, history-tail law, completion, or
progress theorem.

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

The checkpoint's accumulated public surface is exactly fifty-three declaration
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
SequentialFigure7.NopStep.commitmentInterval_parTraceReentryTargetOutcome
SequentialFigure7.WaitStep.commitmentInterval_parTraceReentryTargetOutcome
SequentialFigure7.NopStep.commitmentInterval_parTraceReentryMarkedOutcome
SequentialFigure7.WaitStep.commitmentInterval_parTraceReentryMarkedOutcome
SequentialFigure7.ActiveCarrierExternalReentryMarkedMateSeparatedTarget
SequentialFigure7.ActiveCarrierExternalReentryMarkedHistoricalTarget.mateSeparated
SequentialFigure7.NopStep.commitmentInterval_parTraceReentryMateSeparatedOutcome
SequentialFigure7.WaitStep.commitmentInterval_parTraceReentryMateSeparatedOutcome
SequentialFigure7.ActiveCarrierExternalReentryMarkedMateSeparatedTemporalTarget
SequentialFigure7.ActiveCarrierExternalReentryMarkedMateSeparatedTarget.temporalTarget
SequentialFigure7.NopStep.commitmentInterval_parTraceReentryMarkedTemporalOutcome
SequentialFigure7.WaitStep.commitmentInterval_parTraceReentryMarkedTemporalOutcome
SequentialFigure7.ActiveCarrierExternalReentryMarkedMateSeparatedContinuationExitTarget
SequentialFigure7.ActiveCarrierExternalReentryMarkedMateSeparatedTemporalTarget.continuationExitTarget
SequentialFigure7.NopStep.commitmentInterval_parTraceReentryMarkedContinuationExitOutcome
SequentialFigure7.WaitStep.commitmentInterval_parTraceReentryMarkedContinuationExitOutcome
SequentialFigure7.MarkedConclusionRawReturnCyclicOutcome
SequentialFigure7.MarkedConclusionChain.rawReturnCyclicReduction
SequentialFigure7.MarkedConclusionRawReturnCyclicCancellationSite
SequentialFigure7.MarkedConclusionRawReturnCompleteCancellationPairing
SequentialFigure7.MarkedConclusionRawReturnCompleteCancellationTraversal
SequentialFigure7.ActiveCarrierExternalReentryMarkedMateSeparatedContinuationCyclicReductionTarget
SequentialFigure7.ActiveCarrierExternalReentryMarkedMateSeparatedContinuationExitTarget.
  continuationCyclicReductionTarget
SequentialFigure7.MarkedConclusionRawReturnCyclicJunctionOutcome
SequentialFigure7.MarkedConclusionChain.rawReturnCyclicJunctionReduction
SequentialFigure7.ActiveCarrierExternalReentryMarkedMateSeparatedContinuationCyclicJunctionTarget
SequentialFigure7.ActiveCarrierExternalReentryMarkedMateSeparatedContinuationCyclicReductionTarget.
  cyclicJunctionTarget
SequentialFigure7.MarkedConclusionChain.terminal_marked_of_ne
SequentialFigure7.ActiveCarrierExternalReentryMarkedMateSeparatedContinuationNoExactReturnTarget
SequentialFigure7.ActiveCarrierExternalReentryMarkedMateSeparatedContinuationExitTarget.
  nopNoExactReturnTarget
SequentialFigure7.NopStep.
  commitmentInterval_parTraceReentryMarkedContinuationNoExactReturnOutcome
```

The earlier parent-escape, source-temporal, debt, history-tail,
continuation-exit, common and external temporal-outcome, commitment/re-entry,
and conditional all-marked results remain valid. The re-entry reduction
identifies the exact parent-edge, scheduler status, and canonical raw-mark
provenance of each retained target. The preceding results provide one adjacent
par-conclusion avoiding path from an explicit callback, classify the active
edge as avoidance or one exact trace step, and lift that inclusive
classification across the complete positive interval. The preceding
localization theorem also rules out strictly older selected and
active-owned-mate traces, leaving only a stored-right external mate in that
branch. The preceding typed-step theorems classify that mate as exact
raw-unmarked work for Nop or exact older-representative marked work for Wait.
The preceding theorems use supplied connectedness to add one exact inbound
re-entry edge and classify its active-frontier target as selected raw work,
non-global raw ready-tail work, or a prior concrete mark. They do not make any
conditional implication unconditional. The preceding theorems add exact
no-tail failure and exclude the selected target only in the strictly older
stored-right branch. They retain a distinct authenticated concrete mark at the
active representative. The preceding theorems further separate that target
from the current mate and rule out the current selected head as the mate of
any exact connective view rooted at the target. The preceding target-indexed
theorem binds the same target to its unique parent and normalizes that parent's
first continuation step. The preceding theorem follows every marked non-global
parent through a finite chain and ends raw outside the carrier, at an exact raw
return to the current pair, at strictly older queued work, or at a strictly
older marked global conclusion. It does not eliminate any alternative or make
any conditional implication unconditional. The preceding theorems refine only
that exact raw return. Complete cancellation is empty or localized to one of
the two exact junctions of the individually nonbacktracking prefix and tail.
In the nonempty case the two duplicate-free edge lists are mutually paired by
exact reversal; prefix edges are backward, tail edges are forward, and every
prefix target is concretely marked and non-global. Simple-path source
uniqueness further identifies the continuation tail with the exact reverse
traversal of the retained prefix. A surviving exact par pair keeps its left
occurrence in the prefix and its omitted-right occurrence in the continuation
tail, whose source is a concrete marked non-global chain vertex. The theorems
eliminate neither residual and make no conditional implication unconditional.
The current Nop theorem then removes the exact return to the current mate by
combining concrete terminal marking for every nontrivial chain with the typed
Nop mate-unmarked equation. The other three continuation exits, every Wait
residual, and all avoiding/equal-final branches remain unchanged.

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
[interval par-guard re-entry](api-reference.md#commitment-interval-par-guard-re-entry),
[interval par-guard re-entry failure target][reentry-failure],
[interval par-guard re-entry mate separation][reentry-mate-separation],
[marked re-entry target temporal reduction][target-temporal],
[marked re-entry target finite continuation exit][target-exit],
[marked re-entry target Nop raw-return elimination][target-nop-no-return],
[marked re-entry target raw-return cyclic reduction][target-cycle],
[branch-local continuation credit](api-reference.md#branch-local-continuation-credit),
[continuation-credit preservation](api-reference.md#continuation-credit-preservation),
[endpoint-localized continuation exits](api-reference.md#endpoint-localized-continuation-exits),
and the retained
[Wait endpoint-locality obstruction](api-reference.md#wait-endpoint-locality-obstruction).
The first open proof step is now to eliminate the remaining Wait/generic exact
out-and-back traversal, or use its path, mark, and history uniqueness to
convert it into a distinct payer. The surviving marked omitted-right source
must likewise be eliminated or converted into a distinct payer. The
raw-outside, older-future, and
older-marked-global alternatives and both equal-final trace orientations also
remain to be discharged.
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
  theorem that generic external raw or waiting work re-enters the active
  carrier, or that any branch supplies a distinct ready-tail payer;
- elimination of the prior-concrete-mark target in the strictly older re-entry,
  elimination of either equal-final conclusion-to-selected or
  conclusion-to-mate trace, elimination of the finite raw-outside,
  older-future, or older-marked-global continuation alternatives, or the exact
  raw return in Wait and generic contexts, or
  conversion of that target into a distinct active raw payer;
- impossibility of the remaining Wait/generic ordered exact out-and-back
  cyclic-junction traversal, elimination of the surviving marked omitted-right
  par pair, or conversion of either cyclic residual into a distinct ready-tail
  payer;
- a terminal scheduler state or elimination of any finite continuation exit;
  normalization terminates the marked chain but does not discharge its
  raw, future, or marked-global endpoint;
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
commit    55dd6a2e52ed810d73e58357e1f44205626c8ec2
tree      68edad0f4e037937324dd8c9f52554d34638467b
parent    517bd68f285204c96569016447488399ef364f69
stage     eliminate the typed Nop exact raw return
delta     17 paths, +605/-16
manifest  3638972CEE42C404A8355C10439CAE78687A2C00F3CEBD7EAE799ED4CB0D40A5
```

The manifest hashes canonical
`path<TAB>UPPER_SHA256<TAB>blob<LF>` records for the committed delta.

The checkpoint source receipts are:

```text
Nop source      258F86F64D84851FF0E096DD2AE08A677F77D1A529DC7E63C7EA165A92066B45
Nop consumer    E8A2C8B9573FDB4231E7BFD87F6A855CA1C76A21DDA601E96ACC6EA1FAB3BC01
generated API   939A250159D482FAE7D01F0BEAE687438AA3EA18253355B1D85360BB6E0CB862
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

- full `lake build`: 574/574 jobs;
- Lean source audit: zero actual `sorry`/`admit` findings across 266 Lean
  files;
- generated API reference: current at 73 sections and 1,675 declarations;
- the runnable Nop raw-return-elimination consumer called the terminal-mark
  theorem, refined a supplied generic target, destructed every remaining exit,
  applied the integrated commitment-interval theorem, cased every outer
  outcome, and audited all four public declarations before emitting its
  kernel-green marker;
- public theorem audit: 999 entries total: 706 full-classical, 25
  axiom-free, 129 `propext`-only, and 139 `propext` plus `Quot.sound`;
- the default, extended, and cross-variant progress audits passed with every
  incomplete visited state carrying an exact ready head and successful
  dispatch, every dispatch-none stop fully marked, and zero missing-head,
  incomplete-dispatch-none, cycle, or truncation findings;
- facade, generated API, consumer, and axiom-audit entry points passed under
  the checkpoint's trust-zero and warnings-as-errors gates.

Exact-head proof GitHub verification:

- workflow: `Lean CI`;
- event/ref: `push` / `main`;
- run: [32424826209](https://github.com/fushanbobfan/proofnet-ir/actions/runs/32424826209);
- build job: [96604488097][proof-job];
- exact head: `55dd6a2e52ed810d73e58357e1f44205626c8ec2`;
- result: 36 successful steps, zero failures, and one expected release-ref-only
  skip;
- run: `2026-08-20T22:33:55Z`-`2026-08-20T22:47:42Z` (13m47s);
- build job: `2026-08-20T22:33:59Z`-`2026-08-20T22:47:41Z`
  (13m42s).

[proof-job]: https://github.com/fushanbobfan/proofnet-ir/actions/runs/32424826209/job/96604488097
[reentry-failure]: api-reference.md#commitment-interval-par-guard-re-entry-failure-target
[reentry-mate-separation]: api-reference.md#commitment-interval-par-guard-re-entry-mate-separation
[target-temporal]: api-reference.md#commitment-interval-marked-re-entry-target-temporal-reduction
[target-exit]: api-reference.md#marked-re-entry-target-finite-continuation-exit
[target-nop-no-return]: api-reference.md#marked-re-entry-target-nop-raw-return-elimination
[target-cycle]: api-reference.md#marked-re-entry-target-raw-return-cyclic-reduction

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

1. eliminate the remaining Wait/generic exact raw return's ordered
   out-and-back traversal and its par-pair residual; discharge the
   mate-separated target's
   finite raw-outside,
   older-future, and older-marked-global continuation alternatives; eliminate
   that target or descend its mark to a distinct active payer; and eliminate the equal-final
   conclusion-to-selected/mate trace obstructions over the retained commitment
   interval;
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
