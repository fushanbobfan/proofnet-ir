# Current status

> **Replacement policy:** this page contains one rolling mathematics
> checkpoint. Update it in place; do not append checkpoint history here.

This page is the replaceable status record for the rolling research branch.
It is updated in place when a new mathematics checkpoint supersedes the
previous one.
Historical checkpoints belong in [CHANGELOG.md](../CHANGELOG.md), proof design
belongs in [v0.10-design.md](v0.10-design.md), and stable release guarantees
belong in the corresponding release audit.

Status date: 2026-08-21

## Version tracks

| Track | Revision | Status | Authority |
| --- | --- | --- | --- |
| Stable library | `v0.9.0` / `9b7dc3d104af8f57ea9123aab2e61b42e05d2216` | Released | [v0.9.0 release audit](v0.9-release-audit.md) |
| Rolling research | `v0.10.0-dev`; proof `09d779c`; audit `1e46573` | Active | This page/commits |

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

The preceding checkpoint eliminates the exact raw return specifically from the
typed Nop marked re-entry target. Every nontrivial marked-conclusion chain ends
at a concretely marked vertex. A successful Nop instead keeps its current
opposite premise raw-unmarked, so a nontrivial chain cannot terminate at that
mate. The refined Nop target retains raw work outside the active occurrence
carrier, future work at a strictly older boundary, and a marked global
conclusion at a strictly older representative. The generic cyclic reduction
and the corresponding Wait exact-return branch remain valid and unresolved.
The result supplies no ready-tail witness, history-tail law, completion, or
progress theorem.

The preceding checkpoint refines the exact raw return retained by the generic and
typed Wait targets. The re-entry premise is concretely marked at the active
representative, while its exact submitted parent conclusion lies outside the
active occurrence carrier. Any nontrivial return chain therefore reaches that
parent conclusion at its first step, where exact occurrence ownership makes
its representative strictly older. Canonical tag history authenticates the
same conclusion with a concrete `RawMarked` event. The refined target retains
raw work outside the carrier, this first-step descent, older future work, and
an older marked global conclusion. It exposes rather than eliminates the Wait
descent and derives no ready-tail witness, history-tail law, completion, or
progress theorem.

The preceding causal checkpoint makes the event order of authentic
prepared-selection raw marks explicit. A prior relation survives each later
dispatcher event, while every authentic prior mark precedes the current
selection. Both endpoints remain available and distinct. If a submitted
connective conclusion has an authentic raw-mark event, both submitted premises
have authentic strictly earlier events. The first representative descent
therefore places the re-entry origin and its sibling before the first older
marked parent conclusion, while retaining a finite continuation exit for that
sibling.

The preceding terminal checkpoint proves that strict canonical raw-mark order is
transitive and asymmetric, then follows the first causal descent through its
entire finite marked-conclusion chain. A reflexive chain has the same origin
and terminal; otherwise its origin strictly precedes an authenticated terminal
event. Consequently both the re-entry origin and the first connective's
opposite premise precede the full chain terminal. The target adapter
authenticates the outer mate, which is that terminal in the causal-descent
alternative, and the typed Wait theorem propagates the receipt through every
retained commitment-interval outcome. This orders but does not eliminate the
descent or sibling continuation exit. It derives no ready-tail witness,
history-tail law, completion, or progress theorem, and does not yet expose a
total comparison theorem for arbitrary authentic raw marks.

The preceding checkpoint makes that canonical raw-mark chronology total on
distinct authentic vertices and exposes the equality-or-two-orders comparison
for any two authentic events. It then classifies the first descent's sibling
continuation against the authenticated non-global outer-mate terminal. Raw and
future exits remain unchanged. A marked-global endpoint is distinct from the
outer terminal and is therefore strictly earlier or strictly later. The
generic target adapter and typed Wait theorem preserve the descent and carry
this classification through the retained interval outcome. Neither ordered
branch nor any raw/future endpoint is eliminated, and no ready-tail witness,
history-tail law, completion, or progress theorem follows.

The preceding checkpoint applies the existing exact cyclic-junction reduction
to the complete marked-conclusion chain retained by that same first descent.
Its strengthened target keeps the same switching path and target connective
while carrying both the sibling causal classification and cyclic-junction
outcome. The typed Wait theorem transports that combined witness through the
strictly older interval branch. This aligns chronology and switching geometry
without eliminating a junction, ordered marked-global branch, raw/future
endpoint, or descent. It derives no payer, history-tail law, completion, or
progress theorem.

The preceding checkpoint resolves the endpoint geometry inside nonempty complete
cancellation without removing that branch. Exact reverse traversal now yields
both endpoint reverse junctions simultaneously, together with their four exact
walk endpoints. The same complete marked-conclusion chain classifies the
cyclic source as equal to the authenticated outer terminal or strictly before
it in canonical raw-mark order. The generic target adapter and typed Wait
theorem retain that combined endpoint classification on the same witness.
Complete cancellation, both junctions, the surviving par-pair residual,
sibling exits, both marked-global orders, and the causal descent remain open.
No payer, history-tail law, completion, or progress theorem follows.

The preceding checkpoint eliminates the equality side of that endpoint
classification when the complete-cancellation prefix is nonempty. The
duplicate-free prefix indices and internal no-immediate-reverse law make the
retained prefix cyclically nonbacktracking. If its source equaled its base,
retention through the exact reference mask would therefore give a nonempty
cyclically nonbacktracking closed walk in the correct reference-switching tree,
a contradiction. The strengthened causal theorem returns both exact endpoint
junctions together with an authenticated strict source-before-base event.
Complete cancellation and both junctions remain; only source-equals-base is
removed in this nonempty correct branch. No payer, history-tail law,
completion, or progress theorem follows.

The preceding sibling-open checkpoint re-roots the first causal descent's
sibling continuation after its shared marked non-global conclusion. Reflexive
raw, future, and marked-global exits at that source contradict, respectively,
the marked opposite premise, queued-vertex unmarkedness, and source
non-globality. Comparing the sibling exit with the authenticated outer-mate
chain forces any marked-global endpoint strictly after the outer event.

The preceding checkpoint carries the remaining raw/future exit through exact
scheduler and canonical-history semantics. Raw work is outside the active
occurrence carrier or returns exactly to the current selected/mate pair. Older
future work has an exact ready component or waiting span; both of its submitted
premises are concretely marked and canonically ordered. The outside terminal's
representative is strictly older. Its mate is either older outside the active
carrier or active-owned at the active representative. Exact ready-component
occurrence ownership now eliminates the active-owned ready alternative: it
would place the same mate in live carriers at two distinct boundaries. The
surviving active-owned case is the exact older-terminal-to-active-mate waiting
return. An older-outside mate may still be ready or waiting. This removes one
scheduler subcase, not the exact raw return, future endpoint, causal descent,
complete cancellation, cyclic junctions, par-pair residual, or ready-tail
failure. No payer, history-tail law, completion, or progress theorem follows.

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

The earlier focused boundary ledger below records 181 declarations through the
continuation-exit layer together with the reusable queue-status primitives. The
generated API reference is authoritative for the complete public surface:

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
SequentialFigure7.MarkedConclusionChainFirstRepresentativeDescent
SequentialFigure7.MarkedConclusionChain.firstRepresentativeDescent_of_ne
SequentialFigure7.ActiveCarrierExternalReentryMarkedMateSeparatedContinuationFirstDescentTarget
SequentialFigure7.ActiveCarrierExternalReentryMarkedMateSeparatedContinuationExitTarget.
  firstDescentTarget
SequentialFigure7.WaitStep.
  commitmentInterval_parTraceReentryMarkedContinuationFirstDescentOutcome
SequentialFigure7.CanonicalTagHistory.RawMarkedBefore
SequentialFigure7.CanonicalTagHistory.RawMarkedBefore.first_rawMarked
SequentialFigure7.CanonicalTagHistory.RawMarkedBefore.second_rawMarked
SequentialFigure7.CanonicalTagHistory.RawMarkedBefore.vertex_ne
SequentialFigure7.CanonicalTagHistory.rawMarkedPremisesBefore
SequentialFigure7.MarkedConclusionChainFirstCausalDescent
SequentialFigure7.MarkedConclusionChainFirstRepresentativeDescent.causalDescent
SequentialFigure7.ActiveCarrierExternalReentryMarkedMateSeparatedContinuationCausalDescentTarget
SequentialFigure7.ActiveCarrierExternalReentryMarkedMateSeparatedContinuationFirstDescentTarget.
  causalDescentTarget
SequentialFigure7.WaitStep.
  commitmentInterval_parTraceReentryMarkedContinuationCausalDescentOutcome
SequentialFigure7.CanonicalTagHistory.RawMarkedBefore.trans
SequentialFigure7.CanonicalTagHistory.RawMarkedBefore.asymmetric
SequentialFigure7.MarkedConclusionChain.rawMarkedBefore_or_eq
SequentialFigure7.MarkedConclusionChainFirstCausalDescent.originBeforeTerminal
SequentialFigure7.MarkedConclusionChainFirstCausalDescent.mateBeforeTerminal
SequentialFigure7.
  ActiveCarrierExternalReentryMarkedMateSeparatedContinuationTerminalCausalTarget
SequentialFigure7.
  ActiveCarrierExternalReentryMarkedMateSeparatedContinuationCausalDescentTarget.
    terminalCausalTarget
SequentialFigure7.WaitStep.
  commitmentInterval_parTraceReentryMarkedContinuationTerminalCausalOutcome
SequentialFigure7.CanonicalTagHistory.RawMarkedBefore.total_of_vertex_ne
SequentialFigure7.CanonicalTagHistory.RawMarkedBefore.eq_or_before_or_after
SequentialFigure7.ContinuationExitOuterTerminalCausalOutcome
SequentialFigure7.ContinuationExit.outerTerminalCausalOutcome
SequentialFigure7.MarkedConclusionChainFirstCausalDescent.
  siblingExitOuterTerminalCausalOutcome
SequentialFigure7.
  ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitCausalTarget
SequentialFigure7.
  ActiveCarrierExternalReentryMarkedMateSeparatedContinuationTerminalCausalTarget.
    siblingExitCausalTarget
SequentialFigure7.WaitStep.
  commitmentInterval_parTraceReentryMarkedContinuationSiblingExitCausalOutcome
SequentialFigure7.MarkedConclusionChainFirstCausalDescent.
  rawReturnCyclicJunctionOutcome
SequentialFigure7.
  ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitCausalJunctionTarget
SequentialFigure7.
  ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitCausalTarget.
    causalJunctionTarget
SequentialFigure7.WaitStep.
  commitmentInterval_parTraceReentryMarkedContinuationSiblingExitCausalJunctionOutcome
SequentialFigure7.MarkedConclusionRawReturnCompleteCancellationEndpointJunctions
SequentialFigure7.MarkedConclusionRawReturnCompleteCancellationTraversal.
  endpointJunctions
SequentialFigure7.MarkedConclusionRawReturnCyclicJunctionCausalOutcome
SequentialFigure7.MarkedConclusionChainFirstCausalDescent.
  rawReturnCyclicJunctionCausalOutcome
SequentialFigure7.
  ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitCausalEndpointTarget
SequentialFigure7.
  ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitCausalJunctionTarget.
    causalEndpointTarget
SequentialFigure7.WaitStep.
  commitmentInterval_parTraceReentryMarkedContinuationSiblingExitCausalEndpointOutcome
SequentialFigure7.MarkedConclusionRawReturnCompleteCancellationTraversal.source_ne_base
SequentialFigure7.MarkedConclusionRawReturnCyclicJunctionCausalOutcome.completeEndpoints
SequentialFigure7.ContinuationExitOuterTerminalForwardCausalOutcome
SequentialFigure7.ContinuationExit.afterMarkedSibling
SequentialFigure7.ContinuationExit.outerTerminalForwardCausalOutcome
SequentialFigure7.
  ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitForwardCausalTarget
SequentialFigure7.
  ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitCausalEndpointTarget.
    forwardCausalTarget
SequentialFigure7.WaitStep.
  commitmentInterval_parTraceReentryMarkedContinuationSiblingExitForwardCausalOutcome
SequentialFigure7.MarkedConclusionChain.terminalComparable
SequentialFigure7.ContinuationExitRawOrFuture
SequentialFigure7.MarkedConclusionChainFirstCausalDescent.sourceExitRawOrFuture
SequentialFigure7.
  ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitOpenTarget
SequentialFigure7.
  ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitForwardCausalTarget.
    openTarget
SequentialFigure7.WaitStep.
  commitmentInterval_parTraceReentryMarkedContinuationSiblingExitOpenOutcome
SequentialFigure7.ContinuationExitRawOrFutureActiveCarrierOutcome
SequentialFigure7.ContinuationExitRawOrFuture.activeCarrierOutcome
SequentialFigure7.
  ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitTemporalTarget
SequentialFigure7.
  ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitOpenTarget.
    temporalTarget
SequentialFigure7.WaitStep.
  commitmentInterval_parTraceReentryMarkedContinuationSiblingExitTemporalOutcome
SequentialFigure7.FutureWorkAtExactSchedulerLocation
SequentialFigure7.FutureWorkAt.exactSchedulerLocation
SequentialFigure7.ConnectiveBelow.premisesMarked_of_futureWork
SequentialFigure7.UnmarkedOutsideActiveSchedulerStatus
SequentialFigure7.FutureWorkAt.boundary_lt_active_of_not_owned
SequentialSchedulerBridge.SchedulerInvariant.mem_queued_iff_exists_futureWorkAt
SequentialSchedulerBridge.SchedulerInvariant.unmarkedOutsideActiveSchedulerStatus
SequentialFigure7.ContinuationExitRawOrFutureActiveCarrierScheduledOutcome
SequentialFigure7.ContinuationExitRawOrFutureActiveCarrierOutcome.scheduledOutcome
SequentialFigure7.
  ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitScheduledTarget
SequentialFigure7.
  ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitTemporalTarget.
    scheduledTarget
SequentialFigure7.WaitStep.
  commitmentInterval_parTraceReentryMarkedContinuationSiblingExitScheduledOutcome
SequentialFigure7.MarkedVertexActiveCarrierStatus
SequentialFigure7.ConnectiveBelow.futureWorkPremises_causalOwnership
SequentialFigure7.FutureWorkActiveMateSchedulerOutcome
SequentialFigure7.FutureWorkAtExactSchedulerLocation.activeMateSchedulerOutcome
SequentialFigure7.FutureWorkMateActiveCarrierScheduledStatus
SequentialFigure7.ContinuationExitRawOrFutureActiveCarrierCausalOwnershipOutcome
SequentialFigure7.ContinuationExitRawOrFutureActiveCarrierScheduledOutcome.
  causalOwnershipOutcome
SequentialFigure7.
  ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitCausalOwnershipTarget
SequentialFigure7.
  ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitScheduledTarget.
    causalOwnershipTarget
SequentialFigure7.WaitStep.
  commitmentInterval_parTraceReentryMarkedContinuationSiblingExitCausalOwnershipOutcome
SequentialFigure7.FutureWorkActiveMateWaitingOutcome
SequentialFigure7.FutureWorkActiveMateSchedulerOutcome.waitingOutcome_of_activeOwned
SequentialFigure7.FutureWorkMateActiveCarrierReadyEliminatedStatus
SequentialFigure7.FutureWorkMateActiveCarrierScheduledStatus.readyEliminatedStatus
SequentialFigure7.ContinuationExitRawOrFutureActiveCarrierReadyMateOutcome
SequentialFigure7.ContinuationExitRawOrFutureActiveCarrierCausalOwnershipOutcome.
  readyMateOutcome
SequentialFigure7.
  ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitReadyMateTarget
SequentialFigure7.
  ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitCausalOwnershipTarget.
    readyMateTarget
SequentialFigure7.WaitStep.
  commitmentInterval_parTraceReentryMarkedContinuationSiblingExitReadyMateOutcome
SequentialFigure7.ActiveMateWaitingParentExternalTemporalOutcome
SequentialFigure7.ActiveMateWaitingParentExternalTemporalOutcome.activeCarrierOutcome
SequentialFigure7.FutureWorkActiveMateWaitingOutcome.parentExternalTemporalOutcome
SequentialFigure7.FutureWorkMateActiveCarrierExternalTemporalStatus
SequentialFigure7.FutureWorkMateActiveCarrierReadyEliminatedStatus.externalTemporalStatus
SequentialFigure7.ContinuationExitRawOrFutureActiveCarrierExternalTemporalOutcome
SequentialFigure7.ContinuationExitRawOrFutureActiveCarrierReadyMateOutcome.
  externalTemporalOutcome
SequentialFigure7.
  ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitExternalTemporalTarget
SequentialFigure7.
  ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitReadyMateTarget.
    externalTemporalTarget
SequentialFigure7.WaitStep.
  commitmentInterval_parTraceReentryMarkedContinuationSiblingExitExternalTemporalOutcome
SequentialFigure7.ActiveCarrierExternalEndpointCrossing.reentry
SequentialFigure7.ActiveMateWaitingParentExternalCommitmentReentryFailureOutcome
SequentialFigure7.ActiveMateWaitingParentExternalTemporalOutcome.
  commitmentReentryFailureOutcome
SequentialFigure7.ActiveCarrierExternalReentryFailureHistoricalStatus.
  markedHistoricalTarget_of_storedRight
SequentialFigure7.ActiveMateWaitingParentExternalCommitmentReentryMarkedOutcome
SequentialFigure7.ActiveMateWaitingParentExternalCommitmentReentryFailureOutcome.
  markedOutcome_of_storedRight
SequentialFigure7.FutureWorkMateActiveCarrierExternalCommitmentReentryMarkedStatus
SequentialFigure7.FutureWorkMateActiveCarrierExternalTemporalStatus.
  commitmentReentryMarkedStatus_of_storedRight
SequentialFigure7.
  ContinuationExitRawOrFutureActiveCarrierExternalCommitmentReentryMarkedOutcome
SequentialFigure7.ContinuationExitRawOrFutureActiveCarrierExternalTemporalOutcome.
  commitmentReentryMarkedOutcome_of_storedRight
SequentialFigure7.
  ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitWaitingMarkedTarget
SequentialFigure7.
  ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitExternalTemporalTarget.
    waitingMarkedTarget_of_storedRight
SequentialFigure7.WaitStep.
  commitmentInterval_parTraceReentryMarkedContinuationSiblingExitWaitingMarkedOutcome
SequentialFigure7.ActiveCarrierExternalReentryMarkedOuterMateSeparatedTemporalTarget
SequentialFigure7.ActiveCarrierExternalReentryMarkedHistoricalTarget.
  outerMateSeparatedTemporalTarget
SequentialFigure7.ActiveMateWaitingParentExternalCommitmentReentryTemporalOutcome
SequentialFigure7.ActiveMateWaitingParentExternalCommitmentReentryMarkedOutcome.
  temporalOutcome
SequentialFigure7.FutureWorkMateActiveCarrierExternalCommitmentReentryTemporalStatus
SequentialFigure7.FutureWorkMateActiveCarrierExternalCommitmentReentryMarkedStatus.
  temporalStatus
SequentialFigure7.
  ContinuationExitRawOrFutureActiveCarrierExternalCommitmentReentryTemporalOutcome
SequentialFigure7.
  ContinuationExitRawOrFutureActiveCarrierExternalCommitmentReentryMarkedOutcome.
    temporalOutcome
SequentialFigure7.
  ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitWaitingTemporalTarget
SequentialFigure7.
  ActiveCarrierExternalReentryMarkedMateSeparatedContinuationSiblingExitWaitingMarkedTarget.
    temporalTarget
SequentialFigure7.WaitStep.
  commitmentInterval_parTraceReentryMarkedContinuationSiblingExitWaitingTemporalOutcome
SequentialFigure7.ActiveCarrierExternalReentryMarkedOuterMateSeparatedContinuationExitTarget
SequentialFigure7.ActiveCarrierExternalReentryMarkedOuterMateSeparatedTemporalTarget.
  continuationExitTarget
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
The preceding Nop theorem then removes the exact return to the current mate by
combining concrete terminal marking for every nontrivial chain with the typed
Nop mate-unmarked equation. The other three continuation exits, every Wait
residual, and all avoiding/equal-final branches remain unchanged.
The preceding refinement keeps the generic and Wait return but exposes its first
submitted parent conclusion outside the active carrier. That conclusion is an
authentic canonical raw-mark event whose representative is strictly older than
the active boundary. This is a history-sensitive descent residual, not its
elimination or a distinct ready-tail payer.
The preceding refinement orders the first older marked conclusion after both
submitted-premise raw-mark events, makes the origin and sibling occurrences
distinct from it, and retains a finite continuation exit for the sibling. The
preceding refinement proves transitivity and asymmetry of that event order and
extends both premise-before facts to the authenticated outer-mate terminal of
the full marked chain. It does not eliminate the causal descent or sibling
exit. The preceding refinement makes distinct authentic raw marks comparable,
identifies the same-event case by age and vertex, and classifies a marked-global
sibling endpoint strictly before or after the non-global outer terminal. Raw
and future sibling exits remain unchanged, so this is a causal classification
rather than an endpoint elimination. The preceding refinement applies the exact
cyclic-junction reduction to the full chain retained by that same descent and
stores its result beside the sibling causal outcome on the same switching
path. It aligns the two witnesses but eliminates neither one.
The preceding refinement replaces the disjunctive nonempty cancellation site by
both exact reverse endpoint junctions simultaneously and places the cyclic
source at or before the authenticated outer terminal. It orders and exposes
the same residual witnesses without eliminating complete cancellation or any
endpoint.
The preceding refinement rules out equality in that nonempty branch, so the
cyclic source is now strictly before the authenticated outer terminal while
both exact reverse junctions remain. It does not eliminate the out-and-back
traversal, either endpoint, or any sibling, par-pair, or marked-global
alternative.

The preceding sibling-exit refinement re-roots the sibling continuation after
the first causal descent's shared marked non-global conclusion. Finite-chain
terminal comparability then rules out a marked-global endpoint before the
authenticated outer mate and orders the surviving marked-global endpoint
strictly after it. Raw-mate and future-work endpoints remain unchanged.

The preceding refinement eliminates that remaining marked-global sibling
endpoint. If comparison reaches the current opposite premise, its shared
connective conclusion is concretely marked. Canonical raw-mark history would
then mark both submitted premises, including the selected ready head, which is
exactly raw-unmarked by queued-vertex accounting. The new sibling open-exit
carrier therefore has only raw-mate and future-work constructors. The target's
separate raw, future, and older marked-global branches, complete cancellation,
both endpoint junctions, the par-pair residual, the causal descent, and
ready-tail failure remain. No payer, history-tail law, completion, or progress
follows.

The preceding refinement normalizes those two open sibling exits relative to the
exact active occurrence carrier and a failed non-global ready-tail search. A
raw mate outside the carrier stays external. An internal raw mate is forced to
the current selected head, while the chain terminal is the current mate and
its consumer conclusion is the current connective conclusion. A future-work
conclusion stays outside the carrier at a boundary strictly older than the
active ready head. Every constructor retains the chain terminal outside the
carrier. The exact selected/mate raw return and the outside older future-work
endpoint remain; separate target raw, future, and older marked-global branches
also remain. This refinement produces no payer, history-tail law, completion,
or progress theorem.

The preceding refinement exposes the exact scheduler semantics of the remaining
older future-work sibling endpoint. A ready endpoint now carries its sigma
slot, ready bucket, live component lookup, frontier membership, and raw-
unmarked conclusion. A waiting endpoint carries its exact waiting cell,
submitted par producer, oriented premise marks, and strict younger-boundary
comparison. In both cases, the endpoint consumer's selected premise and mate
are concretely marked. The target adapter and typed Wait theorem transport
those fields without changing the raw-outside or exact selected/mate-return
branches. This classifies but does not eliminate the older future endpoint,
produce a distinct payer, derive the history-tail law, or prove completion or
progress.

The preceding checkpoint authenticates and strictly orders both marked premises
of that older future endpoint. The chain terminal lies outside the active
occurrence carrier and has a representative strictly below the active
boundary. Its mate is either also outside at a strictly older representative,
or active-owned at exactly the active representative. Ready work remains
ready. For waiting work with an active-owned mate, exact span orientation
forces the terminal to be the older premise and the mate to be the younger
premise whose boundary is active; the reverse orientation would create a
strict boundary cycle. This causal/ownership classification does not eliminate
the endpoint, construct a payer, derive `ActiveTopDebtTailLaw`, or prove
completion or progress.

The preceding checkpoint eliminates only the raw continuation from the exact
active-owned waiting mate back to its already concrete-marked older terminal.
The two-constructor
`ActiveMateWaitingParentExternalTemporalOutcome` is fixed to
`consumer.conclusion`: that conclusion lies outside the active occurrence
carrier and is either future work at a boundary strictly older than the active
boundary or a concrete mark whose representative is strictly older. The
surrounding active scheduler status retains that narrowed carrier together with
the exact waiting span.

The raw case would make the older terminal both concretely marked by the
waiting span and raw-unmarked through connective-opposite identity. The direct
bridge uses `CanonicalTagHistory`, `SchedulerInvariant`, active component
lookup and occurrence, the outside-conclusion premise, and the exact waiting
witness. It requires neither `DeclarativelyCorrect`, ready-tail failure, nor a
separate mate-active premise. The refinement is transported through the
scheduler status, sibling target, and typed Wait trace. Older-outside mates may
still be ready or waiting; broader selected/mate raw returns, external temporal
endpoints, the history-tail law, completion, progress, and totality remain
open.

The preceding checkpoint advances both constructors of that exact waiting
endpoint through the strict commitment and failure-conditioned re-entry
pipeline. The future or marked `consumer.conclusion` now retains its exact
`StrictOlderCommitmentSplit`. Supplied reference-switching connectedness gives
an owned-to-external `ActiveCarrierExternalEndpointCrossing`; the new `.reentry`
theorem reverses its edge-simple path and boundary edge into an exact
`ActiveCarrierExternalEndpointReentry`. Under exact ready-tail failure, the
same endpoint also retains
`ActiveCarrierExternalReentryFailureHistoricalStatus`.

The two-case result carrier stores the crossing and theorem-derived re-entry
separately; it does not identify arbitrary stored witnesses. Its inbound target
remains either the selected raw-unmarked head or a distinct concrete mark
authenticated by canonical history and represented at the active boundary.
Neither target is eliminated, and this refinement has not yet been transported
through the outer scheduler-status, sibling-target, or typed-Wait wrappers. It
derives no payer, history-tail law, completion, progress, termination, or
totality theorem.

The preceding checkpoint eliminates the selected raw-unmarked alternative from
that failure-conditioned historical re-entry status when the enclosing
selected connective is a structurally well-formed stored-right `par`. The
generic
`ActiveCarrierExternalReentryFailureHistoricalStatus.markedHistoricalTarget_of_storedRight`
theorem uses structural inbound-parent-edge separation. Beyond the supplied
failure status, it needs only structural well-formedness, the current
connective's `par` kind, and its `.storedRight` side. It requires no avoiding
path or sibling-path alignment.

The exact future/marked waiting endpoints retain their older boundary or
representative, externality, `StrictOlderCommitmentSplit`, owned-to-external
crossing, and reverse re-entry. Only the nested failure status is replaced by
`ActiveCarrierExternalReentryMarkedHistoricalTarget`; crossing and re-entry
witnesses remain existentially separate. The refinement is transported
through the active future-work mate status, continuation sibling target, and
typed Wait older-mate trace. Older-outside, raw-outside, selected-return,
future/marked sibling exits, avoiding/equal-final trace branches, and the
causal-descent/cyclic-junction receipts remain unchanged. The surviving target
is a distinct canonical-history-authenticated mark at the active
representative. It is neither eliminated nor converted into a payer, and no
history-tail law, completion, progress, termination, or totality theorem
follows.

The preceding checkpoint normalizes each surviving marked re-entry from its
actual waiting endpoint, instantiated as `consumer.conclusion` rather than the
enclosing `current.mate`. Active-frontier ownership places the inbound target
in the active owned carrier, while the enclosing `current.mate ∉ owned` receipt
separates the two vertices. Structural parent uniqueness identifies the
target's submitted consumer, aligns the inbound source with that consumer's
conclusion, retains that conclusion outside the carrier, and keeps the target
consumer's mate distinct from the selected head. The concrete target remains
authenticated by canonical history and represented at the active boundary.

Under the retained exact ready-tail-failure premise, continuation credit has
three forms. The target consumer's mate is raw-unmarked outside the active
carrier; its conclusion is future work at a boundary strictly below the active
age; or that conclusion is marked at a representative strictly below the
active age. The no-tail premise is consumed only in the raw-mate case: an
active-owned unmarked mate would be the selected head or occur in the ready
tail, and the non-global tail alternative contradicts no-tail. It does not
eliminate the resulting raw-outside, future, or marked temporal alternatives.

Constructor-preserving maps carry this endpoint-parametric status through both
exact future/marked waiting endpoints, the active future-work mate,
continuation sibling target, and typed Wait older-mate trace. All unrelated
raw/future/marked exits, avoiding/equal-final trace branches, and
causal-descent/cyclic-junction receipts remain unchanged. The marked target is
not eliminated, arbitrary crossing and re-entry witnesses are not aligned, and
no payer, history-tail law, completion, progress, termination, or totality
theorem follows.

The preceding checkpoint combines carrier-forest marked ownership with exact
live-carrier disjointness at that same waiting endpoint. A nonreflexive
continuation step first marks the unique target-parent conclusion, already
known to lie outside the active owned carrier. If its owner is active, owned
uniqueness directly contradicts that outside receipt. If its owner is
distinct, connective closure puts the active frontier origin in both live
carriers, contradicting disjointness. The finite continuation chain is
therefore reflexive.

Consumer and parent uniqueness then eliminate the exact selected/current-mate
raw return. The marked-global endpoint contradicts the same outside-parent
argument. An older ready future endpoint would own the active origin in both
its exact ready component and the active component, so live-carrier
disjointness eliminates it as well. Exactly two cases remain: the original
target consumer's mate is raw-unmarked outside the active carrier, or that
consumer's conclusion is future work at an exact waiting cell whose boundary
is strictly below the active raw age. The waiting case retains its initialized
payload, submitted par lookup, singleton source-index entry, unmarked
conclusion, oriented marked premises, both sigma-boundary equations, and strict
boundary order. Neither survivor is eliminated or converted into a payer, and
the theorem derives no avoiding witness, aligned re-entry path, history-tail
law, progress, completion, termination, or totality result.

The preceding [outer-obstruction checkpoint][wait-outer-obstruction] retains
the exact inner waiting-branch path while exposing the remaining outer
obstruction. Given the submitted consumer, declarative correctness and the
exact older waiting location produce one common path from the older consumer
mate to the active target. The path keeps its exact target finish, inner
waiting-conclusion avoidance, and outside-to-inside directed edge before any
branch split. With
canonical tag history, a selected outer par, and exact ready-tail failure, the
theorem then splits on the outer selected-parent conclusion.

If the common path avoids that outer conclusion, the theorem separately
derives an existential marked historical target for an inbound carrier edge.
The classifier is obtained from the same evidence, but its interface does not
expose identity between its internal path or edge and the retained common
witnesses. Otherwise the result states only that the outer conclusion belongs
to `path.vertices`; it gives no occurrence localization or first-visit fact.
Here "historical target" names the classifier's internal inbound-edge target;
the public result exposes no equality identifying that vertex with the retained
common path endpoint, the older mate, or either conclusion. Neither branch
eliminates or payer-converts the waiting target, the raw survivor remains, and
no history-tail law, progress, completion, termination, or totality follows.

The preceding [outer-containing-status checkpoint][wait-contains] strengthens
that split without adding hypotheses. Two reusable ready-head theorems show
that the conclusion of any connective consuming the selected head is not
`Produced`, and that exact occurrence accounting keeps it outside any supplied
owned carrier. The main theorem returns both facts for `current.conclusion`
unconditionally while preserving the common exact mate-to-target path,
outside-to-inside edge, inner waiting-conclusion avoidance, and left avoiding
classifier.

In the containing branch, outer-conclusion membership is retained and a
separate `ActiveCarrierExternalReentryFailureHistoricalStatus` is derived from
that conclusion via a suffix and an outside-to-inside boundary not claimed to
be first. Its internal path and edge are not identified with the common path
or crossing. The classified target is the selected raw head or a distinct
authentic marked target at the active representative. No occurrence position
or first visit is exposed. Neither branch is eliminated or payer-converted,
the raw survivor is unchanged, and no history-tail law, progress, completion,
termination, or totality follows.

The [preceding stored-right checkpoint][wait-right] adds the explicit
`current.side = .storedRight` refinement. It removes only the selected-head
alternative from the containing branch's independent failure-conditioned
status. The avoiding branch retains a marked historical re-entry classifier at
`consumer.mate`; the containing branch retains
`current.conclusion ∈ path.vertices` and now carries a marked historical
re-entry classifier at `current.conclusion`. The common exact path, crossing
edge, inner avoidance, outer membership split, and freshness facts are
unchanged.

The two classifier witnesses remain existentially independent of the common
path and crossing and of each other. The theorem exposes no occurrence
position, first visit, or boundary identity. It eliminates neither marked
target, does not payer-convert either branch, leaves the raw survivor unchanged,
and proves no history-tail law, progress, completion, termination, or totality.

The preceding checkpoint adds [future-work queue status][future-queue]. Under
`SchedulerInvariant`, flattened `queuedVertices` membership is equivalent to a
proof-relevant `FutureWorkAt` witness at some boundary. Given active component
lookup and an occurrence witness for a supplied `owned` list, future work
outside that list lies strictly below the active raw boundary and retains an
exact ready or initialized-waiting scheduler location.

`UnmarkedOutsideActiveSchedulerStatus` therefore records that an in-bounds
raw-unmarked vertex outside the supplied list is either currently absent from
the queue, live frontier, and `Produced`, or has exact future work at some
strictly older boundary. The low-level status is a current-state classifier
only: it proves no unique or first boundary, historical queue origin,
persistence, reachability, dispatchability, payer, history-tail law, progress,
completion, termination, or totality.

The preceding [outer queue-status checkpoint][wait-outer-queue] lifts that status
through the exact waiting-parent target and both branches of the stored-right
outer split. The new queue-status target preserves the marked-parent path,
inbound edge, authentic mark, representative, and target consumer. It replaces
only the raw-unmarked `targetConsumer.mate` leaf with
`UnmarkedOutsideActiveSchedulerStatus`; the exact initialized-waiting
`targetConsumer.conclusion` alternative is unchanged. The adapter uses the
existing scheduler invariant, component lookup, and occurrence witness.

The final theorem starts from the stored-right outer result and adds only
`currentMateOutside : current.mate ∉ owned`. Its output remains a disjunction:
the avoiding branch carries its queue-status target at `consumer.mate`, while
the containing branch retains `current.conclusion ∈ path.vertices` and carries
its target at `current.conclusion`. It does not export both classifiers
simultaneously. The common path, crossing, inner avoidance, ownership, and
freshness facts are preserved, while each target's internal witnesses remain
independent of that path, crossing, and the other branch.

Only the replaced raw leaf is current-state; the surrounding target retains
its canonical history evidence. A future-work boundary inside that leaf is
existential and not proved first, unique, or canonical. No queue origin,
persistence, reachability, dispatchability, elimination, payer, history-tail
law, progress, completion, termination, or totality follows.

The preceding [waiting commitment re-entry queue-status outcome][wait-endpoint-queue]
transports that target through both constructors of the exact waiting-parent
endpoint. Its `olderFuture` branch preserves the boundary, work, strict age,
outside-carrier fact, commitment split, crossing, and re-entry receipts. Its
`olderMarked` branch preserves the conclusion age, mark, strict representative
age, outside-carrier fact, commitment split, crossing, and re-entry receipts.
Only the endpoint outcome carrier's nested target field changes.

Beyond the supplied temporal outcome, the adapter's proof premises are exactly
the scheduler invariant, active component lookup, component occurrence witness,
and no-tail premise. It maps the temporal target through its continuation exit,
exact waiting parent, and queue status; it adds no current-mate-outside,
correctness, par-kind, connectivity, or stored-side premise. The endpoint
remains `consumer.conclusion`. The endpoint outcome's crossing and re-entry
witnesses are not identified with the nested target's internal path, and an
endpoint older-future boundary is not identified with the nested queue leaf's
future-work boundary. Only the final raw-unmarked leaf is current-state; the
exact initialized-waiting leaf is unchanged. No queue origin,
persistence, reachability, dispatchability, elimination, payer, tail law,
progress, completion, termination, or totality follows.

The preceding [future-work mate queue-status checkpoint][wait-mate-queue] lifts
that endpoint outcome through the two-case future-work mate temporal status.
Its `olderOutside` branch preserves `notMembership` and
`representativeOlder` verbatim. Its `activeExternal` branch preserves
`membership`, `representative`, and the exact `waiting` witness, changing only
the `external` endpoint through `queueStatusOutcome`.

Beyond the supplied temporal status, the adapter's premises are exactly the
scheduler invariant, active component lookup, component occurrence witness,
and no-tail premise. It adds no correctness, current-mate-outside,
connectedness, par-kind, stored-side, or geometric premise. It introduces no
equality among the status boundary, endpoint older-future boundary, and nested
future-work boundary, and does not align the endpoint crossing or re-entry
receipts with the nested target path. The older-outside branch is neither
queue-classified nor eliminated. The continuation and sibling maps are recorded
below; typed-Wait transport remains open.

The preceding [continuation queue-status checkpoint][wait-cont-queue] lifts that
future-work mate status through the exact three-case continuation outcome. It
copies `rawOutside` and `rawSelectedReturn` with their chains, endpoints,
mate-unmarked lookups, outside evidence, selected return, and current-
connective equalities unchanged. In `futureOlder`, it preserves the chain,
endpoint, shared boundary,
future work, marks, canonical events, representative order, unresolved event-
order disjunction, and exact scheduler location. Only `mateStatus` is mapped
through `queueStatus`.

Beyond the supplied continuation outcome, the adapter's premises are exactly
the scheduler invariant, active component lookup, component occurrence
witness, and no-tail premise. It adds no `current.mate ∉ owned` premise;
`rawOutside.mateOutside` remains an existing payload about `consumer.mate`.
The continuation boundary is already shared by its work, mate status, and
location. The map introduces no equality with an endpoint older-future or
nested queue boundary and aligns no endpoint receipt with the nested target
path. Neither raw exit is queue-classified or eliminated, and the event-order
disjunction remains unresolved. At that checkpoint, sibling and typed-Wait
transport remained open; the sibling map is recorded next.

The current [continuation sibling queue-status checkpoint][wait-sibling-queue]
lifts that continuation outcome through the exact waiting sibling-exit target.
It preserves the outer mate mark, switching path, directed-edge membership,
inbound-parent evidence, marked target event, representative equality, target
consumer, directed source, and outside conclusion. The raw, older-future, and
older-marked sibling exits are copied verbatim. In the causal branch, the first
descent, consumer, mate event and order, and cyclic-junction causal outcome stay
unchanged; only the nested continuation outcome is mapped through
`queueStatusOutcome`.

Beyond the supplied sibling target, the adapter's premises are exactly the
scheduler invariant, active component lookup, component occurrence witness,
and no-tail premise. It adds no current-mate-outside or geometric hypothesis,
aligns no switching, continuation, crossing, re-entry, cyclic-junction, or
nested-target path, and introduces no boundary equality. The three noncausal
exits remain queue-unclassified and uneliminated. Typed-Wait transport remains
open, as do queue origin, queue history, persistence, reachability, payer
recovery, a tail law, progress, completion, termination, and totality.

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
[marked re-entry target raw-return first descent][target-first-descent],
[canonical raw-mark causal order](api-reference.md#canonical-raw-mark-causal-order),
[marked re-entry target raw-return causal descent][target-causal],
[marked re-entry target raw-return terminal causal order][target-terminal-causal],
[marked re-entry target sibling-exit causal order][target-sibling-causal],
[marked re-entry target sibling-exit causal/cyclic junction][target-junction],
[marked re-entry target cyclic-junction endpoint causal order][target-endpoint],
[marked re-entry target complete-cancellation causal endpoints][target-complete],
[marked re-entry target sibling-exit forward causal order][target-forward-causal],
[marked re-entry target sibling open exits][target-open],
[marked re-entry target sibling temporal exits][target-temporal-open],
[exact future-work scheduler locations][future-location],
[future-work queue status][future-queue],
[marked re-entry target sibling scheduled exits][target-scheduled],
[marked re-entry target sibling causal ownership][target-causal-ownership],
[marked re-entry target active-mate ready elimination][target-ready-mate],
[marked re-entry target active-mate waiting parent recursion][target-wait-parent],
[marked re-entry target active-mate waiting external temporal outcome][wait-ext],
[active-mate waiting external commitment re-entry failure][wait-ext-reentry],
[stored-right waiting commitment re-entry marked target][wait-ext-marked],
[waiting commitment re-entry marked-target temporal normalization][wait-temporal],
[waiting commitment re-entry marked-target finite continuation exit][wait-cont],
[waiting commitment re-entry marked-target continuation waiting][wait-cont-waiting],
[waiting re-entry continuation producer orientation][wait-producer-orientation],
[waiting re-entry continuation mate avoidance][wait-mate-avoidance],
[waiting re-entry continuation outer obstruction][wait-outer-obstruction],
[waiting re-entry continuation outer-containing historical status][wait-contains],
[waiting re-entry continuation stored-right marked outer split][wait-right],
[waiting re-entry continuation outer queue status][wait-outer-queue],
[waiting commitment re-entry queue-status outcome][wait-endpoint-queue],
[future-work mate external re-entry queue status][wait-mate-queue],
[continuation external re-entry queue status][wait-cont-queue],
[continuation sibling external re-entry queue status][wait-sibling-queue],
[marked re-entry target raw-return cyclic reduction][target-cycle],
[branch-local continuation credit](api-reference.md#branch-local-continuation-credit),
[continuation-credit preservation](api-reference.md#continuation-credit-preservation),
[endpoint-localized continuation exits](api-reference.md#endpoint-localized-continuation-exits),
and the retained
[Wait endpoint-locality obstruction](api-reference.md#wait-endpoint-locality-obstruction).
The first open proof step is now to transport the sibling queue-status target
through the typed-Wait wrapper. The sibling adapter already preserves the outer
age, event, switching path, inbound edge, target mark, representative,
consumer, separation, and outside receipts. It copies the raw, older-future,
and older-marked sibling exits and maps only the causal alternative's nested
continuation outcome. The typed-Wait lift must copy the `avoiding`,
`equalSelected`, and `equalMate` trace constructors verbatim. In `olderMate`,
every trace field, mate-outside receipt, mate mark, and representative order
must remain unchanged; only the final sibling target may be mapped. No
switching, continuation, crossing, re-entry, cyclic-junction, or trace path may
be aligned, and no endpoint or nested queue boundary equality may be introduced.

The currently absent and exact older-work leaves still require elimination or
payer conversion, as does the exact initialized-waiting conclusion alternative.
The avoiding endpoint remains `consumer.mate`; the containing endpoint remains
`current.conclusion`, whose common-path membership is retained only by the
outer theorem. The causal/cyclic receipts remain preserved rather than
discharging either target.
Broader selected/mate raw returns, other external temporal alternatives, and
Wait first-descent branches remain open. The surviving marked omitted-right
source must likewise be eliminated or converted into a distinct payer. Both
equal-final trace orientations, older-outside waiting, and external-raw
outcomes also remain unresolved.
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
- elimination of
  `ActiveMateWaitingParentExternalTemporalOutcome` or the broader
  `ActiveCarrierParentExternalTemporalOutcome`; the exact waiting-mate
  future/marked endpoints now retain crossing, reverse re-entry, and an exact
  endpoint-parametric temporal-parent split under the stored-right/no-tail
  refinement; their marked re-entry target also admits finite-chain
  normalization, but the broader carriers remain and no generic raw/waiting
  endpoint supplies a distinct ready-tail payer;
- complete elimination of all temporal-parent or finite-continuation
  alternatives:
  no-tail proves that the immediate raw parent mate is outside the active
  carrier; carrier ownership and live-component disjointness eliminate every
  nonreflexive chain, the exact selected/current-mate return, older ready work,
  and marked-global work, while the raw-outside mate and exact older waiting
  conclusion remain unresolved; the latter's producer is oriented exactly and
  yields an inner-conclusion-avoiding older-mate-to-target path. That path now
  splits at the outer selected conclusion into a branch-local queue-status
  waiting-parent target at `consumer.mate`, or outer-conclusion membership and
  the same target shape at `current.conclusion`. Each target retains its
  independently witnessed marked parent. The preceding endpoint adapter carries
  that target through the exact continuation-exit and waiting-parent maps in
  both the older-future and older-marked endpoint constructors, preserving all
  other endpoint payloads. Only the final raw mate leaf is current-state
  queue-classified, and the exact initialized-waiting conclusion leaf is
  unchanged. The stored-right premise removes only the selected-head
  alternative from the containing branch's prior failure status. Neither outer
  branch exposes an occurrence position or first visit, and neither is
  identified with the common path, crossing, or the other branch. The endpoint
  crossing and re-entry receipts are not aligned with the nested target's path,
  and its older-future boundary is not equated with the nested queue boundary.
  The outer disjunction does not provide both targets simultaneously, and
  neither outer branch eliminates the survivor;
- elimination or payer conversion of the surviving re-entry targets: the
  independently witnessed marked classifier at each outer endpoint;
  localization and elimination of the outer-conclusion membership;
  elimination of either equal-final conclusion-to-selected or
  conclusion-to-mate trace, elimination of the finite raw-outside or exact
  older-waiting continuation alternatives, or the
  authenticated first-step descent now replacing exact raw return in Wait and
  generic contexts, or
  conversion of that target into a distinct active raw payer;
- elimination of an older future-work endpoint merely from its exact ready or
  waiting scheduler location, the concrete and canonically ordered marks on
  both submitted premises, the exact younger-target/older-mate producer
  orientation, or the older-outside/active-owned mate classification, or
  conversion of those facts into a distinct active payer;
- transport of the sibling queue-status target through the typed-Wait wrapper;
  the avoiding, equal-selected, and equal-mate trace exits must remain
  unchanged, while every older-mate trace receipt and its mate-outside, mark,
  and representative-order payload must surround the same mapped target;
- totality of any operational schedule beyond the supplied canonical history,
  elimination of the causal first descent or a raw/future sibling exit, or
  conversion of an earlier event into a distinct ready-tail payer;
- impossibility of the remaining Wait/generic exact out-and-back
  cyclic-junction traversal, elimination of either simultaneous endpoint
  junction or the surviving marked omitted-right par pair, or conversion of
  the now strictly ordered cyclic residual into a distinct ready-tail payer;
- a terminal scheduler state or complete discharge of the finite-continuation
  target;
  endpoint-parametric normalization collapses the marked chain and eliminates
  three terminal families but does not discharge its raw-outside mate or exact
  older-waiting conclusion;
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
commit    09d779c57df327a2464c3f58e9c7fdb965a3f1c9
tree      f83b9c49c78068ba5dea33a1aa929db6d8fe6427
parent    bc56d7d40137ed1e94e427b8601a459c309e88db
stage     lift sibling queue status
delta     17 paths, +416/-39
manifest  ABCF7FC05D9F2390989B4AA7DA318129CCBF6C56CABEFF13F625B0C090BDF0A5
```

The manifest hashes canonical
`path<TAB>UPPER_SHA256<TAB>blob<LF>` records for the committed delta.

The checkpoint source receipts are:

```text
sibling source    62D8CECC3552780486C14FD9EE2FF1755AA7169A71B67D9C394E44DB1B424F10
sibling consumer  B089B68E900F0278B8A843F24E84FAC8EAD4BFFFC8BC319483AEF8B1811BBCED
generated API     E07376AD2C128C5481723336C7B024E8622E15B55C2D51A849FA4FF0A31FBC03
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

Local verification of the committed checkpoint, with ignored prototype probes
included only in the broader source scan:

- full `lake build`: 709/709 jobs;
- pre-push syntax-aware Lean source audit: zero actual `sorry`/`admit`
  findings across the 352-file local non-build superset present at verification
  time, including ignored prototype probes and zero actual `sorryAx` findings;
- library inventory: 330 Lean files and 205,340 Lean source lines, including
  183 module files under `ProofNetIR/`; a parser-aware count finds 179 imported
  submodules in the public facade, or 180 modules including the facade itself;
- generated API reference: current at 106 sections and 1,835 declarations;
- the runnable sibling consumer reconstructed the public target and invoked the
  public adapter; both new declarations use the standard-three boundary, and
  the executable emitted
  `Figure-7 continuation sibling queue status: kernel-green`;
- public theorem audit: 1109 entries total: 811 standard-three, 25 axiom-free,
  132 `propext`-only, and 141 `propext`/`Quot.sound` boundaries;
- the default, extended, and cross-variant progress audits passed with every
  incomplete visited state carrying an exact ready head and successful
  dispatch and every dispatch-none stop fully marked; they covered 23,184,
  96,444, and 1,182,816 states with checksums 741,882, 5,588,478, and
  77,141,346, respectively, and all three modes had zero missing-head,
  incomplete-dispatch-none, cycle, or truncation findings;
- facade, generated API, consumer, and axiom-audit entry points passed under
  the checkpoint's trust-zero and warnings-as-errors gates.

Exact-head proof GitHub verification:

- workflow: `Lean CI`;
- event/ref: `push` / `main`;
- run: [32541660030](https://github.com/fushanbobfan/proofnet-ir/actions/runs/32541660030);
- build job: [96952712972][proof-job];
- title/attempt: `feat: lift sibling queue status` / 1;
- exact head: `09d779c57df327a2464c3f58e9c7fdb965a3f1c9`;
- result: 36 successful steps, zero failures, and one expected release-ref-only
  skip;
- run: `2026-08-22T00:51:19Z`-`2026-08-22T01:02:42Z` (11m23s);
- build job: `2026-08-22T00:51:21Z`-`2026-08-22T01:02:41Z`
  (11m20s).

[proof-job]: https://github.com/fushanbobfan/proofnet-ir/actions/runs/32541660030/job/96952712972
[reentry-failure]: api-reference.md#commitment-interval-par-guard-re-entry-failure-target
[reentry-mate-separation]: api-reference.md#commitment-interval-par-guard-re-entry-mate-separation
[target-temporal]: api-reference.md#commitment-interval-marked-re-entry-target-temporal-reduction
[target-exit]: api-reference.md#marked-re-entry-target-finite-continuation-exit
[target-nop-no-return]: api-reference.md#marked-re-entry-target-nop-raw-return-elimination
[target-first-descent]: api-reference.md#marked-re-entry-target-raw-return-first-descent
[target-causal]: api-reference.md#marked-re-entry-target-raw-return-causal-descent
[target-terminal-causal]: api-reference.md#marked-re-entry-target-raw-return-terminal-causal-order
[target-sibling-causal]: api-reference.md#marked-re-entry-target-sibling-exit-causal-order
[target-junction]: api-reference.md#marked-re-entry-target-sibling-exit-causalcyclic-junction
[target-endpoint]: api-reference.md#marked-re-entry-target-cyclic-junction-endpoint-causal-order
[target-complete]: api-reference.md#marked-re-entry-target-complete-cancellation-causal-endpoints
[target-forward-causal]: api-reference.md#marked-re-entry-target-sibling-exit-forward-causal-order
[target-open]: api-reference.md#marked-re-entry-target-sibling-open-exits
[target-temporal-open]: api-reference.md#marked-re-entry-target-sibling-temporal-exits
[future-location]: api-reference.md#exact-future-work-scheduler-locations
[future-queue]: api-reference.md#future-work-queue-status
[target-scheduled]: api-reference.md#marked-re-entry-target-sibling-scheduled-exits
[target-causal-ownership]: api-reference.md#marked-re-entry-target-sibling-causal-ownership
[target-ready-mate]: api-reference.md#marked-re-entry-target-active-mate-ready-elimination
[target-wait-parent]: api-reference.md#marked-re-entry-target-active-mate-waiting-parent-recursion
[wait-ext]: api-reference.md#marked-re-entry-target-active-mate-waiting-external-temporal-outcome
[wait-ext-reentry]: api-reference.md#active-mate-waiting-external-commitment-re-entry-failure
[wait-ext-marked]: api-reference.md#stored-right-waiting-commitment-re-entry-marked-target
[wait-temporal]: api-reference.md#waiting-commitment-re-entry-marked-target-temporal-normalization
[wait-cont]: api-reference.md#waiting-commitment-re-entry-marked-target-finite-continuation-exit
[wait-cont-waiting]: api-reference.md#waiting-commitment-re-entry-marked-target-continuation-waiting
[wait-producer-orientation]: api-reference.md#waiting-re-entry-continuation-producer-orientation
[wait-mate-avoidance]: api-reference.md#waiting-re-entry-continuation-mate-avoidance
[wait-outer-obstruction]: api-reference.md#waiting-re-entry-continuation-outer-obstruction
[wait-contains]: api-reference.md#waiting-re-entry-continuation-outer-containing-historical-status
[wait-right]: api-reference.md#waiting-re-entry-continuation-stored-right-marked-outer-split
[wait-outer-queue]: api-reference.md#waiting-re-entry-continuation-outer-queue-status
[wait-endpoint-queue]: api-reference.md#waiting-commitment-re-entry-queue-status-outcome
[wait-mate-queue]: api-reference.md#future-work-mate-external-re-entry-queue-status
[wait-cont-queue]: api-reference.md#continuation-external-re-entry-queue-status
[wait-sibling-queue]: api-reference.md#continuation-sibling-external-re-entry-queue-status
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

1. transport the sibling queue-status target through the typed-Wait trace. The
   next wrapper must copy `avoiding`, `equalSelected`, and `equalMate` verbatim.
   In `olderMate`, it must preserve every interval and trace receipt together
   with the mate-outside receipt, mate mark, and strict representative order;
   only the final sibling target may change through `queueStatusTarget`. It
   consumes an already-successful typed Wait and must not add an applicability
   premise. No switching, continuation, crossing, re-entry, cyclic-junction,
   or trace witnesses may be aligned, and no shared continuation, endpoint
   older-future, or nested queue boundary equality may be introduced.
   Then eliminate or payer-convert the current-absence and exact older-work
   leaves, the exact older waiting conclusion, and the surviving authenticated
   active-representative marked target. Occurrence localization, elimination,
   and payer conversion remain open. Use the separately proved simultaneous
   endpoint junctions, strict source-before-base order, aligned sibling-exit
   causal witness, retained commitment paths, and refined scheduler/ownership
   classification as applicable. Eliminate the remaining older-outside
   ready/waiting endpoint or broader selected/mate raw return, or recover a
   distinct ready-tail payer; discharge the par-pair residual and the mate-
   separated target's remaining finite alternatives; eliminate that target or
   descend its mark to a distinct active payer; and eliminate the equal-final
   conclusion-to-selected/mate trace obstructions over the retained commitment
   interval; resolve the waiting/raw outcome alternatives; then derive the
   remaining global-created Forward/UnifyPayload alternatives; equivalently,
   prove that correctness plus `CanonicalTagHistory` implies
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
