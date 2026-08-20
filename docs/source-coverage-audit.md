# Local source coverage audit

Audit date: 2026-07-22; live PDF/chat inventory and hashes refreshed 2026-08-06

## Review question

Which claims in the local corpus are required to justify ProofNet-IR's MLL
semantics, correctness criterion, sequentialization boundary, library design,
and empirical hypothesis, and what has actually been read closely enough to
support those claims?

## Inventory and screening

The workspace currently contains 16 PDFs. Seven UCLA `131BH`
homework/submission PDFs are coursework artifacts and are not project
literature. `paper1_中文讲解.pdf` is a derived guide to `paper1.pdf`, not an
independent source. The original project corpus is therefore seven PDFs plus
the complete short Rowling chat brief; the later Guerrini primary-source audit
is the sixteenth PDF and is tracked separately below.

```text
PDFs inventoried                                      16
Coursework PDFs excluded                              7
Derived duplicate-format guide merged                 1
Original project sources included                     7
Supplemental primary source included                   1
Physical pages in included PDFs                     948
Exact repeated pages in linearlogic.pdf             168
Approximate unique physical pages                   780
```

All seven PDFs have extractable text. One page in the Manin scan has no
extractable text and requires visual/OCR treatment.

## Honest coverage matrix

| Source | Pages | Current evidence | Status |
|---|---:|---|---|
| Pfenning, *Linear Logic* | 336 physical; 168 unique after exact repetition | complete ordered text reading and rendered-image inspection of all 168 unique pages in a [page matrix](source-pages/pfenning-linear-logic.md) | complete |
| Manin, *A Course in Mathematical Logic for Mathematicians* | 389 | complete ordered text reading in a [page matrix](source-pages/manin-mathematical-logic.md), including visual inspection of the extraction-empty cover, Kochen-Specker graphs on pages 99-100, and graph-language pages 307-313; the final interval was also checked for substantive embedded images | complete |
| *Proof Nets as Graphical Proof Objects* | 20 | complete end-to-end reading and selected-page visual verification | complete |
| *ProofNet-IR Research Plan* | 19 | complete end-to-end reading and selected-page visual verification | complete, but treated as a generated design input rather than authority |
| Marcolli, Berwick, Chomsky, *Syntax-Semantics Interface* | 75 | complete ordered text reading and rendered inspection of all 19 numbered figures and three algebraic tables in a [page matrix](source-pages/marcolli-syntax-semantics.md) | complete |
| *Geometry of Neuroscience* | 33 | complete ordered text reading and visual inspection of all 33 pages and Figures 1--10; [page matrix and claim boundary](source-pages/geometry-of-neuroscience.md) | complete, but adjacent generated exposition rather than core authority |
| Park, *Open Book Decompositions with Page a Four-Punctured Sphere* | 76 | complete ordered text reading and rendered inspection of pages 1--74, covering every mathematical diagram, code listing, and data table; [page matrix and claim boundary](source-pages/park-four-punctured-sphere.md) | complete |
| `Rowling_s chat history.txt` | short text | read completely | complete |
| Guerrini, *A linear algorithm for MLL proof net correctness and sequentialization* (TCS 2011) | not locally held | official metadata and abstract checked; full text inaccessible and unread | metadata-only follow-up, excluded from PDF/page/hash counts |

Consequently, all seven original project PDFs and the complete Rowling chat
have now been read in full under the recorded protocol. This is a corpus
coverage result, not a mathematical endorsement of every source or a claim
that every source supports ProofNet-IR: Park and the generated adjacent
expositions contain no theorem that strengthens the core MLL results.

## Reading protocol used for completion

For each source:

1. record every chapter/section and physical-page interval;
2. read extracted text page by page, recording definitions, theorem statements,
   hypotheses, proof dependencies, counterexamples, and project consequences;
3. render and visually inspect every page containing proof nets, inference
   rules, commutative diagrams, graphs, tables, or extraction anomalies;
4. distinguish source theorems from project inferences;
5. record a completion line only when every unique page has been accounted for;
6. recheck every code-level mathematical claim against the resulting matrix.

The linked page matrices are the evidence behind the completion claim. A live
2026-08-06 PDF/chat rescan again found the same 16 PDFs, with no new, removed,
or changed research source. Its SHA-256 refresh matched every original-source
prefix recorded in `reading-ledger.md` and the full Guerrini digest below; the
Rowling chat matched the full digest recorded there. The broader 2026-07-28
bounded scan classified all 39 Markdown candidates as ten
ledger/map/page-matrix/Guerrini-audit artifacts and 29 project
design/release/architecture documents, not new external papers or books. The
DOCX/HTML Chinese guide remains a duplicate-format derivative, temporary text
files remain extractions, and the Rowling brief was unchanged in the current
rescan. This ledger does
not turn adjacent sources into proof-net authorities and does not replace
kernel checking of the implementation.

## Supplemental primary-source audit

On 2026-07-23 the project added Stefano Guerrini's ten-page LICS 1999 paper
*Correctness of Multiplicative Proof Nets is Linear* as external primary
literature for the contraction/unification implementation. It is not counted
among the seven original user-provided PDFs above. The complete extracted text
and all eight figures were inspected. The local audit copy's SHA-256 is
`47c2b9fe82c73db3bcbb5c0dab183cb2130c9c446a1ae0f9c72fe59e53cbb149`.

The audit confirms the exact axiom/start, unary-par/forward, and
binary-tensor/unify rules, the waiting-par/deadlocked-tensor distinction, the
total-marking/single-thread acceptance condition, and the extra worklist,
`NEXTAXIOM`, and special union-find structure needed for the paper's linear
theorem. The code-level mapping and nonclaims are recorded in
[guerrini-unification-audit.md](guerrini-unification-audit.md).

The same audit records an internal Figure-7 indexing conflict: the 1999 prose
defines `W` on inactive `σ` boundaries and `unify` reads the old predecessor,
whereas the printed `new` writes the fresh active top. The literal transition
is retained only for source comparison. Production code uses a documented
project interpretation that initializes the old active boundary and leaves the
fresh top undefined, with kernel-checked `OperationalWaitingDomain`
preservation. This is not presented as an author-confirmed erratum.
The invariant does not by itself establish payload ownership or reachability.
The exact empty/init/operational-new execution history separately proves tag
provenance, global submitted-slot non-reuse, and reservation-count alignment
for that fragment. Exact local `concl`/`nop`/`wait`/`forward` are now
executable with
proof-carrying canonical consumer/conclusion views; local `wait` resolves the
mate raw age through `sigmaBoundary?` and prepends only to an initialized
cell. Forward now also has an independent Boolean-free direct rule and exact
executable correspondence; its `Nodup` condition is explicitly a fail-closed
list shape rather than the paper's non-strict raw-age guard. Conditional
state-only queue ownership is preserved under the supplied invariant. The
arbitrary-payload atomic `UnifyPayload` transition now also preserves the full
occurrence-exact state-only invariant on every successful step: the input
invariant yields pre-activation freshness/provenance, each stored par activation
establishes exact ownership, and the final forest covers the payload. A
separate input-only predicate proves conditional applicability under the full
invariant, but not invariant-alone enabledness or unconditional reachability.
A canonical priority dispatcher and proof-carrying certified history now
integrate every implemented successful rule family and prove exact canonical
reservation-event counting against final `nextAge`. Structural route
reconstruction now recovers the exact proof-relevant
source-left run and terminal-partner exclusion. Canonical reservation counting
derives strict fresh capacity for that exact run; an exact axiom-endpoint
queue-history theorem derives both post-pop endpoint absences without claiming
that arbitrary queued connective conclusions are tagged. Hence canonical and
certified histories prove `NewEnabled ↔ NewInputNecessary` while retaining the
exact route as an explicit premise. The implementation now classifies every
structurally well-formed in-bounds source-left search as either a
formula-budget exact run or a nonempty tag/raw-mark blocker on a visited
stored-left occurrence or the terminal axiom partner. Source shape,
singletonhood, and fuel are discharged structurally; queue separation and
fresh capacity remain post-run. Canonical history plus the complete invariant
now classifies each exact blocker further: a tag failure is a prior exact
history touch, while a raw-mark failure is either the current selected-head
update or an old raw-marked occurrence with occurrence-exact ownership in a
live component. The three alternatives may overlap. An explicit universal
no-obstruction premise yields the exact run and the established
`NewInputNecessary`/`NewEnabled` bridges, but deriving that premise from
correctness and certified history is still open. The exact historical-event
touch subcase is excluded when its current representative equals the active
head representative, and the active-region order layer below classifies every
remaining touch as strictly older. Global older-event separation and old
marked-owner blockers remain. Authentic reservation-event touch is now exactly
equivalent to membership in that event's complete structural source-left
region under structural well-formedness. This reverse direction reconstructs
only the successful run stored by the event and supplies no new current-owner,
representative-order, created-region, or progress fact. This checkpoint is an
implementation consequence of the already-audited source semantics and does
not record a new literature reading. The resulting event-touch predicate is
now proved equivalent to the older-region separation invariant under the same
structural assumption, with identical ledger/candidate/current-representative
quantification. That is a proof-interface normalization, not a new paper claim
or a proof that the invariant is globally available. The active-region order
layer now derives a further code consequence: an authentic event touch in the
active mate region must be strictly older in representative and raw-age order,
and a supplied older-event separation invariant therefore makes the complete
region tag-fresh. It does not add a literature reading or provide the route,
readiness, queue/capacity, or global-invariant witnesses still needed for
enabledness. A further kernel-checked code consequence decomposes a historical
touch of any future tensor conclusion into a mate touch or queued-head touch;
for the active candidate the conditional tag-freshness theorem eliminates the
mate branch. This is not a new literature reading, does not prove the
conclusion untouched, and leaves the head-touch/raw-mark obstruction open. The
occurrence-carrier source-left closure is now another kernel-checked code
consequence: if a source occurrence belongs to an `OccurrenceDerivation` owned
list, the complete stored-left region, including the terminal axiom partner,
stays in that carrier. It is not a new literature result and supplies no
scheduler component, chronology, reachability, or progress claim. The
strictly older queued-head residue is now packaged as
`OlderEventFutureWorkTouchSeparated`. Together with the separate mate-region
law and structural well-formedness it yields strict candidate-conclusion
non-touch. Empty, structurally well-formed init, and Prepared/concl/nop
preservation are proved. This is another kernel-checked code
consequence, not a new literature reading or evidence that canonical histories
satisfy the new invariant. The successful typed New case is now a further
kernel-checked code consequence: retained candidates transport, old-event
touch of a created endpoint contradicts canonical history disjointness, and
the fresh event cannot be strictly older. It requires the supplied prior
invariant and is not evidence of global availability. The successful typed
Wait case is conditionally preserved under the candidate-indexed
`WaitCreatedHeadTouchSeparated` premise. Retained candidates transport and the
inserted conclusion is exactly the residual old-event/head obligation. This is
also a code consequence rather than a literature result, and it does not derive
the residual from scheduler invariants, history, or reachability. A further
kernel-checked code consequence now derives that Wait residual structurally:
the exact submitted par sends a hypothetical touched event endpoint through
its stored-left premise into the selected or already-marked mate carrier, and
strict live-slot disjointness contradicts chronological endpoint ownership.
The direct Wait corollary still consumes the supplied prior invariant and does
not close the source-region/raw seam or equal-boundary callback. The successful
typed Forward case first has a conditional preservation theorem under the
candidate-indexed `ForwardCreatedHeadTouchSeparated` residual. A further
kernel-checked code consequence now derives that residual structurally: exact
ledger endpoint accounting and occurrence-carrier closure place a hypothetical
touched endpoint in two distinct live component carriers, contradicting forest
disjointness. The direct Forward corollary still consumes the supplied prior
invariant and does not close the source-region/raw seam or equal-boundary
callback. The successful typed UnifyPayload case first has a conditional
preservation theorem under the candidate-indexed
`UnifyPayloadCreatedHeadTouchSeparated` residual. Survivor and moved candidates
transport through the prior invariant after strict output order excludes the
retired active class; the inserted conclusion is the sole residual case. A
further kernel-checked code consequence now derives that residual structurally:
tensor-output source-left closure and chronological endpoint accounting place
a hypothetical touched endpoint in distinct live carriers, contradicting
forest disjointness. The direct UnifyPayload corollary still consumes the
supplied prior invariant and does not close the source-region/raw seam or
equal-boundary callback. A downstream kernel-checked code consequence now
inducts over every supplied canonical history and derives the queued-head
invariant from structural well-formedness. This closes queued-head global
availability without a new literature claim. It does not derive the distinct
mate-region or raw-mark invariants, construct a history, give unconditional
stored-left equal-boundary avoidance, or prove enabledness or progress. A
further
kernel-checked code consequence now connects the two supplied separation
invariants to retained commitment geometry. Under the complete scheduler
invariant, the child-event untouched callback follows automatically for an
adjacent edge whose child boundary is strictly older than a future candidate;
strict sigma ordering extends this to a positive interval from only strict
oldness of its final boundary. This is not a new literature result and does not
derive mate-region or raw-mark invariant availability, give unconditional
stored-left equal-boundary avoidance, recover queue origin, close a raw seam,
or prove progress. Another kernel-checked code consequence locates any
strictly older authentic ledger event and future-New
candidate in retained `sigma`, returning the candidate's immediate predecessor
and the possibly empty prefix ending there. Positive prefixes use the existing
strict interval result. A further kernel-checked code consequence classifies
the final edge: storedRight yields target avoidance, while the inclusive
general result returns that path or an exact same-age storedLeft
conclusion-to-head touch witness. That witness records callback failure, not
proof that no avoiding path exists. These are code consequences, not new
literature results. The split itself is an index/representative consequence,
not a global separation theorem. Under declarative correctness and the complete
scheduler invariant, for a supplied canonical history, active `NewGuard`,
ledger membership, and an event representative strictly below the active head,
the blocker-advance layer gives another three-way code consequence: exact
avoiding path, strictly higher-current-representative mate-touch event below the
active head, or exact equal stored-left callback failure. This inclusive
reduction does not make representative order into chronology, maximalize or
eliminate the advance, deny a path in its final branch, close any created-
candidate raw seam, or prove progress. A subsequent kernel-checked maximality
consequence filters the finite authentic mate-touch blockers by their current
representatives. At a maximum, another advance is impossible; an avoiding path
for that blocker would splice with the audited historical and component routes
to form the tensor bypass forbidden by reference-switching acyclicity. Thus the
current inclusive reduction is an exact avoiding path or the exact equal stored-
left callback failure. This is a code consequence, not a new literature result;
the callback branch by itself still does not deny path existence. A subsequent
code theorem supplies the missing local context through
`ActiveMateEventAnchor`: if the strictly older event also has an exact active-
mate-to-event-left path avoiding the active conclusion, both maximality branches
contradict exact reference-tree edge uniqueness. Any authentic event touch in
the active mate source-left region constructs this anchor, so every ledger event
is locally touch-separated from that region. This is derived Lean geometry, not
a newly read literature theorem, and it does not claim callback impossibility
without the anchor or global invariant preservation. The availability-reduction
layer consumes the existing structural search and code invariants: it proves
`NewSourceRegionInput` or an exact old marked owner, then `NewEnabled` or that
owner. The raw-mark separation layer separately turns owner exclusion into a
state invariant, proves its empty/initial and Prepared/concl/nop cases, and
derives active-region no-mark/no-owner when supplied. The newest local code
consequence no longer requires that global invariant for the current guard: a
concrete raw mark yields its same-age authentic event and an
`ActiveMateEventAnchor`, so no raw mark or exact owner remains; tag freshness and
structural search then yield `NewSourceRegionInput` and `NewEnabled`. None of
these steps records new page/chapter reading. A downstream kernel-checked code
consequence now combines that unmarked-tensor result with stable enabledness and
the marked-tensor adjacency bridge. For a supplied correct canonical-history
ready head, it returns an inclusive priority-enabled-or-predecessor-gap
disjunction; under certified reachability the positive branch gives an exact
dispatcher result. The gap says that the marked mate resolves to a retained
boundary strictly below the active top but lacks an immediate-predecessor
witness. It does not deny that another branch may also be enabled, prove the gap
unreachable, or establish ready-head existence. The deterministic replay audit
observed 6,198 default and 26,658 extended marked-tensor ready-head states with
zero such gaps. This is finite executable evidence and records no new
page/chapter reading or universal theorem. A further kernel-checked code
consequence now defines the predecessor invariant over every ready or waiting
`FutureWorkAt`, not only the selected head, and preserves it through
empty/init/Prepared/Concl/Nop/New and canonical Wait, Forward, and
UnifyPayload.
The Wait proof transports retained work and derives the inserted conclusion's
adjacency from reference, touch, and commitment geometry. A source-visible
conditional bridge packages that geometry only after strict older-event
separation and an exact child-event anchor are supplied; it does not prove
either premise, applicability, or progress. The Forward proof privately derives
those premises for an already-successful typed step. The Unify proof first
exposes a carrier-free raw touch theorem for the inserted tensor conclusion.
Retained evidence survives the final sigma pop; moved active work contradicts
strict output order; and created work composes final component provenance, that
raw touch result, and the conditional bridge. Both typed branch theorems consume
declarative correctness, the complete scheduler invariant, canonical history,
typed dispatch/step data, and the prior invariant. A further kernel-checked
packaging consequence inducts over every exact canonical dispatcher history,
exposes the invariant for every correct `ExecutedHistory`, and eliminates the
predecessor residual at an explicitly supplied reachable ready head to produce
one exact successful dispatcher result. The theorem is independent of the
finite replay and does not construct that ready head. These are code
consequences and record no new page/chapter reading.
`SequentialFigure7ActiveTopResidual.lean` is a further kernel-checked code
consequence. It uses stack alignment and exact ready-bucket/frontier
correspondence to prove that a started invariant state has no ready head exactly
when its active live component has no raw-unmarked frontier occurrence. The
reachable wrapper combines this with the full-history ready-head result to
return a non-exclusive exact-dispatch / explicit-residual disjunction. It neither interprets the
residual as semantic completion nor proves it unreachable, and it records no
new literature reading.
`SequentialFigure7ActiveTopMarkedNonconclusionDebt.lean` is another
kernel-checked code consequence, not a new source-reading claim. Its state
predicate pairs each marked nonconclusion on the active frontier with a
raw-unmarked nonconclusion witness there. Empty, initial reservation, and New
establish it, with no additional scheduler-invariant premise needed by New;
Concl preserves it; and Forward/UnifyPayload establish it under the prior
complete scheduler invariant when their created conclusion is not global.
Under declarative correctness and the complete scheduler invariant, the debt
and `ActiveTopDrained` imply
`core.allMarked = true`.
`SequentialFigure7ActiveTopDebtBranchResidual.lean` is a further code
consequence. Under prior debt, post-Nop and post-Wait debt are exactly the
prepared selected-away witness. Under the prior complete invariant and a global
created conclusion, Forward and UnifyPayload post-debt are exactly presence
implying a non-global vertex in the branch's ready tail. Presence only detects
vacuity. Canonical history derives no debt witness, so full debt preservation remains
open. This records no new page or chapter reading.
`SequentialFigure7ContinuationCredit.lean` and its preservation module are also
kernel-checked code consequences, with no new source-reading claim. Their two
carriers give every concretely marked nonconclusion an unmarked-mate,
future-conclusion, or marked-conclusion receipt. Fresh events receive credit in
all six dispatcher cases. The six branch transports and two dispatcher
transports require structural well-formedness; Nop and New additionally use the
old owner's mark. Exact canonical tag histories preserve the predicate without
a correctness premise. This weaker history invariant supplies no active-frontier
raw witness, selected-away witness, global-created exact tail, full active-top
debt preservation, or progress theorem.
`SequentialFigure7ContinuationExit.lean` is the next kernel-checked code
consequence and records no new source reading. Strict increase of formula
complexity normalizes any supplied continuation receipt through a finite chain
of marked non-global conclusions to an unmarked raw mate, future-conclusion
work, or a marked global conclusion. A separate endpoint-bound receipt retains
only the raw and future cases and binds the endpoint to one component frontier;
it has no global case. This locality condition is sufficient, is not claimed
necessary. With structural well-formedness and queued vertices unmarked it
implies active-top debt; with declarative correctness, the complete scheduler
invariant, and
`ActiveTopDrained` it implies `core.allMarked = true`. These are conditional
code consequences, not an existence, unconditional progress, completion,
terminality, or totality theorem.
`SequentialFigure7EndpointLocalityObstruction.lean` is a further code
consequence and records no new source reading. Every successful typed
`WaitStep` from a scheduler-invariant input refutes the unrestricted locality
law at its output, so that exact law cannot be a full canonical-history
invariant across successful Wait transitions. The theorem neither makes the
output drained nor establishes reachable-Wait existence or progress. It does
not refute direct debt or a Wait-compatible drained, temporal, or
cross-component weakening, and the earlier conditional implications remain
valid. A concrete `native_decide` trace remains research-only and outside the
public theorem.
`SequentialFigure7ActiveTopDebtQueueTail.lean` and
`SequentialFigure7ActiveTopDebtHistoryTail.lean` are further kernel-checked
code consequences and add no source reading. Under prior debt and the complete
scheduler invariant, the Nop and Wait post-debt propositions are each exactly
equivalent to a non-global vertex in the prepared `remainingTop`. The
reset-aware `ActiveTopDebtTailLaw` retains the prior obligation through Concl,
Nop, and Wait, requires that exact witness for Nop and Wait, and resets at New,
Forward, and UnifyPayload to the exact current branch obligation. The law plus
the matching canonical tag history yields endpoint debt. The law is supplied,
not derived from correctness, canonical history, or reachability; therefore no
unconditional all-marked, progress, termination, totality, or completeness
claim follows.
`SequentialFigure7ActiveTopDebtParentEscape.lean` is a further kernel-checked
code consequence and adds no source reading. For an explicit ready head
selecting a `par`, declarative correctness plus `SchedulerInvariant` returns
the active component occurrence/accounting data and either a non-global
ready-tail witness or `ActiveCarrierParentEscape`. The escape is a concrete
marked non-global frontier premise distinct from the selected vertex whose
exact submitted connective parent conclusion lies outside the active owned
carrier. The theorem does not assert that these outcomes are exclusive; if the
tail is absent, the failure-conditioned theorem forces the escape.
`CanonicalTagHistory` is used only by the separate theorem authenticating the
concrete mark as an earlier prepared-selection event. This layer neither
assumes nor derives `ActiveTopDebtTailLaw`, and it contains no computational
coexistence receipt. The downstream re-entry classifier reduces no-tail failure
to selected-raw or concretely-marked targets; its stored-right specialization
now eliminates the selected target, while the marked target remains open.
`SequentialFigure7ActiveTopDebtParentEscapeTemporal.lean` is another
kernel-checked code consequence and adds no source reading. With a matching
canonical tag history, correctness, scheduler invariant, active
occurrence/accounting data, and no-tail escape, it gives an exact source split.
Par has an authentic reservation anchor and a raw-sibling or strictly older
future/marked continuation. In the tensor branch, the escaped mark resolves to
the active representative while its sibling and conclusion lie outside the
carrier; the branch retains the older marked-tensor predecessor
invariant. The theorem neither supplies the missing tail nor eliminates either
residual, and it does not assume or derive `ActiveTopDebtTailLaw`.
`SequentialFigure7ActiveTopDebtParentTemporalOutcome.lean` adds no source
reading. It consumes the already-proved continuation-credit and temporal
residual APIs to map both par and tensor into a raw-sibling, older-future, or
older-marked outcome. The future and marked parent conclusions stay outside
the active carrier and strictly older than its raw boundary; the raw sibling
is selected or external. This remains a residual reduction, not a tail or
history theorem.
`SequentialFigure7ActiveTopDebtParentExternalTemporalOutcome.lean` adds no
source reading. For actual Nop and Wait failures, typed mate facts eliminate
the selected raw case from that common outcome. The remaining endpoint is raw
and outside the active owned carrier, or it is an outside future/marked parent
at a strictly older boundary or representative. No endpoint is shown to
re-enter the active frontier, so no ready-tail witness or history-tail law is
derived.
`SequentialFigure7ActiveTopDebtParentExternalCommitmentOutcome.lean` adds no
new source reading. It uses retained `sigma` order and the canonical
commitment-edge path API to attach the final predecessor-to-active edge to the
older future and older marked branches. It preserves the external raw branch
and proves no endpoint re-entry, tail witness, or tail law.
`SequentialFigure7ActiveTopDebtParentExternalEndpointCrossing.lean` also adds
no new source reading. It uses reference-switching connectedness, exact child
occurrence ownership, and graph boundary extraction to connect the active
carrier to each older endpoint and retain one owned-to-outside stored-edge
crossing. It does not classify that crossing as raw or marked, return a
ready-tail witness, or derive the history-tail law.
`SequentialFigure7ActiveTopDebtParentExternalCommitmentReentry.lean` adds no
new source reading. It composes every adjacent commitment path across the
positive retained interval. Ready future and marked endpoints receive an
endpoint-to-active path and an exact outside-to-inside edge; waiting retains
its exact cell and raw work remains unchanged. The edge is not classified as a
distinct raw payer, so no ready-tail witness or history-tail law follows.
`SequentialFigure7ActiveTopDebtParentExternalReentryTarget.lean` adds no new
source reading. It proves that the re-entry is the reverse of an exact
submitted connective-parent edge with a non-global active-frontier target.
Exact ready-bucket accounting classifies the target as selected raw, ready-tail
raw, or concretely marked. The no-tail wrapper removes only the ready-tail
case. Canonical raw-mark history authenticates a marked target at the active
representative. A retained path that also avoids the current par conclusion
cannot target the selected head, so only a distinct historical mark remains.
Adjacent-edge target avoidance now accepts the exact child-event untouched law
for this par conclusion. The active-edge dichotomy returns either avoidance or
an authentic same-age trace step from the conclusion to selected or mate. The
complete positive-interval dichotomy now composes all local avoiding paths or
localizes one exact failed child edge with an authentic child-age
selected/mate trace; the child is strictly before or equal to the final
boundary. Active-carrier localization excludes strictly older traces to the
selected head or an active-owned mate, leaving only a stored-right trace to an
external mate. Equal-final selected/mate traces and the inclusive outer split
remain. Typed Nop identifies the older external mate as raw-unmarked; typed
Wait identifies its exact concrete mark and strictly older representative.
The modules do not return those external endpoints to the active frontier,
eliminate the equal-final cases, or produce a distinct payer, tail law, or
progress theorem.
`SequentialFigure7CommitmentIntervalParGuardReentry.lean` adds no source
reading. Supplied reference-switching connectedness returns the exact older
Nop/Wait mate through one active-carrier inbound parent edge and classifies
its target as selected raw, non-global ready-tail raw, or concretely marked.
The selected/marked and equal-final branches remain, so this is not yet a
tail-law or progress theorem.
`SequentialFigure7CommitmentIntervalParGuardReentryFailure.lean` also adds no
source reading. Under exact absence of a non-global ready-tail witness, the
stored-right guard, parent uniqueness, and strict complexity exclude the
selected target in the strictly older Nop/Wait branch. The surviving target is
a distinct authenticated concrete mark represented at the active boundary.
The theorem does not eliminate that mark or either equal-final trace.
`SequentialFigure7CommitmentIntervalParGuardReentryMateSeparation.lean` adds no
source reading. The retained simple path makes the exact marked target distinct
from its starting current mate. Exact connective-parent uniqueness then shows
that every connective view rooted at that target has a mate different from the
current selected head. The result excludes the selected raw-sibling alternative
for this target, but does not eliminate the target, choose its source kind,
derive a ready-tail witness or history-tail law, or close equal-final traces.
`SequentialFigure7CommitmentIntervalParGuardReentryMarkedTargetTemporal.lean`
adds no source reading. It binds the unique consumer at that exact marked
target to the inbound parent edge and normalizes its continuation to raw work
outside the active carrier, queued parent work at a strictly older boundary,
or a parent conclusion marked at a strictly older representative. It does not
eliminate the target or any case, derive a tail witness or law, or close the
avoiding/equal-final traces.
`SequentialFigure7CommitmentIntervalParGuardReentryMarkedTargetContinuationExit.lean`
adds no source reading. It follows the target-bound marked parent through the
finite continuation-credit normalizer and preserves exact endpoint identity.
Its raw endpoint is outside the carrier or returns to the current
selected/mate pair; future and marked-global endpoints remain outside at a
strictly older boundary or representative. It does not eliminate any exit,
derive a payer or tail law, or close the avoiding/equal-final traces.
`SequentialFigure7MarkedTargetRawReturnCyclicReduction.lean`
adds no source reading. It turns the exact raw return into a closed full-graph
walk whose switching prefix is retained and whose continuation tail is forward
with distinct targets; both segments are individually nonbacktracking.
Nontrivial complete cancellation occurs at one of their two exact oriented
endpoint junctions. Both segments then have unique occurrence indices; every
prefix occurrence is backward, its exact reverse occurs in the tail, and its
reached vertex is a concrete marked non-global source in the tail ledger.
Otherwise the reduction exposes both premise occurrences of a par, placing the
kept one in the prefix and the omitted one in the continuation tail. The
omitted-right source is concretely marked and non-global. It does not order the
paired occurrences into exact reverse traversals or eliminate either residual
or any other open exit/trace branch.
Global preservation of the mate-region and older-raw-mark invariants through
candidate-creating rules remains open, as do queue origin, created-candidate raw
seams, derivation of the re-entry avoidance premise, marked-history descent,
unconditional active-top completion, progress,
later-state totality,
fallback removal,
sequentialization, faithful token-age scheduling, and whole-program linearity.
The future-head-touch invariant is
preserved through New and through
Wait, Forward, and UnifyPayload after structurally deriving their created-head
residuals, and canonical-history induction now makes it globally available
under structural well-formedness. Global preservation of the mate-region and
raw-mark invariants remains open, although the local active-guard enabledness
theorem bypasses their availability at its current state. The New raw-mark
branch is now conditionally
transported: switching acyclicity removes
the selected-mark/created-candidate case, and
`NewRetainedRawMarksSeparated` names the sole remaining retained-mark seam.
This is a kernel-checked code consequence, not a new literature reading or a
proof that canonical histories satisfy the seam. The Wait raw-mark branch is
also conditionally transported: the typed age order eliminates the selected
mark, and `WaitRetainedRawMarksSeparated` names the retained-mark seam. This is
again a kernel-checked code consequence, not a new literature reading or proof
that canonical histories satisfy the seam. The Forward raw-mark branch is
likewise conditionally transported: selected and inserted work share the same
active raw age, and `ForwardRetainedRawMarksSeparated` names the sole
retained-mark seam. This is a kernel-checked code consequence, not a new
literature reading or proof that canonical histories satisfy the seam. The
UnifyPayload raw-mark branch is now conditionally transported as well: strict
output order excludes the retired active class, and
`UnifyPayloadCreatedRawMarksSeparated` names the inserted-candidate seam. The
covering origin alternatives need not be exclusive. This is again a
kernel-checked code consequence, not new literature reading or evidence that
canonical histories satisfy the seam. Canonical histories now have an exact
raw-mark event provenance layer: every final
concrete mark is the selection of an authentic typed dispatcher branch, and
the one-step effect is exactly old-or-current-event. This is a kernel-checked
code consequence, not a new literature reading. It does not identify raw marks
with `NEXTAXIOM` touches and does not by itself supply queue origin,
vertex-level commitment paths, target avoidance, or any created-candidate
seam. An independent kernel-checked commitment-spine layer now proves that
every adjacent pair in the final retained `sigma` is backed by the exact
historical `new` event stored at the child raw-age ledger slot. This closes
allocation ancestry only and is not a new literature reading. Ownership
through a complete reachable transition system remains open, but a new
kernel-checked code consequence now gives the local raw-mark reservation
anchor: each concrete mark and both endpoints of its same-age reservation event
share one exact owned carrier, with contained paths to both endpoints. This is
not a new literature reading. A further kernel-checked code consequence now
composes one exact adjacent retained commitment edge from the parent event's
left endpoint to the child event's left endpoint, retaining the historical
`new` step and both owned anchors. This too is not a new literature reading.
A further kernel-checked code consequence conditionally makes that single edge
avoid a supplied future tensor conclusion when the exact child ledger event is
explicitly known not to touch it. This is not a new literature reading and does
not derive the untouched law. A further kernel-checked code consequence now
composes explicit adjacent avoiding witnesses across any positive-length
retained-`sigma` interval. It matches exact middle ledger events and uses
verified loop erasure; this too is not new literature reading. Global
availability of the untouched laws and edge callbacks, unconditional
whole-history instantiation, queue origin, the four raw seams, later-state
totality, progress, and pure-worklist completeness remain open.

On 2026-07-28 the official metadata and abstract were checked for Guerrini,
[*A linear algorithm for MLL proof net correctness and
sequentialization*](https://www.sciencedirect.com/science/article/pii/S0304397510007127),
*Theoretical Computer Science* 412(20), 2011,
DOI `10.1016/j.tcs.2010.12.021`. The abstract describes a full-detail account
of the 1999 algorithm. The full text could not be accessed and was not read;
the record therefore does not change the 16-PDF inventory, included-page
counts, completion claims, or the status of the 1999 indexing conflict.
