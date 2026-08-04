# ProofNet-IR

ProofNet-IR is an experimental, verified proof-geometry intermediate
representation for AI-guided theorem proving in Lean 4.

Current release: `v0.9.0` (exact occurrence-aware graph semantics,
checker-free reconstruction proved complete for every accepted certificate,
and a sound worklist-first unification tier whose exact wrapper is proved
equal to the reference checker). Pure-worklist completeness and a
whole-program linear bound are not claimed. See [CHANGELOG.md](CHANGELOG.md)
and [the release audit](docs/v0.9-release-audit.md) for the precise guarantees
and non-goals.

Development on `main` now continues as `v0.10.0-dev`. Lean now constructs one
unified exact closing package with common terminal-base, complement-base,
complement, and normalized-core indices, then enriches its proof-relevant seam
replay with an occurrence-position endpoint zipper. Unlike the older
`CyclicSeamCursor.gap`, the zipper gap is definitionally the complete
complementary arc between the fixed first and last tagged endpoint occurrences.
Every indexed flipped scheduler segment is proved nonempty. Consequently, an
empty zipper gap in the initial tagged scheduler family would force exactly the
scheduler-coordinate adjacency already excluded by the closing endpoint
witness, so that complete complementary arc is nonempty.

Starting from the normalized closing core's empty exact gap, Lean now builds a
canonical endpoint replay of the fixed terminal-complement step. It always
first-opens in that terminal replay by an internal case split: if the exact
reverse-shell context is nonempty, the reverse-shell frame opens the gap first;
otherwise the generator's nonempty omitted arc opens it in the second frame.
The returned first-opening proposition does not itself expose a separately
consumable branch/origin sum or identify the anchor as the opening frame.
Alongside that proposition, the construction separately retains
`closing.map erase = reverseTraversal (opening.map erase)`, the omitted-right
zero-offset backward anchor at the arc head, the forward retained-left last
occurrence of that outer arc, and the exact base-gap equation
`closing ++ taggedArc ++ opening`. Erasing the nonempty outer `taggedArc`
gives a closed `EdgeWalk` at the complement base and a
`CuspFreeTraversal`; its exact cyclic closing pair is nevertheless
`Cusp outerLast.value anchor.value`, with
`outerLast.value ≠ anchor.value.reverse`. The cusp is at the wraparound pair,
not an internal adjacency forbidden by the linear cusp-free predicate. The
base gap is nonempty. Endpoint replay preserves the complete old gap as a
sublist, so the whole `taggedArc` remains an ordered sublist of the exact gap
after the ancestry replay reaches the initial scheduler family; in particular,
its omitted-right head and retained-left last occurrence remain members there.
From a retained sublist's exact `head?` and `getLast?`, a generic list lemma now
extracts an ordered decomposition of the containing list. Applied here, the
initial exact gap has the form
`g0 ++ anchor :: g1 ++ outerLast :: g2`, and the enclosing scheduler family
has a `CyclicFourPointDisplayAt firstTag lastTag anchor outerLast`. The generic
four-point relation permits empty intervening lists and repeated values; it is
not a strict scheduler-rank theorem. This generic result is linear
ordered-sublist transport, not contiguity, a fixed linear rank, crossing,
cyclic betweenness, or a model-specific scheduler-order/proper-nesting theorem.
For the actual complete initial `tagSchedulerFamily`, the ambient scheduler
coordinates are `Nodup`, even when erased directed-edge values repeat. Lean now
uses that fact to prove
`[firstTag, lastTag, anchor, outerLast].Nodup`; this distinguishes the four
exact `SchedulerOccurrence` tags, not their erased edges, edge endpoints, or
vertices. The endpoint replay retains the same outer positioned par choice
which names `anchor` and `outerLast`. Exact membership transport then lifts
both that outer witness and the normalized inner closing witness through
ancestry to the complete initial family. One specialized theorem returns both
positioned witnesses, the four-point display, and the four-tag `Nodup` fact
together. Its cyclic point order is
`firstTag → lastTag → anchor → outerLast`: the inner and outer endpoint pairs
are separated, not alternating, so this is not a crossing witness. No
intervening interval is proved nonempty, and contiguity, fixed or modular rank,
a model-specific scheduler-order/proper-nesting contradiction, closing-par
exclusion, progress, and pure-worklist completeness remain unproved. No
planarity principle is assumed for commutative MLL.

A stable three-axiom/two-tensor regression now rules out one proposed way of
closing that gap. The current eager initializer assigns token ages in submitted
axiom-link order, while the flat worklist reverses submitted connective order;
the accepted regression therefore fires a tensor joining ages 0 and 2 before
the intervening age-1 component. It succeeds in exactly two attempts, with no
waiting requeue and two successful firings. These public counters are the
regression receipt, not a direct observation of token-class membership; the
noncontiguous merge follows from the fixed links and the eager-start and
reverse-queue definitions. Thus the current flat scheduler does not preserve
contiguous token-age intervals or a Figure-7 top-of-stack union discipline.
`tagSchedulerFamily.step` is the index of a selected dependency-cycle segment,
not a firing time or token age. Moreover, the displayed
`firstTag → lastTag → anchor → outerLast` order consists of two separated
endpoint pairs, which ordinary laminarity permits as siblings. Flat-worklist
completeness may instead be pursued through preservation of a residual parsing
witness or a suitable theorem modulo an explicitly justified observation.
Guerrini-style whole-program linearity remains a separate goal and requires a
faithful full `NEXTAXIOM`/token-age scheduler. General checker-accepted
sequentialization is already complete through recursive reconstruction;
closing-par exclusion, correct-state progress, pure-worklist completeness,
fallback removal, and linearity remain open.

The separate delayed-scheduler track now implements the project's operational
local Figure-7 `new` pipeline over the currently proved
`ReservationInvariant`. It pops the
deterministic head of the last ready bucket without discarding an exhausted
bucket, raw-marks that occurrence at the old last `σ` boundary in both state
views, resolves the unique orientation-aware tensor consumer through the
certificate's fixed sound-and-complete `ConsumerIndex`, runs `NEXTAXIOM` from
the opposite tensor premise in the post-mark production state, and appends and
reserves the returned axiom with fully threaded tags. That reservation uses
`operationalNewEnqueue?`: the old active `σ` boundary becomes an initialized
empty waiting cell, while the newly pushed active top remains undefined. Lean
proves preservation of `OperationalWaitingDomain`, which says exactly that
allocated initialized waiting cells are the inactive boundaries
`sigma.dropLast`. The printed Figure-7 update that writes the fresh cell is
retained separately as the display-only `newEnqueue?`; production code does
not call it. Choosing the old-boundary update is this project's interpretation
of the paper's surrounding prose and its `wait`/`unify` behavior, not an
author-confirmed erratum or a uniqueness result. The proof argument rules out
independently forged stack horizons, raw ages, and production carriers, and
callers cannot substitute a partial consumer table. This remains a local rule,
not a full scheduler theorem: `ReservationInvariant` alone records only
tag-array size rather than tag provenance/monotonicity, and it does not
establish waiting-payload or global queue ownership. The local `wait` and
successful `forward` rules described below obtain those obligations from the
stronger supplied `SchedulerInvariant`. A bounded `UnifyEmpty` query now
covers exactly the `W(j) = empty` successful-rule slice under the supplied
`ReservationInvariant`: soundness needs that invariant, while completeness and
the direct iff additionally require structural validity and the separate
ready-list `Nodup` premise. Given the stronger state-only
`SchedulerInvariant`, every successful typed or executable bounded step now
preserves that entire occurrence-exact invariant, including `RealizesSigma`,
component-forest ownership, live-frontier/queue/waiting/pending facts, and the
exact firing counter across the simultaneous active-`sigma` pop and
`parent[i] := j` union. The strict-singleton `UnifyOne` slice now covers
exactly `W(j) = [c]`. It recovers `c`'s unique producer from the occurrence
source index with the exact submitted par slot and stored orientation, then
executes one atomic prepare → tensor construction/union → waiting-par
activation → scheduler-drain transition. `UnifyOneRule` and
`WaitingParActivationRule` are independent Boolean-free relations; their
typed/executable correspondence and output uniqueness are kernel checked.
Every successful typed or executable `UnifyOne` preserves
`ReservationInvariant` and the complete occurrence-exact
`SchedulerInvariant`, and the exact connective counter increases by two.
`unifyOne?` rejects `W(j) = []` and every payload of length at least two; the
empty case remains the separate `UnifyEmpty` slice. Guerrini's paper specifies
moving `W(j)` into ready. Explicitly constructing the waiting par before that
move is this project's derivation/provenance representation refinement, not a
claim that the paper states such a construction.
`SequentialFigure7Unify.lean` now adds the local production-core foundation for
an arbitrary finite stored payload. `activateWaitingPayload?` threads
`activateWaitingPar?` head to tail; independent direct and typed fold relations
have exact executable correspondence and unique output. Successful typed folds
preserve marks, parents, component-array size, started-axiom count, abstraction,
ordered parents, formula consistency, and reservation carrier alignment under
their stated hypotheses, while increasing the project-local connective counter
by exactly `payload.length`. Guerrini's `W(j)` is set-valued, so this traversal
order and its exact derivation nesting are deterministic representation choices.
This fold has no scheduler stack and does not prove payload applicability,
occurrence-forest preservation, an atomic arbitrary-payload `Unify`, or any
complexity bound.
`SequentialFigure7UnifyPayload.lean` now supplies that local atomic composition:
`unifyPayload?` executes the common prepare prefix, one exact tensor
construction/union, the stored-head-to-tail activation fold, and the exact
two-level scheduler drain. Its high-level-executable-independent direct
`UnifyPayloadRule`, typed witness, and executable have exact correspondence
and output uniqueness
under the documented structural, `ReservationInvariant`, and final-ready
`Nodup` premises. Successful typed/executable steps preserve
`ReservationInvariant`, and the exact state theorem fixes
`after.core.firedConnectives = before.core.firedConnectives + 1 + payload.length`
in the
project representation. `SequentialFigure7UnifyPayloadInvariant.lean` now
proves that every such successful typed or executable step also preserves the
complete occurrence-exact state-only `SchedulerInvariant`, including
`ComponentForestProvenance`. Its non-circular transient gap invariant fixes the
final scheduler stack, accounts for the not-yet-activated payload suffix, and
closes after the last activation. Payload freshness and exact occurrence
provenance are derived from the full input invariant; pre-activation payload
conclusions are forest-fresh/non-produced, each activation establishes their
exact ownership, and the final forest covers the full payload. No
history/reachability hypothesis is added. `SequentialFigure7UnifyPayloadEnabled.lean`
adds the separate input-only applicability layer: `UnifyPayloadEnabled` records
only the top ready occurrence, two adjacent sigma levels, the canonical tensor
consumer, and the mate raw age in the previous interval. From that predicate
plus the complete `SchedulerInvariant`, Lean derives every hidden mutation
guard and proves that `unifyPayload?` returns a result satisfying the same
invariant. The predicate contains no post-state or success equation. The full
invariant alone does not imply it, as exact empty and initialized axiom-only
counterexamples demonstrate. Exhaustive derivation of this predicate for the
selected dispatcher branch remains open. Intermediate tensor/fold states are
not claimed to satisfy `SchedulerInvariant`. Existing
`UnifyEmpty`/`UnifyOne` successes map one way to the same exact output of the
new executor, without a general executor equality or reverse equivalence.
Stored order fixes execution and derivation nesting only; no commutativity,
paper temporal order, O(1), or linearity claim follows.
`SequentialFigure7StableEnabled.lean` supplies the matching input-only layer
for the four stable rules. `ReadyHeadInput` records just the top ready
occurrence, its tail and raw age, and the exact top/sigma equations;
`SubmittedParInput` records an exact submitted par slot and premise
orientation. `ConclInput`, `NopInput`, `WaitInput`, and `ForwardInput` then add
only their rule-side input guards. In particular, wait does not store its
derived sigma destination or waiting payload, and forward does not store its
derived active token, component picks, or representation `Nodup`. No enabled
witness stores a post-state or executor-success equation. From each predicate
plus the complete `SchedulerInvariant`, Lean derives the hidden guards, proves
the corresponding executor succeeds, and returns a result preserving that
invariant. For a supplied ready head and exact submitted par, the invariant
also proves the scoped `NopEnabled ∨ WaitEnabled ∨ ForwardEnabled`
classification. This does not classify conclusions, tensors, `new`,
unification, empty/completed ready buckets, dispatcher priority, or arbitrary
invariant-valid work, and it proves no unconditional reachability or progress.
`SequentialFigure7Dispatcher.lean` now gives the six implemented canonical
rules one deterministic entry point, with precedence
`concl → nop → new → wait → forward → unifyPayload`. Its dependent
`DispatchStep` retains the successful executor equation and every earlier
branch's exact `none` equation, and `dispatch?_some_iff` characterizes that
priority-aware result. Every successful dispatcher call preserves the complete
`SchedulerInvariant`. Empty- and singleton-payload compatibility executors are
not separate dispatcher tags: their existing successes enter through the one
general `unifyPayload` branch, avoiding duplicate history representations.
`ExecutedHistory` and `ReachableByImplementedDispatcher` record exact certified
executions, but every later edge explicitly carries the full invariant used by
the call. They are therefore proof-carrying traces, not applicability,
unconditional reachability, totality, or progress theorems. A regression locks
the distinction by showing that an invariant-valid empty scheduler state has
`dispatch? = none`.
`SequentialFigure7PriorityEnabled.lean` now characterizes that same fixed
dispatcher order with branch-indexed applicability. For `concl`, `nop`,
`wait`, `forward`, and `unifyPayload`, a successful typed step reconstructs the
existing pure input-only enabled witness, and the corresponding executor has
existential success exactly when that witness exists under the full
`SchedulerInvariant`. The `new` field in this priority layer remains the
operational compatibility proposition `NewExecutableEnabled`, naming
existential `new?` success. `PriorityEnabled` combines one selected enabled witness with the
negations of all earlier predicates, giving exact conversion to `DispatchStep`,
exact selected-kind success iff, dispatcher failure iff no indexed kind is
enabled, and uniqueness of the priority kind. A real completed ready state
`[[]]` satisfies the invariant while no priority kind applies. Thus this is an
exact interface to current dispatcher behavior, not a proof that every
intended nonterminal state has a branch, nor progress, pure-worklist
completeness, fallback removal, or whole-program linearity.
`SequentialFigure7NewInputNecessary.lean` now exposes a separate, deliberately
one-way input projection for `new`. `NewGuard` records the ready head, exact
valid tensor-below consumer, and input-unmarked mate;
`FreshSourceLeftRoute` adds a bounded exact source-left route with input tag
freshness, whole-trace production readiness, and ready axiom endpoints. A
typed `NewStep`, executable `new?`
success, `NewExecutableEnabled`, or a priority-selected `new` branch implies
`NewInputNecessary`. There is no converse: the witness does not record
recursive per-step tag-update equations, exclusion of the terminal partner
from the intermediate trace, or the later operational enqueue guard. All-true
and terminal-partner-pretagged regressions keep
the shallow guard while `new?` fails. Consequently dispatcher priority still
uses operational `NewExecutableEnabled`; this module proves neither input-only
enabledness nor later-call `NEXTAXIOM` totality.
`SequentialFreshSourceLeftRun.lean` supplies the missing exact route layer: a
fuel-indexed inductive witness mirrors both terminal-axiom orientations and
the stored-left tensor/par recursion of `nextAxiomWithFuel?`, including each
recursive tag update and raw-mark readiness fact. Lean proves exact execution
correspondence in both directions, trace `Nodup` and freshness,
terminal-partner exclusion, and exact terminal reservation under structural
well-formedness and carrier alignment. `SequentialFigure7NewEnabled.lean`
then defines the genuine input-only local predicate `NewEnabled` from
`NewGuard`, one exact run at the certificate fuel bound, and the exact
operational enqueue guard at the selected raw age. The witness contains no
executor result/equation, output, history, or reachability field. Under
`SchedulerInvariant`, it is equivalent to existential `new?` success and
yields an invariant-preserving output. A queued-partner regression shows that
`NewGuard` plus the exact run is still insufficient without the enqueue guard.
This closes only local `new` applicability; `PriorityEnabled` has not yet been
migrated from its compatible operational field because that requires a
dedicated dependency split. It proves no reachable nonterminal exhaustiveness,
later-call totality, dispatcher progress, pure-worklist completeness, fallback
removal, or whole-program linearity.
`SequentialFigure7TagHistory.lean` augments exactly those existing traces with
branch-aligned tag evidence. The five non-`new` branches preserve the complete
tag array; `new` retains its exact `NEXTAXIOM` touch and submitted axiom-link
slot. Every certified reachable state therefore has a canonical tag history,
and Lean proves current true tags iff recorded initialization/`new` touches,
history-wide touch separation, monotone growth, and submitted-slot `Nodup`.
The touched predicate is history-independent for two exact histories ending at
the same state. This does not make `SchedulerInvariant` a history predicate:
same-sized forged tag arrays can still satisfy that state-only invariant, and
this checkpoint does not separately prove the concrete all-true regression
state unreachable.
`SequentialFigure7History.lean` now separately
defines proof-relevant reachability for exactly the empty/init/operational-new
fragment. For every such execution, Lean proves current tags are true exactly
at vertices touched by a recorded search, submitted axiom-link slots never
repeat across the whole history, and the reservation-event count equals both
`nextAge` and `startedAxioms`. This dedicated `InitNewHistory` is intentionally
not a generic Figure-7 history: the executable non-reserving `concl`, `nop`,
`wait`, `forward`, bounded `UnifyEmpty`, strict-singleton `UnifyOne`, and
arbitrary-payload `UnifyPayload` rules need rule-step accounting distinct from
reservation-event counting and remain outside that richer reservation-only
history. The canonical dispatcher tag augmentation now lifts exact touch
provenance and axiom-slot non-reuse across all six rule families, but it does
not lift the reservation-event count theorem or publish a whole-history
oriented-route theorem. Guard applicability,
exhaustive branch classification, correct-state progress, pure-worklist
completeness, fallback removal, and linearity remain open.

`SequentialFigure7Rules.lean` now makes the common non-`init` prefix and five
local rule slices exact. A proof-carrying generic
`ConnectiveBelow` query fixes lookup to the certificate's canonical consumer
index and retains the submitted par/tensor slot, stored premise orientation,
opposite premise, conclusion, and local link well-formedness. A separate
`ConclusionBelow` query requires explicit conclusion membership, local
`NodeWellFormed` ownership, and an exactly empty consumer bucket; it
deliberately does not identify
`uniqueConsumer? = none` with a conclusion, because a malformed bucket with
distinct consumers also returns `none`. `prepare?` synchronizes
pop-before-mark with the production raw mark. `concl?` accepts only the exact
conclusion view; `nop?` accepts only an exact par view whose mate remains raw
unmarked after the prefix. `wait?` accepts only an exact par view whose mate
has raw mark `mateRawAge < selectedRawAge`; it computes
`sigmaBoundary? stack.sigma mateRawAge` and prepends the par conclusion to that
already initialized cell. It never substitutes a union-find representative or
the raw age itself for the returned boundary, and this local layer performs no
`queuedVertices` scan. `forward?` instead requires the exact submitted par,
the mate's raw mark, and the paper guard
`selectedRawAge ≤ mateRawAge`; the inequality is intentionally non-strict.
A separate theorem regression covers the non-equality interval case
`sigmaBoundary? [0] 1 = some 0`. The executable then queues that exact par and
prepends its conclusion to the active ready bucket. Its additional
`(conclusion :: remainingTop).Nodup` guard is only a fail-closed list-shape
check, not part of the paper rule.

The five bounded `concl`/`nop`/`wait`/`forward`/`UnifyEmpty` rules and the
strict-singleton `UnifyOne` slice have dependent success-iff witnesses, typed
unique outputs, and preserve `ReservationInvariant`. The bounded `UnifyEmpty` proof transports
`RealizesSigma` through `parent[i] := j`; under the supplied full
`SchedulerInvariant`, its typed and executable successful steps also preserve
the complete occurrence forest and every other state-only invariant field.
A successful `WaitStep` or `ForwardStep`, and
hence a successful executable `wait?` or `forward?`, also preserves the full
current `SchedulerInvariant`. Forward preservation retains the exact submitted
par occurrence, occurrence forest and live frontier, ready/waiting queue facts,
waiting spans, pending-premise coverage, and exact fired-connective count. A
typed `init → nop → forward → concl` regression locks the successful
composition. `UnifyOne` is atomic across prepare, tensor union, exactly one
producer-exact waiting-par activation, and scheduler drain; it preserves the
full invariant and proves the counter changes by exactly two. These are
conditional successful-step theorems, not
applicability, totality, dispatcher, history, reachability, or progress. Only
the wait bucket-local prepend is O(1): tail-based ready/`sigma` operations,
boundary lookup, and the overall transitions have no O(1) or linearity claim.
`NopStep.mate_unmarked_before` proves that this post-prefix executable guard
is the paper's pre-state `μ(u₂)=⊥` guard, because the locally well-formed mate
is distinct from the only occurrence written by the prefix.
`RulePrefixAt`, `ConclRule`, `NopRule`, `WaitRule`, and `ForwardRule` now give
separate Boolean-free direct state relations. The first four mention neither
`prepare?` nor either canonical query or rule executable; `ForwardRule`
likewise avoids every Figure-7 executable and mutation wrapper while retaining
the exact submitted par position, occurrence picks, component update, and
ready-stack result. `WaitRule` uses a proposition-level exact
`sigmaBoundary? = some boundary` equation, not Boolean/Option control flow,
and states its paper guard directly through `before.core.marks`. The old
`ConclStep`/`NopStep`/`WaitStep`/`ForwardStep` records remain as
compatible equation-backed executable witnesses. Lean proves executable
soundness from the supplied `ReservationInvariant`; valid-guard completeness
uses `StructurallyWellFormed` plus that invariant. Each relation has a unique
output under its documented hypotheses. Forward completeness additionally
takes the separate
`ForwardExecutableReadyNodup` representation condition. The complete
`SchedulerInvariant` derives that condition semantically from exact
ready/frontier correspondence and `ProducedPremisesMarked`, yielding a
second direct executable iff without adding `Nodup` to the paper rule.
`NopRule` states the paper-level `μ` guard
directly as `before.core.marks`. Separately, the supplied invariant's
`RealizesSigma.marks_eq` justifies identifying that
production view with the delayed-stack `μ` view; neither statement identifies
raw ages with union-find representatives.
`NodeWellFormed` is a local ownership guard, not a replacement for
`StructurallyWellFormed` or `check`: an eventual untrusted dispatcher must
carry a checked/structural certificate gate and full reachable-state
invariant.
These local rules by themselves do not establish applicability, totality,
unconditional reachability, progress, or a linear-time implementation. The
later canonical dispatcher and certified history only compose already-
successful calls; the canonical consumer table is still rebuilt by this pure
API unless a future scheduler threads it explicitly.

The bounded production-core slice supplies the mutations used by successful
local `forward` and needed by eventual `unify`. `Certificate.queuePar?` and
`Certificate.queueTensor?` build par/tensor components, increment their local
connective counter, and leave the conclusion's raw mark unchanged; under a
prior `ComponentsFormulaConsistent` invariant and explicit `LinkWellFormed`
hypothesis, separate theorems prove the new live components
formula-consistent. The ready-pop rule is still responsible for assigning the
conclusion's raw age.
The tensor core merges the two generic current representatives by
`min`/`max`, with distinctness extracted from the executable guard. The
delayed state separately exposes `prependReadyTop?` and
`mergeTopReadyWaiting?`. The two-level merge uses the reproducible list order
`conclusion :: (payload ++ previousReady ++ activeReady)`, drains the previous
waiting bucket, resets that boundary to `undefined`, and pops one active
level. Figure 7 treats the bucket contents as sets, so this list order is a
project-level deterministic refinement rather than a claim about source
order. A component frontier's derivation/exchange order is also not the ready
bucket's scheduling-list order; later correctness must use proved membership
or permutation facts rather than defining those lists to be equal. Its
`WellShaped` theorem takes merged `Nodup`, conclusion-bound, and
waiting-payload-bound facts explicitly; no primitive infers ownership by
scanning `queuedVertices`.

These primitives are not rules by themselves; `forward?` now composes the par
and active-ready pieces under the guards above. The bounded `unifyEmpty?`
slice composes the tensor and stack operations only when `W(j) = empty`; under
`ReservationInvariant`, its correspondence proof derives that the generic
tensor representatives are exactly the scheduler boundaries `j` and `i` and
therefore orients the update as `parent[i] := j`. It increments the tensor core
only once. `UnifyOne` additionally handles exactly `W(j) = [c]`: its
producer lookup retains `c`'s exact submitted par slot, its activation builds
that par component, and the atomic transition increments the counter by two.
Directly composing `queueTensor?` with `mergeTopReadyWaiting?` without the
activation fold is insufficient: the stack move exposes delayed conclusions in
ready without constructing every corresponding par derivation. The local
head-to-tail fold constructs an arbitrary stored payload, and
`unifyPayload?` now atomically composes it with one tensor and the stack drain.
Its exact theorem accounts for `1 + |W(j)|` project constructors and preserves
the complete occurrence-exact `SchedulerInvariant`; the transient-gap proof
establishes each payload occurrence's exact ownership before the final forest
covers the whole payload. Conditional applicability is proved from explicit
`UnifyPayloadEnabled`; deriving that predicate for intended reachable states,
exhaustive dispatcher enabledness, generalizing reservation-count and
whole-history oriented-route laws, unconditional full-rule reachability and later-state
totality, progress, scheduler/pure-worklist completeness, fallback removal, and
whole-program linearity remain
open. Tail-based list operations also carry no O(1) claim.

The first separate sequential primitive is now present in
`SequentialUnification.lean`. Lean proves exact submitted-link origin for a
reusable source-incidence index. Exact origin alone is only the `Sound`
contract: it does not imply that a bucket exists or is unique, and a malformed
self-axiom is deliberately counted twice at one endpoint. The stronger
`StructurallyWellFormed.sourceIndex_lookup_eq_singleton` theorem now proves
that every in-bounds occurrence of a structurally well-formed certificate has
exactly the singleton bucket consumed by the executable. For an exact
submitted par lookup, `sourceIndex_lookup_eq_submitted_par` strengthens this
to the positional `(linkIndex, link)` incidence, so equal-valued formulas or
links at other slots cannot be substituted. Its bounded, globally
tagged `NEXTAXIOM` search either fails closed or returns the exact submitted
axiom link index and endpoints, the updated tag array, and the followed
occurrence trace; both axiom endpoints were unmarked in the input state and
`trace.length ≤ fuel`.

`SequentialRoute.lean` now gives that trace its exact orientation. Every
successful search has a nonempty source-left chain from the requested start to
the endpoint actually reached, plus the other axiom endpoint. The reached
endpoint is related by proof to the submitted axiom's stored `left`/`right`
orientation instead of being silently identified with `left`; the canonical
stored-right regression reaches endpoint `1` along trace `[5, 1]` while the
submitted axiom remains `.axiom 0 1`.

The result type is indexed by its input tags. Kernel-checked fields and
`nextAxiomWithFuel?_tag_trace_invariants` prove that the tag carrier size is
preserved, every input `true` tag stays `true`, the recursive trace is `Nodup`,
and every trace occurrence plus both axiom endpoints changes from input
`false` to output `true`. `NextAxiomResult.Touched` includes the trace and both
endpoints, including the non-recursive axiom partner.
The equation-backed
`nextAxiomWithFuel?_tagged_iff_input_or_touched` and production-wrapper
corollary additionally prove that every output true tag was either already
true on input or belongs to that exact touched set; there are no unexplained
true tags in an executable result. The execution equation is essential because
the public result record remains manually constructible. Two successful calls
have disjoint touched sets when the second call is made with exactly
`first.tags`. Thus the global no-revisit discipline applies only to a chain
that strictly passes each result's tags onward; the theorem does not apply
after resetting or replacing the tag array.
`nextAxiomWithFuel?_exists_of_structural_clearThrough` additionally proves
local totality on the production source index when structural well-formedness,
state abstraction, rank-scoped untagged/unassigned freshness, and
`formulaComplexityAt start < fuel` hold. Its full-carrier-clear corollary uses
the exact rank budget `formulaComplexityAt start + 1`; this is an initial/local
result, not totality of the carrier-size `nextAxiom?` wrapper or of later
Figure-7 `new` calls. Indeed, one success tags complexity-zero axiom endpoints,
so this global low-rank freshness predicate cannot itself be threaded to a
second call at any natural rank; the later scheduler needs a route-local
freshness invariant.

`SequentialSchedulerState.lean` isolates the first delayed Figures 7–8 state
layer. `SequentialSchedulerBridge.lean` now connects its empty/initial
reservation to the production unifier without collapsing the two state
representations. `RawTokenAge` is
the discovery-order age and is deliberately not a union-find representative.
`SigmaAgePartition` makes `σ` a strictly increasing boundary list below
`nextAge`, with boundary `0` at every positive horizon, and the executable
`sigmaBoundary?` returns the greatest boundary not exceeding a queried raw
age. Fixed-capacity `WaitingCell` storage distinguishes three cases that must
not be collapsed: an out-of-bounds array lookup, an in-bounds `undefined`
cell (`⊥`), and `initialized []` (`∅`).

The strict local initialization guard requires an empty scheduler view: age
horizon, `σ`, and ready buckets are empty; every mark is absent; every
allocated waiting cell is `undefined`; and the two endpoints are distinct and
in bounds. Global carrier agreement and the remaining `WellShaped` obligations
are separate preservation-theorem preconditions. `initEnqueue?` then reserves
age `0`, records
`[[reached, partner]]`, and leaves both endpoint marks and `W(0)` unchanged,
so `W(0)` remains `undefined`. The literal `newEnqueue?` source-audit helper
appends the old age horizon to `σ`, appends the ready bucket
`[reached, partner]`, and writes `[]` to the fresh waiting cell exactly as the
printed Figure-7 display does. It preserves only the deliberately weak
`WellShaped` invariant and is not the production transition.
`operationalNewEnqueue?` instead initializes the old active `σ` boundary,
leaves the fresh active top `undefined`, and preserves
`OperationalWaitingDomain`: among allocated ages, a waiting cell is
initialized iff its age lies in `sigma.dropLast`. This one-cell update is the
project's interpretation of the prose-defined nonactive waiting domain and
the later `wait`/`unify` operations. It is not presented as an
author-confirmed erratum or as the uniquely possible reconstruction of the
paper.

A successful dynamic start immediately allocates and assigns a token and
refines one independent Figure-5 `start` transition under the existing
abstraction and `OrderedParents` invariants. It is not the delayed marking of
Figures 7–8 `init`/`new`. Tests cover
the canonical trace/tags, an already tagged start, zero fuel, out-of-bounds and
marked starts, missing and non-unique malformed sources, a distinct second
start using threaded result tags, repeat rejection, and dynamic token
allocation. A depth-two fixture locks the exact fuel boundary: rank fuel `2`
fails and `rank + 1 = 3` succeeds both by theorem and execution. This is not
yet the Figures 7–8 algorithm. `SequentialSchedulerBridge.lean` now wraps the
delayed and production views in `ReservationState` and provides
`initializeReservation?` and `reserveNewAxiom?`. Each successful call runs the
bounded tagged search, stores its search-oriented `[reached, partner]` bucket,
reserves the submitted axiom at `result.linkIndex` as an unmarked production
component with a fresh self-parent, and threads the complete result tag array.
The proof-relevant
`InitialReservationStep` and `NewReservationStep` records expose each internal
success, with `initializeReservation?_some_iff` and
`reserveNewAxiom?_some_iff` characterizing executable success.

Strict tag threading rules out replay of the same submitted axiom-link index
across composable wrapper calls: an initial step followed by a later step, and
two later steps, return different link indices. Without a structural
single-source/duplicate-link premise, this does not identify equal axiom values
at different indices. Reset/replaced tags are outside the guarantee and can
make low-level `NEXTAXIOM` rediscover an old axiom; the operational wrapper
independently rejects endpoints already stored anywhere in the ready stack or
waiting payload table. Direct low-level `reserveAxiomAt?` calls remain
replayable because they have neither guard.
`ReservationInvariant` bundles delayed `WellShaped`,
`OperationalWaitingDomain`, `RealizesSigma`, production `OrderedParents`,
`Abstractable`,
`ComponentsFormulaConsistent`, component/parent carrier alignment,
started-axiom/counter alignment, and tag-domain alignment. It holds after
initialization and is preserved by every successful later reservation. This is
a preservation bundle for wrapper-generated histories, not an inductive
reachability or tag-history characterization: its tag field proves only size,
so a reset-tag state may still satisfy the record. The waiting-domain field
characterizes initialized cells, not ownership or correctness of their
  payloads. The local `wait` rule below proves one exact initialized-cell
  transfer, but the reservation invariant alone still does not establish its
  global ownership. The bounded `UnifyEmpty` slice handles only an initialized
  empty previous waiting cell; with the stronger state-only invariant, its
  successful typed/executable steps preserve the complete occurrence forest and
  scheduler bundle. Strict-singleton `W(j) = [c]` activation is now the
  separate `UnifyOne` slice. The arbitrary-payload production-core fold and
  local atomic tensor/fold/drain `UnifyPayload` composition are present. From
  the full input invariant, the atomic composition now preserves the complete
  occurrence-exact scheduler bundle through a fixed-final-stack transient gap
  proof. The input-only `UnifyPayloadEnabled` layer now proves execution exists
  from that predicate plus the full invariant, but the invariant alone does not
  establish the predicate; no physical intermediate tensor/fold state is
  assigned that invariant.
`SequentialSchedulerInvariant.lean` adds a stronger, still state-only
foundation without conflating invariance with reachability:
the bundle carries `StructurallyWellFormed` explicitly,
`ComponentDomainExact` matches live raw component slots to `sigma`,
`ReadyBucketFrontierExact` matches aligned ready buckets extensionally to
raw-unmarked component frontiers, live frontiers and the combined
ready/waiting queue are globally `Nodup`, every queued occurrence is
raw-unmarked, and delayed pending-premise coverage exempts only already
constructed ready conclusions. `Produced` records observable production as
either a concrete raw mark or live-frontier membership;
`ProducedPremisesMarked` requires both submitted premises of every such
par/tensor to have concrete raw marks. Together with a future rule's
pre-prefix unmarked-premise witness, this is a necessary causal
anti-reconstruction guard. It is not, by itself, exact internal link provenance:
repeated formula labels mean `FormulaConsistent` alone cannot bind every
internal derivation node to one certificate-link occurrence. The separate
occurrence-provenance layer described below supplies that missing identity
without changing this observable state predicate.
`WaitingSpanExact` gives every delayed par an
exact unique producer, raw-unmarked conclusion, and strict older/younger
marked-premise span; `FiredCounterExact` counts connective constructors in the
actual live production trees. Empty state and successful initialization
establish the combined `SchedulerInvariant` for structurally well-formed
certificates, including either search orientation of the submitted axiom.
The synchronized `PreparedStep` now preserves every current state-only field:
the active ready occurrence is removed and raw-marked while its already-live
component frontier, every other ready bucket, waiting span, queue uniqueness,
premise coverage, and counter equation are transported exactly. Exact
`ConclStep`/`NopStep` witnesses and successful `concl?`/`nop?` calls inherit
that theorem because their output is `prepared.after`. This does not add
reachability.
`SequentialComponentProvenance.lean` now supplies the proof-only exact
occurrence layer that formula consistency could not: every partial derivation
constructor records submitted link indices, exact frontier picks, and every
owned certificate vertex. Local witnesses require duplicate-free used-link
and owned lists; the forest predicate requires distinct live slots to be
disjoint. A marked owned vertex's raw age must resolve to that exact live
slot, an unmarked owned vertex must remain on the same component frontier,
and every concrete raw mark is conversely owned by the component at its
representative slot. This exact relation implies
`FormulaConsistent`, initializes on a submitted axiom, and extends through the
local par/tensor queue constructors when their submitted link index/lookup is
provided. A repeated-label regression keeps the distinction concrete:
formula consistency accepts a forged same-label axiom frontier, while exact
occurrence provenance rejects it because no such submitted axiom exists.
Two closed predicate regressions separately reject a marked owned vertex
whose raw age resolves to another live slot and a raw mark outside every live
component's ownership forest.
The forest predicate is now a field of `SchedulerInvariant`: empty and exact
initial reservation establish it, while the prepared pop/raw-mark prefix
preserves it from the representative-indexed live owner. Exact/executable
`concl` and `nop` therefore preserve the strengthened bundle. A successful
deterministic `NewStep`, and hence an executable `new?` call returning `some`,
now preserves the complete current occurrence-exact state-only bundle as well.
Successful deterministic/executable `wait` now preserves that same complete
bundle: it transports the prepared forest and ready state, proves the inserted
conclusion fresh and raw-unmarked across the combined queue, and extends
`WaitingSpanExact` with the exact submitted par and strict raw-age/boundary
witness. A local `wait` records a promise and is not counted as an already
constructed connective. Successful deterministic/executable `forward` now
preserves the same complete bundle while constructing the exact submitted par,
replacing the selected and mate frontier occurrences with its conclusion in
the live component, updating the active ready bucket, preserving the combined
queue and all waiting spans, maintaining pending-premise coverage, and
incrementing the exact fired-connective count. These theorems do not prove that
`new?`, `wait?`, or `forward?` succeeds in every intended later state and are
not applicability, reachability, or progress theorems. The independent
Boolean-free `ForwardRule` and both structural and scheduler-invariant
executable correspondence layers are now kernel checked. Bounded `UnifyEmpty`
also has exact executable/direct correspondence for `W(j) = []` and preserves
the complete current `SchedulerInvariant` on every successful typed or
executable step, including its exact scheduler-boundary/representative
correspondence, component forest, queue/waiting/pending facts, and fired
counter. Strict-singleton `UnifyOne` also preserves the complete bundle and
increments the counter by two. The local arbitrary-payload activation fold has
production-core correspondence and `+ payload.length` accounting, and
`UnifyPayload` atomically composes one tensor, that fold, and the two-level
drain with exact `1 + payload.length` accounting and complete occurrence-exact
`SchedulerInvariant` preservation from a full input invariant. The proof uses
a transient payload-suffix gap over the fixed final stack and therefore does
not assert the ordinary invariant for physical tensor/fold intermediates. It
proves conditional payload applicability from explicit input-only
`UnifyPayloadEnabled`; the canonical certified dispatcher history is now
integrated, while derivation of that predicate for the selected branch,
exhaustive enabledness, richer history laws,
and later-state applicability/totality,
pure-worklist completeness, fallback removal, faithful
`NEXTAXIOM`/token-age sequencing, and whole-program linearity remain open.
`RealizesSigma` preservation for later reservations splits old and fresh raw
ages: `sigmaBoundary?_append_fresh_old` preserves old boundaries, while the
fresh-boundary lemma and the production old/fresh representative lemmas align
the appended self-parent.

The canonical two-step reservation regression makes both orientations
concrete: submitted `[0,1]` / ready `[1,0]`, then submitted `[2,3]` / ready
`[3,2]`. A deliberately
arbitrary ordered parent forest with parents `#[0, 1, 0]` and
`sigma = [0, 1]` maps raw age `2` to boundary `1` but representative `0`.
That state is not proved reachable by an actual `unify`/union transition; it
only refutes deriving `RealizesSigma` automatically from `WellShaped`,
marks/horizon alignment, and `OrderedParents`. This checkpoint still does not
prove a full reachable Figure-7 state machine. The operational local `new`
transition
now composes pop-before-mark, raw-age marking, orientation-aware binary-mate
lookup, post-mark `NEXTAXIOM`, and later reservation under a supplied
`ReservationInvariant`; its canonical regression yields marks/sigma/ready
`μ(0)=0`, `σ=[0,1]`, and `R=[[1],[2,3]]`, with `W(0)=∅` and the fresh
`W(1)=⊥`. The `ReservationInvariant` supplied to this local transition does
not by itself express semantic ownership or global queue uniqueness. The
stronger state-only `SchedulerInvariant` above expresses those obligations,
and now preserves them through successful `wait` and `forward`. The bounded
`UnifyEmpty` local query has direct executable/declarative correspondence for
`W(j) = empty`: soundness assumes `ReservationInvariant`, and completeness/iff
also assume structural validity plus the separate ready-list `Nodup` premise.
Given the full input `SchedulerInvariant`, successful typed and executable
execution preserves its occurrence forest and every remaining field.
The strict-singleton executable/direct correspondence is complete under its
documented structural, invariant, and ready-`Nodup` hypotheses. The local
arbitrary-payload fold and atomic `UnifyPayload` composition are exact in stored
order, account for one tensor plus every payload par, and preserve the complete
occurrence-exact state-only invariant on every successful step from a full
input invariant. Conditional applicability under `UnifyPayloadEnabled` is now
proved, while exhaustive branch enabledness and later-state totality remain
open; the proof does not assert the invariant for physical intermediate
states. The
canonical dispatcher now integrates successful
`concl`/`nop`/`new`/`wait`/`forward`/general `UnifyPayload` calls into a
proof-carrying certified history; specialized empty/singleton unifiers remain
compatibility APIs represented by the general branch. This integration does
not prove applicability, totality, or unconditional reachability. The separate
`InitNewHistory` proves exact tag history, whole-history submitted-slot
non-reuse, and event-counter alignment only for genuine empty/init/new
executions. The canonical tag augmentation now lifts touch provenance and
submitted-slot non-reuse through every stable dispatcher branch; event-counter
alignment and a public whole-history oriented-route theorem are not yet lifted.
Correct-state progress, pure-worklist completeness, fallback removal, and
whole-program linearity therefore remain open.

The flat-scheduler proof route was also narrowed by counterexample. Exact
concrete-state confluence already fails on a derivation-generated correct
certificate, and structural-only confluence fails on a structurally well-formed
certificate. The current candidate observation is the marked occurrence
domain together with the occurrence-thread partition. No confluence, progress,
completeness, or complexity theorem at that quotient is claimed.

Independent
transition refinement and the
production run's bundled abstraction/forest/component/pending-frontier
invariant are now kernel checked. Atomic pop-and-process restores complete
scheduler coverage once the popped index is known to be a submitted
connective: the removed head is reclassified, every other status is
transported, newly enabled consumers are enqueued, and tensor union preserves
old shared-token classes. Reverse consumer-table provenance now proves that
dependency fan-out enqueues only submitted connectives; waiting requeues
contain only submitted pars; and every real queue head is therefore a genuine
connective. The complete finite production run preserves a bundled
core/scheduler/flag/carrier/provenance invariant and full scheduler coverage.
Queue and waiting flags are now exact in both directions, both concrete
registries remain duplicate-free through every finite run, and each registry
is proved to contain at most one entry per submitted link slot. Exact
cumulative accounting now proves that, from canonical initialization, link
attempts plus the residual queue length equals the total number of initial,
dependency, and waiting-requeue insertions. Structural linear ownership and
queue deduplication charge at most one dependency insertion to each successful
firing; exact firing history bounds successful firings by the submitted link
count; and the duplicate-free waiting registry charges at most one link
carrier of requeues to each tensor firing. Lean now proves the resulting
cumulative insertion bound fits `n(n+4)+1`, and that the canonical production
run reaches an empty queue within that fuel. At this quiescent state every
submitted but unfired connective is now kernel-classified by an explicit
semantic obstruction witness. Choosing an unassigned conclusion of least
formula complexity rules out the idle-premise case: its source is a concrete
submitted connective whose premises are already assigned. Thus an incomplete
run initially yields either a distinct-thread registered par or a same-thread
tensor deadlock. Reference-switching acyclicity excludes the tensor branch.
The abstract semantics now also proves the converse active-component
invariant: every active retained edge stays inside one token class, every
reachable marking is causally closed, and active-graph walks between marked
occurrences are equivalent to union-find thread equality. Consequently the
remaining waiting-par premises are kernel-proved to lie in different active
graph components, not merely to have different executable representatives.
The exact reference path between them is now bracketed by token-anchored,
oppositely oriented scheduler boundaries. Cutting at the first reentry
isolates a contiguous block whose intervening edge endpoints are unassigned.
The selected waiting conclusion is globally minimum among unassigned formula
complexities; each boundary is consequently proved either strictly above
that minimum or to be another exact distinct-thread waiting par. A separate
strong-induction theorem now proves that every unassigned occurrence reaches
a concrete registered waiting par through strict formula-complexity descent.
Applied to the two inactive-block orientations, both frontier chases terminate
at waiting pars without increasing rank while preserving the exact path
decomposition. The construction has now been generalized from that selected
minimum obstruction to every registered waiting par: each waiting par has an
exact outgoing path/frontier/chase dependency to another registered waiting
par, all dependency endpoints lie in the finite formula carrier, and
iterating for one more step than the number of formula occurrences is
kernel-proved to repeat a waiting conclusion. The repetition is also exposed
as concrete indices `earlier < later ≤ formulas.size`, with equal endpoint
conclusions, registered-waiting evidence for every chain vertex, and the full
dependency witness retained on every edge inside the nonempty closed segment.
The well-founded chase inside each dependency is no longer recorded only by
an endpoint inequality: Lean now retains a reflexive-transitive sequence of
exact source-connective/premise steps, and proves that these paths compose,
never increase formula complexity, and decrease it strictly when nontrivial.
Each such formula-premise step is now lifted to the exact full occurrence
graph edge from connective conclusion to selected premise. Lean composes a
nontrivial chase into a vertex-simple path whose edges are all traversed
backward and whose internal vertices are therefore cusp-free. The
state-indexed chase also retains that every visited formula occurrence is
unassigned, closing a gap that an endpoint-only relation could not express.
At the scheduler boundary, an occurrence-exact retained-edge API preserves
the concrete full-graph edge and its orientation; the previous endpoint API
remains available as a compatibility projection. A nontrivial dependency
tail cannot immediately reverse the lifted assigned-to-unassigned frontier.
The all-left switching mask is now classified at that exact full-edge index,
not by edge value: axiom, tensor-left/tensor-right, and the sole retained
par-left occurrence remain distinct even when parallel edges have equal
endpoints. The lifted prefix now preserves the stored edge and orientation at
every list position, and the segment theorem propositionally binds its
classified frontier to the actual last prefix occurrence and its classified
formula edge to the actual first tail occurrence. Structural typing excludes
the axiom case at a formula-descent source, while unique connective production
identifies the frontier producer with the first tail producer. Lean
consequently proves the exhaustive local turn theorem for the edges that are
actually concatenated: a retained par frontier and the reversed first tail
incidence share the same par color and form a genuine cusp; a tensor frontier
and tail carry exact unique colors, and color equality would force the
prohibited immediate reversal, so the turn is free. Every edge of the finite
 closed waiting-dependency segment now carries this occurrence-geometric
 alternative and an exact composable `fullGraph` segment from its source
 waiting conclusion to its target. Lean concatenates the selected finite
 family into a genuinely nonempty closed occurrence-aware walk in the
 certificate's complete graph. A reusable exact-occurrence
 `Graph.EdgeWalk.NoImmediateReverse` predicate now proves that every individual
 dependency segment is internally nonbacktracking: the source/prefix junction,
 retained simple prefix, classified frontier/tail junction, and all-backward
 tail are covered separately. This does not yet make the concatenated closed
 walk nonbacktracking, because an immediate reversal may still occur between
 two adjacent segments. Lean now proves that any such junction reversal forces
 the preceding dependency's formula chase to be reflexive; a nontrivial
 preceding tail and the next segment head are both backward, so they cannot be
 reverses. The reflexive alternative is occurrence-exact: the final retained
 frontier occurrence is the same stored edge used backwards as the next
 waiting par's source incidence. A generic graph theorem and a
 dependency-specific theorem now cancel exactly that pair while preserving the
 walk endpoints, all other occurrences, and the nested-waiting-par witness.
 A terminating exact-occurrence normalizer repeatedly removes internal pairs
 and rotates away a reversing last/first cyclic pair. Lean therefore reduces
 the nonempty closed dependency walk to a closed walk which is either empty or
 cyclically nonbacktracking, with every surviving occurrence drawn from the
 original obstruction. The empty alternative is real for nested out-and-back
 tree walks and is not silently discarded. The cyclic normalizer now also
 returns a proof-relevant cancellation tree: every internal deletion and every
 rotated closing deletion is retained. Lean proves from an empty trace that,
 for every directed-edge value represented in the original obstruction, the
 reverse orientation of that same stored edge also occurs in the original
 walk. This is an exact-index membership result, not yet a bijection between
 list positions. The scheduler theorem exposes both the trace and that reverse-
 membership result. It now also proves that every forward-oriented occurrence
 in the original dependency walk is retained by the all-left reference
 switching. Therefore, in the empty-normal-form branch, reverse membership
 upgrades this to retention of every original edge index. This identifies the
 empty obstruction as a fully reference-retained nested tree walk. Lean now
 transports that original nonempty closed walk into the deterministic reference
 switching, and the public
 `DeclarativelyCorrect.referenceSwitchingTree` theorem packages that graph's
 tree property. A nonempty closed tree walk may still be nested backtracking, so
 this does not yet exclude the obstruction. The empty branch now additionally
 exposes a `CyclicImmediateReverseSite` in the original traversal: either an
 exact adjacent occurrence/reverse pair or an exact reverse pair across the
 cyclic closing junction. Cyclically nonbacktracking inputs are proved fixed by
 the proof-relevant normalization, and if two individually nonbacktracking
pieces contain an internal cancellation after concatenation, that
cancellation is proved to cross their unique junction. The scheduler proof
 now retains the complete finite dependency-segment family, its chain indices,
 and each segment's exact head/last scheduler classifications. It localizes the
 site to an adjacent or cyclic segment junction and proves that this junction
 is the same exact occurrence used both as the preceding dependency's retained
 reflexive end and as the following waiting par's stored left incidence. The
 dependency repetition is now chosen at its first repeated conclusion, so all
 earlier chain positions are injective. The retained empty-branch family is
 therefore a simple dependency cycle, not an arbitrary closed segment hiding a
 smaller repetition. Its cancellation junction crosses two distinct waiting
 pars, which rules out a singleton cycle and proves that the family contains at
 least two segments. Each dependency now retains its exact first
 marked-to-unmarked frontier together with assignment of every preceding path
 endpoint. Lean proves that every forward occurrence entering an unassigned
 vertex is exactly this frontier and that, when the target is another registered
 waiting par, the formula chase must be reflexive. The fully cancelling simple
 cycle therefore pairs every source reverse with the unique cyclic
 predecessor's exact last occurrence, and every segment ends at its reflexive
 frontier. The occurrence-indexed full-segment decomposition is now preserved
 through the finite family. Removing each exact backward source incidence and
 forward reflexive frontier yields a deterministic residual core; Lean proves
 its endpoints share one live token, chains it occurrence-exactly to the cyclic
 successor, and proves every edge of every residual core has both endpoints
 assigned before the first marked-to-unmarked boundary. Lean also proves that
 no residual core is empty: emptiness would make adjacent waiting pars consume
 the same exact premise occurrence, so structural one-parent ownership would
 identify their stored links and contradict simplicity of the dependency
 cycle. Removing the source and frontier boundaries also preserves each core's
 exact no-immediate-reverse property, and the deterministic active family
 packages these nonempty internally nonbacktracking cores. Lean composes their
 deterministic flattening into a nonempty closed full-graph walk whose last
 endpoint returns to the first core's exact source-premise base. Every core
 occurrence is retained by the reference switching, so cyclic normalization
 cannot leave a nonempty cyclically nonbacktracking residue in its tree. Lean
proves that the core-only normal form is empty and localizes an exact reversal
to a cyclic junction between two nonempty internally reduced cores. That
junction is now tied to one exact dependency step and both concrete segment
decompositions. The adjacent segments contain the strict occurrence word
`inner, outer, outer.reverse, inner.reverse`; their own nonbacktracking proof
rules out a degenerate inner/outer pair. Both original detailed segment
witnesses remain attached at that same step, and each `core ++ frontier` is
pointwise aligned with its exact retained reference-switching prefix. Lean
also proves that the successor prefix begins with the inner occurrence's exact
reverse. Lean now performs that local switching flip for every reflexive
dependency: it replaces the backward left-par source incidence and retained
prefix by the exact backward right-par occurrence followed by the reversed
strict reference suffix. Each replacement is a vertex-simple full-graph path,
avoids the exact left occurrence of its target waiting par, and the finite
family composes into a nonempty closed cyclically nonbacktracking walk. Every
internal transition, adjacent segment junction, and last/first closing
junction of that flipped walk is kernel-proved cusp-free. The remaining
empty-branch obligation is therefore no longer normalization, indexing,
reference-prefix transport, a hidden formula tail, immediate reversal, or a
local cusp. It is the global repeated-vertex/nesting argument needed to turn
this exact cyclic witness into one forbidden switching cycle without
re-pairing incidences incorrectly at a repeated vertex. Lean now additionally
localizes the unavoidable concrete par-pair conflict to two distinct indexed
flipped segments: the omitted right occurrence is uniquely the head of its
source segment, while the matching retained left occurrence cannot lie in
that same vertex-simple segment. Under the first-repeat prefix injectivity
already carried by the dependency-cycle witness, the conflict conclusion is
also proved distinct from the holder segment's start and reached in that
segment's target list. The holder occurrence is the exact retained left
incidence and the source head is the exact omitted right incidence. Lean now
splits the holder segment at that conclusion into incoming and outgoing
vertex-simple paths: the incoming path is nonempty, the retained-left
occurrence belongs to the orientation-correct side, and the two paths meet
only at the conclusion. The two conflict segments are additionally ordered by
an exact before/middle/after decomposition of the indexed family. Cutting the
cyclic family at the shared conclusion then constructs two closed full-graph
arcs, with the first arc nonempty, the omitted-right occurrence in that first
arc, the retained-left occurrence assigned to one of the two arcs, and their
concatenation covering the original flipped occurrences up to the cyclic
rotation permutation. Lean now additionally retains an exact rotation witness,
proves the rotated concatenation cusp-free internally, and derives internal
cusp-freedom for each arc. The retained-left orientation is now tied to the
exact chord boundary: if it is forward, it is the incoming path's last edge,
the omitted-right occurrence is the first edge of the first arc, and that
new closing turn is kernel-proved to be a par cusp. If retained-left is
backward, it is the outgoing path's first edge and therefore the nonempty
second arc's exact head. Lean now also classifies that backward closing turn:
the exact rotation boundary is cusp-free, and the reversed retained-left and
omitted-right incidences have the same par color, so every possible last edge
of the second arc closes cusp-free against its head. Combined with the
already-proved internal cusp-freedom, the second arc is cyclically
nonbacktracking. It is nonempty and strictly shorter than the original
flipped walk because the complementary first arc is nonempty. This still does
not make it a `CuspFreeCycle`: the second arc may repeat vertices, and
correctness then forces some concrete par pair to survive again. Lean now
transports more than length through this descent: every second-arc occurrence
retains its exact indexed flipped-scheduler segment, every forward occurrence
remains reference-kept, and the recursive omitted-right par is located at the
exact head of one classified segment while its retained-left mate lies in a
distinct classified segment. The shared par conclusion is the first segment's
start and a genuine internal target of the second segment. That information is
now packaged as a generic cyclic scheduler-subarc state. Lean rotates any such
subarc to its omitted-right occurrence and cuts at retained-left. A backward
retained-left produces a strictly shorter state with the same closed-walk,
cusp-freedom, reference-retention, scheduler-provenance, and located-par
invariants. Each cut additionally retains a proof-relevant cyclic-interval
trace: the larger traversal's exact rotation decomposition and the smaller
contiguous interval are recorded rather than replaced by a membership subset.
Recursion on traversal length therefore terminates at a forward retained-left
par-cusp arc, with its full interval-descent trace back to the original flipped
family. The infinite-backward-descent concern is closed without loop erasure.
The terminal proof object now also retains the exact complementary cyclic
interval rather than merely naming an unrelated closed arc. One indexed
terminal witness binds the positioned generator, terminal arc, complement,
derived strict cut, closed complement walk, reverse-shell normalization, and
the nesting trace that consumes them. The complement is nonempty, closed,
internally cusp-free, and strictly shorter. Lean proves that
any cusp at its closing junction must be the exact last/first immediate
reversal: a nontrivial par cusp would also cusp against the terminal arc's
retained-left boundary, contradicting the rotated traversal's internal
cusp-freedom. Lean now strips those exact reverse shells proof-relevantly,
retaining an exact
`opening ++ normalized ++ reverseTraversal opening` decomposition and length
equation. A nonempty normalized core inherits both the concrete par
obstruction and its exact scheduler location. If that core closes cusp-free,
the same construction produces a strictly nested terminal forward cusp;
well-founded recursion records the transitive cyclic-interval descent and
terminates. The finite empty normalized-shell alternative is now ruled out:
its nonempty opening is immediately followed at the shell midpoint by the
exact reverse of its last occurrence, which is a cusp and contradicts the
inherited `CuspFreeTraversal`. The remaining geometric obligation is the
scheduler-located nontrivial closing-par core.
For the
 nonempty normal form, exact
 index/orientation transport through arbitrary switching masks is now proved.
 Any par-pair-sparse cyclically nonbacktracking walk would therefore lie in one
 occurrence switching and contradict its tree property. Lean consequently
 exposes a concrete par whose two exact premise occurrences both survive; the
 all-left forward-retention invariant forces its omitted right occurrence to be
 traversed backward. Proof-net correctness and finite length now transport the
 exact cyclic scheduler state through every shorter backward witness and force
 a terminal forward par-cusp interval. Its complementary interval is exact,
 nonempty, closed, strictly shorter, internally cusp-free, and its reverse
 shells are now normalized with exact positional and length evidence. Finite
 nested descent reduces the obstruction to either an empty shell core or a
 scheduler-located nontrivial closing par cusp. In the empty branch, the
 coordinate-exact reverse chord now carries both source endpoints, complete
 retained reference-suffix walks, and the exact target-left occurrences avoided
 by the two classified segments; the global fully reflexive-cycle theorem
 exposes this outcome directly. The selected compacted suffix occurrences are
 proved to remain exact reverses. The empty shell itself is now split into two
 nonempty reference-switching walks through one midpoint, with the complete
 closing traversal kernel-proved equal to the reverse of the opening traversal.
 Lean now uses that same exact shell equation together with inherited internal
 cusp-freedom to exclude the empty branch: the midpoint is an unavoidable
occurrence/reverse cusp. The surviving closing-par core carries exact first
and last scheduler tags, their segment/offset lookups and flipped-segment
classifications, and proof that its forward last incidence is retained by
the reference switching. Those exact tags now share one dependent witness with
the same par link and normalization core; Lean proves the tagged core has the
form `first :: middle ++ [last]`, remains closed, and its artificial closing
seam is neither a same-segment nor a segment-boundary adjacency of the original
scheduler. The retained state-and-interval ancestry now binds every
backward-search cut to its positioned par obstruction and binds every terminal
complement to the same indexed forward-cusp generator, arc, derived cut, closed
walk, and reverse-shell trace. The terminal path no longer invokes the generic
`CyclicIntervalCut` positional lift; only the source-fixed reverse-shell
decomposition is lifted. The global closing theorem now packages that exact
terminal base, its data-indexed global ancestry, the closing outcome, and the
endpoint split: the first three share the same
`(base, complementBase, taggedComplement, taggedNormalized)` tuple, and the
split shares that exact `taggedNormalized`. The full terminal `StepAt` frame
remains existential inside its step wrapper rather than a global package index.
The structural replay now consumes that wrapper once and carries both the
older candidate cursor and an exact endpoint zipper through the terminal frame,
backward frames, reverse shells, nesting, and global ancestry. The zipper's
gap is the complete complementary endpoint arc, not the candidate cursor gap.
The canonical terminal replay fixes the reverse-shell opening and closing
contexts and the nonempty omitted arc. Its first opening is the reverse-shell
frame when `closing ++ opening` is nonempty and otherwise the omitted-arc
frame. The resulting base gap is exactly
`closing ++ taggedArc ++ opening`; it contains the omitted-right anchor and
the outer retained-left last occurrence. Its erased outer arc is a closed,
internally cusp-free walk whose exact wraparound from the outer last occurrence
to the anchor is a nontrivial cusp. The first-opening proof is constructed by
the stated shell case split, but its returned proposition does not expose the
chosen frame together with the anchor origin. The complete base gap is a
sublist of every later ancestry gap, and the entire `taggedArc` therefore
survives in its original linear order inside the initial scheduler-family gap.
The exact head/last lookups now decompose that gap as
`g0 ++ anchor :: g1 ++ outerLast :: g2` and yield
`CyclicFourPointDisplayAt firstTag lastTag anchor outerLast`. The generic
display permits empty intervals and repeated values; it proves no contiguity,
fixed linear rank, crossing, cyclic betweenness, or model-specific
scheduler-order/proper-nesting contradiction. In the complete initial `tagSchedulerFamily`,
the four exact tags are now proved `Nodup` without claiming distinct erased
edges or vertices. The same outer positioned choice and the inner positioned
witness are both lifted through ancestry to that full family and returned with
the display. Its `firstTag → lastTag → anchor → outerLast` order separates,
rather than crosses, the two endpoint pairs; intervals may still be empty, and
ordinary laminarity permits the pairs as siblings. The fixed accepted
three-axiom regression refutes a generic flat age-interval/LIFO invariant.
Flat completeness therefore points to residual-witness preservation or
confluence modulo the marked-domain/occurrence-thread observation. Exact-state
and structural-only confluence are already refuted; no theorem at the candidate
quotient exists. The bounded/tagged `NEXTAXIOM` and dynamic-start primitive is
kernel checked, including per-call trace/tag invariants, exact oriented routes,
initial/local rank-scoped totality, and touched-set disjointness for successive
calls that strictly thread `first.tags`. The delayed state checkpoint proves
raw-age `σ` partitioning, the three waiting-cell states, the mark-preserving
`init`, the display-only printed `new`, and the separate operational `new`
that preserves `OperationalWaitingDomain`. The production
bridge now packages both views in `ReservationState`, supplies executable
initial and later reservation wrappers with typed success witnesses and
`some_iff` characterizations, and preserves the complete
`ReservationInvariant` bundle, including the waiting domain, across both
stages. Complete output-tag
threading excludes replay of one submitted axiom-link index between composable
wrapper calls, but resetting tags or using the low-level reservation primitive
remains outside that result.
The canonical receipt is submitted/ready `[0,1]`/`[1,0]` followed by
`[2,3]`/`[3,2]`. The newer operational local Figure-7 `new` layer additionally
performs
the synchronized pop/raw-mark prefix, fixed canonical tensor-consumer lookup,
opposite-premise search in the marked state, and the same exact later
reservation. Its input carries `ReservationInvariant`, which alone is not a
reachable-scheduler certificate. The dedicated `InitNewHistory` now records
only genuine empty/init/new executions and proves exact tags-as-touched,
whole-history submitted-slot non-reuse, and reservation-count alignment.
Successful `NewStep` and executable `new?` outputs now preserve the complete
current occurrence-exact state-only `SchedulerInvariant`, including its
component forest and global queued-occurrence fields. This conditional
preservation result does not prove later `new?` success or totality.
Successful local `wait` now preserves that state-only invariant and its exact
waiting-span/queue ownership fields. Successful local executable/typed
`forward` now preserves the same complete invariant through exact submitted-par
construction, live-frontier replacement, active-ready insertion, queue and
waiting transport, pending coverage, and fired-counter increment. Independent
Boolean-free Forward semantics and its executable correspondence are now
kernel checked. Bounded `UnifyEmpty` has the same direct correspondence under
its documented structural/invariant/list-shape premises, and successful typed
or executable bounded steps preserve the complete occurrence-exact
`SchedulerInvariant`. Strict-singleton `UnifyOne` has the same direct
correspondence and full invariant preservation. The local stored-order
arbitrary-payload activation fold has exact direct/executable correspondence,
and `UnifyPayload` now composes it atomically with the tensor and scheduler
drain while preserving the complete occurrence-exact state-only invariant from
a full input `SchedulerInvariant`. The separate input-only enabledness theorem
establishes conditional applicability under `UnifyPayloadEnabled` and returns
an invariant-preserving result; it neither derives that predicate from the
invariant alone nor assigns the invariant to physical intermediate tensor/fold
states. Integration of successful local
`concl`/`nop`/`new`/`wait`/`forward`/general `UnifyPayload` into a canonical
certified history is complete, including exact tag-touch provenance and global
submitted-slot non-reuse. Generalizing reservation-event counting and the
whole-history oriented-route API, proving exhaustive guard applicability, and
obtaining a total later-state transition system remain open.
Closing-par
scheduler-order exclusion and correct-state progress remain open.
Pure-worklist completeness, recursive-fallback removal, and a whole-program
linear cost theorem remain separate open gates. See
[the v0.10 design](docs/v0.10-design.md).

v0.9 exposes
occurrence-aware multigraph acyclicity and proves that every declarative
`IsTree` is acyclic. Exact edge occurrences, walks, cycles, and acyclicity are
also proved invariant under bounded bijective vertex renaming. The converse
forest-count theorem is now complete, yielding
`IsTree ↔ Bounded ∧ Connected ∧ Acyclic`. A certified exhaustive cycle
decision procedure now decides that exact `Acyclic` semantics and yields a
second tree checker proved Boolean-equal to the existing
reachability-plus-count implementation. The new path is an exponential
specification oracle. A second exhaustive oracle now decides the exact colored
`CuspAcyclic` proposition used by the generalized-Yeo splitting proof, and
reference-checker acceptance is proved to imply its acceptance. For
structurally well-formed certificates, Lean now also proves that
`CuspAcyclic` is equivalent to occurrence-aware acyclicity of every switching,
using exact mask-index transport even in the presence of parallel
equal-valued edges. A new finite-forest theorem proves that a nonempty bounded
acyclic graph with `|E| + 1 = |V|` is connected. Because every switching
retains the same number of edge occurrences, Lean now reduces universal
switching connectedness to one deterministic all-left reference switching.
The exact compact criterion is:

```text
check = true ↔
  StructurallyWellFormed ∧
  CuspAcyclic ∧
  ReferenceSwitchingConnected
```

`Certificate.compactCheck` executes this criterion and is proved
Boolean-equal to `Certificate.check`. It does not enumerate switchings, but
its current colored-cycle oracle is still exhaustive and exponential. A
new Guerrini-style token-unification fast path constructs a derivation while
firing par/forward and tensor/unify rules, then independently verifies that
derivation. Lean proves the fast path sound. The public
`Certificate.unificationCheck` now tries an event-driven dependency worklist,
then the eager scan, then the already complete checker-free sequentializer.
It is proved Boolean-equal to `Certificate.check` without enumerating
switchings. Both fast paths independently verify their generated derivation.
Pure fast-path completeness and Guerrini's linear complexity bound are still
separate open proof obligations. The statistics-bearing eager API carries kernel proofs
that eager saturation performs at most `|links|` full passes and exactly
`passes * |links|` link-list visits, hence at most `|links|²` such visits.
That scoped bound does not cover frontier search, union-find traversal,
independent verification, or the hybrid fallback. The worklist result
separately carries a proof that link attempts stay within the conservative
fuel `n(n+4)+1`; current `main` additionally proves that this fuel exhausts the
canonical production queue on every structurally well-formed input whose axiom
initialization succeeds. This is scheduler fuel sufficiency, not yet
correct-net completeness.

The v0.8 release adds a proved non-factorial intrinsic canonical
form and the separate `proofnet-canonical-key-0.2` wire. On
structurally well-formed certificates, equality of the new typed key is proved
equivalent to exactly the existing `ProofNetEquivalent` relation. It does not
change that relation or claim arbitrary graph isomorphism.

The research hypothesis is that a model should sometimes predict proof
geometry before it predicts a tactic sequence. A graph certificate can factor
out arbitrary ordering between independent inferences, expose dependency
structure, and support local repair. The Lean kernel remains the final source
of trust.

## Current vertical slice

The repository currently contains:

- a unit-free MLL formula language with involutive De Morgan duality;
- explicit formula occurrences and typed `axiom`, `tensor`, and `par` links;
- executable structural well-formedness checks;
- independent proposition-level structural semantics and an iff theorem for
  the executable structural checker;
- exhaustive enumeration of all par switchings;
- an independent inductive `ChoiceSelection` relation and an iff theorem
  proving the enumerator covers exactly all one-edge-per-par switchings;
- a finite undirected graph checker for boundedness, connectedness, and the
  `|E| + 1 = |V|` tree condition;
- an occurrence-aware `Graph.Acyclic` predicate in which parallel stored
  edges remain distinct and can form a length-two cycle; every declarative
  tree is proved acyclic, exact cycles plus acyclicity are proved invariant
  under bounded bijective vertex renaming, and the converse forest theorem
  proves `IsTree ↔ Bounded ∧ Connected ∧ Acyclic`;
- an exhaustive `Graph.isAcyclic` reference oracle proved sound and complete
  for exact occurrence-aware cycles, plus `Graph.isTreeViaAcyclic`, proved
  Boolean-equal to the existing `Graph.isTree`; both are deliberately
  specification paths rather than scalability claims;
- an exhaustive colored-cycle oracle `Certificate.isCuspAcyclic`, proved
  sound and complete for the proposition-level `CuspAcyclic` criterion used
  by the splitting theorem; every reference-checker-accepted certificate
  passes it, and structural well-formedness gives the exact equivalence
  `CuspAcyclic ↔ every occurrence-order switching is Acyclic`;
- a finite maximal-forest proof of
  `Bounded ∧ Acyclic ∧ |E| + 1 = |V| → Connected`, followed by the exact
  reference reduction
  `AllOccurrenceSwitchingsConnected ↔ ReferenceSwitchingConnected` under
  structural well-formedness and cusp-acyclicity;
- exact compact decomposition theorems for both declarative and executable
  correctness, plus `Certificate.compactCheck`, a switching-free executable
  specification checker proved Boolean-equal to `Certificate.check`. Its
  exhaustive colored-cycle phase is not yet a scalable contraction checker;
- a deterministic Guerrini-style unification fast path that starts axiom
  tokens, forwards par links when premise classes agree, unifies tensor links
  when they differ, carries partial derivations, and independently verifies
  the final tree. Lean proves fast-path soundness. The exact
  `Certificate.unificationCheck` API combines it with the complete
  checker-free reconstruction fallback and is proved equal to `check`; the
  detailed tier returns stable `UnificationErrorCode` diagnostics, while the
  pure fast path is not yet proved complete or linear. Its
  `unificationDerivationCandidateWithStats` result exposes proved eager-scan
  counters without overstating them as a whole-program time bound;
- an event-driven worklist prototype that precomputes premise consumers,
  enqueues newly armed links, and requeues only waiting par links after tensor
  unions. Every worklist success is independently verified and proved sound;
  the worklist-first hybrid is proved equal to `check`, while completeness,
  the final correctness-to-progress argument, flat-waiting-set complexity,
  and full Figures 7–8 `NEXTAXIOM` sequentialization remain open. The current
  production fuel is proved sufficient to empty its queue. If that quiescent
  run is incomplete, least-complexity descent eliminates idle premises and
  initially leaves a distinct-thread waiting par or same-thread tensor
  deadlock. A kernel-checked active-reference connectivity invariant and
  switching-cycle argument now exclude the tensor branch on every
  declaratively correct input. A second causal-closure/reference-edge
  invariant proves exact equivalence between active graph components and
  union-find classes, strengthening the remaining submitted waiting par to
  two marked premises with no active reference walk between them. Exact
  occurrence-aware tree-edge exchange now also supplies a reference simple
  path between those premises which avoids the par conclusion; an incomplete
  run must expose an unmarked internal occurrence on that path. A generic
  occurrence-preserving first-frontier theorem now strengthens this to an
  exact traversed reference edge directed from a marked occurrence into an
  unmarked occurrence while retaining an entirely active path prefix. Exact
  active-component/thread correspondence therefore proves that the frontier
  source carries the waiting par's left-premise token; it is not merely an
  unrelated marked vertex. Reading the same path backward selects the last
  inactive frontier, proves its target carries the waiting par's right token,
  and yields one exact ordered decomposition with distinct left and right
  boundary occurrences. Exact retained-edge/source-link lookup, completed
  axiom initialization, and causal closure now classify the boundary as a
  forward premise-to-conclusion occurrence of a concrete submitted par or
  tensor. Quiescent scheduler coverage then proves these exact local
  alternatives at both sides of the bracketed region: a par has an unassigned
  omitted premise or remains registered on distinct tokens, while a tensor
  has an unassigned opposite premise. A stricter suffix cut now selects the
  first reentry into the marked region and proves that every intervening
  traversed occurrence has two unmarked endpoints, while retaining exact
  scheduler classifications at both boundary orientations. The subsequent
  occurrence-aware dependency, flipped-cycle, terminal-cusp, reverse-shell,
  and well-founded nesting arguments exclude the empty reverse-shell base by
  its forced midpoint cusp and reduce the remaining progress proof to one
  scheduler-located nontrivial closing-par core. Its exact endpoint tags,
  par link, normalized core, and first-to-last tagged split now share one
  witness, and its artificial seam is proved not to be an original scheduler
  coordinate adjacency. Every recursive backward-chord frame is generated by
  the same coordinate-exact positioned obstruction and retained in the search
  trace. The terminal generator, arc, complement, derived cut, closed walk,
  reverse-shell normalization, and nesting trace now likewise share one
  indexed witness, without the first generic `CyclicIntervalCut` lift. The
  terminal base, global trace, closing outcome, and normalized endpoint split
  are now assembled into one data-indexed closing package. A private
  proof-relevant endpoint replay consumes each stored exact frame without
  reselection. Its occurrence-position zipper defines the complete
  complementary arc between the tagged closing endpoints. The canonical
  terminal replay always supplies the first opening: a nonempty reverse shell
  opens in the first frame, while an empty shell leaves the generator's
  nonempty omitted arc to open in the second. It retains the exact reverse
  equation, omitted-right anchor, outer retained-left last occurrence, and
  base gap `closing ++ taggedArc ++ opening`. The erased outer arc is a closed
  `EdgeWalk` and `CuspFreeTraversal`, with an exact nontrivial closing cusp from
  its retained-left last occurrence to its omitted-right head. The construction
  proves the first-opening fact by its shell case split, while the returned
  first-opening payload does not independently expose that branch or bind it to
  the anchor frame. Endpoint-gap sublist transport carries the whole
  `taggedArc` in its original linear order through ancestry into the
  initial-family gap, including its named head and last occurrences. A generic
  head/getLast-plus-sublist theorem gives the exact gap decomposition
  `g0 ++ anchor :: g1 ++ outerLast :: g2` and a
  `CyclicFourPointDisplayAt firstTag lastTag anchor outerLast`. Its intervals
  may be empty and its values may repeat generically, so this is not a strict
  scheduler-rank theorem and proves no contiguity, fixed linear rank, crossing,
  cyclic betweenness, or scheduler-order/proper-nesting contradiction. On the complete initial
  family, exact scheduler-coordinate `Nodup` distinguishes the four tags
  without distinguishing their erased edges or vertices. Both the inner
  positioned witness and the same outer positioned choice survive ancestry and
  are returned with the display; the resulting
  `firstTag → lastTag → anchor → outerLast` order is separated rather than
  crossing. A stable accepted three-axiom regression independently shows that
  this flat eager worklist can first merge token ages 0 and 2, so no generic
  contiguous-age/LIFO invariant may be imported here. Ordinary laminarity also
  permits the two displayed pairs as separated siblings. Exact-state
  confluence and structural-only confluence are independently refuted; a
  candidate quotient retains the marked occurrence domain and induced
  occurrence-thread partition. Residual-witness preservation or a theorem at
  that quotient remains the
  scheduler-preserving route for flat completeness. The separate
  bounded/tagged `NEXTAXIOM` primitive and the first independent delayed
  raw-age state layer are checked. The latter proves strictly increasing `σ`
  boundaries, distinct out-of-bounds/undefined/initialized-empty waiting
  states, a mark-preserving `init`, the literal printed `new` display helper,
  and a separate operational `new` preserving `OperationalWaitingDomain`.
  `ReservationState`, `initializeReservation?`, and `reserveNewAxiom?` now
  connect those reservations to the production carrier. Typed initial/later
  witnesses and their `some_iff` theorems expose exact success; complete tag
  threading excludes replay of the same submitted axiom-link index between
  composable wrapper calls; and
  `ReservationInvariant` is established initially and preserved later,
  including `WellShaped`, `OperationalWaitingDomain`, `RealizesSigma`,
  production forest/abstraction/formula consistency, and
  carrier/counter/tag alignment. Reset tags can replay the low-level search,
  although the operational stack guard rejects already queued endpoints;
  direct low-level reservation remains replayable. A single shared public
  `ConsumerIndex` now replaces the former private worklist builder and is
  proved sound and complete; structural linear ownership gives set-level
  singleton consumers. The operational local Figure-7 `new` rule fixes that
  canonical
  index, performs pop-before-mark, raw marking, orientation-aware tensor-mate
  lookup, post-mark `NEXTAXIOM`, and operational later reservation, and carries
  the input reservation invariant in its dependent success witness. Successful
  typed and executable `new` outputs now preserve the complete current
  occurrence-exact state-only `SchedulerInvariant`, but no theorem says that
  the executable must succeed on every intended later state. A separate
  proof-relevant `InitNewHistory` now characterizes exactly executed
  empty/init/new histories and proves exact tag provenance, submitted-slot
  `Nodup`, and reservation-count alignment. This is not a characterization of
  the full scheduler: successful local `wait` also preserves the complete
  state-only invariant, and successful executable/typed `forward` preserves it
  while constructing the exact submitted par and incrementing the exact
  connective count. Its independent Boolean-free `ForwardRule`, separate
  executable-list shape predicate, direct soundness/completeness/iff, and
  scheduler-invariant iff are now kernel checked. A bounded `UnifyEmpty`
  executable/direct-relation slice is also kernel checked for exactly an empty
  previous waiting payload: soundness assumes `ReservationInvariant`, while
  completeness/iff additionally assume structural validity and the separate
  ready-list `Nodup` premise. Given the complete state-only invariant,
  successful typed and executable execution preserves the full
  occurrence-exact `SchedulerInvariant`, including `RealizesSigma` and the
  component forest.
  The strict-singleton `UnifyOne` executable/direct correspondence is complete
  under its documented structural, invariant, and ready-`Nodup` hypotheses.
  The local arbitrary waiting-payload fold has exact head-to-tail
  executable/direct correspondence, and `UnifyPayload` atomically composes it
  with one tensor and the two-level drain. Successful steps preserve
  the complete occurrence-exact `SchedulerInvariant` and satisfy exact
  `1 + payload.length` accounting. The non-circular proof carries a transient
  unactivated-suffix gap over the fixed final stack. Input-only
  `UnifyPayloadEnabled` plus the full invariant now implies executable success
  and an invariant-preserving result, but the invariant alone does not imply
  enabledness and physical intermediates remain outside the invariant. A
  canonical priority
  dispatcher and proof-carrying certified successful history now cover
  `concl`/`nop`/`new`/`wait`/`forward`/general `UnifyPayload`; later-state
  totality, unconditional reachability, reservation-count transport, and a
  whole-history oriented-route theorem remain open. Closing-par exclusion,
  correct-state progress, pure-worklist completeness, fallback removal, and
  whole-program linearity remain open;
- a separate bounded/tagged `NEXTAXIOM` checkpoint with a reusable
  source-incidence index of proved exact submitted-link origin.
  `SourceIndex.Sound` alone is only provenance; structural well-formedness now
  additionally proves a singleton lookup at every in-bounds occurrence,
  including the multiplicity argument that prevents malformed self-axioms from
  masquerading as singleton buckets. Success retains the exact axiom
  index/endpoints, final tags, and trace, proves both endpoints were
  input-unmarked and the trace length is fuel-bounded, preserves the tag
  carrier and old `true` tags, and proves trace `Nodup` plus input-`false` to
  output-`true` for every trace vertex and both endpoints. Successive touched
  sets are disjoint only under strict `first.tags` threading, which is the
  scope of the global no-revisit discipline; reset tags are outside the
  theorem. Successful traces now carry exact oriented source-left routes, and
  initial/local calls are total under rank-scoped freshness with
  `complexity + 1` fuel. Its immediate dynamic start refines eager Figure 5
  under `OrderedParents`; malformed source buckets still fail closed. Tests
  additionally cover zero fuel, out-of-bounds and marked starts, missing
  sources, a threaded distinct second start, stored-right orientation, and
  repeat rejection, plus a depth-two exact rank/fuel boundary. A separate
  delayed-state checkpoint now covers raw ages, `σ`, waiting-cell distinctions,
  and exact mark-preserving initial/later reservations. The
  `ReservationState` bridge proves both executable wrappers equivalent to typed
  initial/later steps, preserves `RealizesSigma` and the full reservation
  invariant across later appends, and exposes both submitted and
  reached/partner orientations. Strictly threaded wrapper calls cannot reserve
  the same submitted axiom-link index; reset tags or direct low-level
  reservation can. The next layer gives the project's operational local
  Figure-7 `new` sequencing under `ReservationInvariant`, with a fixed
  sound-and-complete consumer index, mark-before-search dependency, and
  preservation of the exact initialized-cell domain. Its successful typed
  step, and executable `new?` success, now preserve the complete current
  occurrence-exact state-only `SchedulerInvariant`; this does not establish
  `new?` success or totality on every intended later state. The separate local
  `wait` rule now performs an exact raw-age-to-`sigma`-boundary payload cons and
  preserves the complete state-only invariant on every successful result.
  Successful executable/typed `forward` now likewise preserves that invariant,
  with the exact submitted par, forest/frontier/queue/waiting/pending fields,
  and fired counter accounted. The independent `ForwardRule` and exact
  executable correspondence are also proved, with active-ready `Nodup`
  isolated as a fail-closed representation condition. Bounded `UnifyEmpty`
  now has exact direct/executable correspondence for an empty previous waiting
  cell, and successful typed/executable steps preserve the complete
  occurrence-exact `SchedulerInvariant`. A local arbitrary-payload activation
  fold and atomic tensor/fold/drain `UnifyPayload` composition are present;
  successful typed/executable arbitrary compositions preserve the component
  forest and full scheduler invariant from a supplied full input invariant.
  The separate pure-input `UnifyPayloadEnabled` predicate now gives conditional
  applicability and invariant-preserving output; deriving it exhaustively for
  reachable dispatcher states and invariance of physical tensor/fold
  intermediates are not established. Canonical successful-trace integration is now
  complete for the six dispatcher families. Reachable later-state
  applicability/totality, unconditional full-rule reachability, richer history
  commitments, full scheduler correctness, and a
  whole-program cost proof remain open;
- a Lean theorem `check_sound` connecting executable acceptance to an
  independent inductive walk semantics;
- kernel-checked loop erasure and a finite-vertex path bound, yielding full
  checker soundness and completeness for that standard unbounded semantics;
- exact soundness and completeness against an independent fuel-indexed path
  semantics: `closureN fuel` iff a path of at most `fuel` steps is available
  when stored edges are in bounds;
- `check_iff_fuelDeclarativelyCorrect`, lifting both the path and switching
  correspondences to the complete certificate checker;
- `check_iff_declarativelyCorrect`, proving the Boolean checker decides the
  public Boolean-free, unbounded switching specification;
- explicit exchange/permutation plus recursive identity expansion proving
  `|- A, A-dual` for every unit-free MLL formula;
- a first-order arbitrary cut-free derivation-tree language with explicit
  resource positions and exchange permutations;
- an exact synchronization theorem proving that formula inference succeeds iff
  occurrence-aware fragment construction succeeds with the same ordered
  formula boundary, including exchanges between duplicate labels;
- a kernel theorem proving that every successfully constructed fragment's
  public certificate lookup recovers exactly that ordered formula boundary;
  separate structural-composition and switching-composition theorems now prove
  every such fragment declaratively correct and executable-checker accepted;
- totality of both `desequentializeChecked?` and `elaborate?` for every rule
  tree accepted by the independent `infer?` pass;
- general validated desequentialization of those trees, with a checked return
  type carrying `certificate.check = true`;
- a deterministic broad-family derivation generator whose first 250
  depth-two trees all produce accepted certificates;
- a derivation-first generator for the corresponding canonical identity
  certificate at arbitrary formula depth, with exact certificate-gated
  reconstruction;
- a finite formula enumerator whose depth-two one-atom corpus checks all 210
  generated identity certificates;
- labeled negative-certificate mutations, compile-time regression assertions,
  and an executable smoke test.
- an independent CI differential audit over 33,868 exhaustive graphs and
  1,000 generated or mutated certificates.
- versioned canonical v0.2 JSON plus a committed deterministic dataset of 250
  positive and 750 negative checker-labeled records;
- a native v0.2/v0.3 JSON parser with path-aware errors, a v0.2-to-v0.3
  migration API, a checker-gated API for untrusted certificates, and a
  deterministic 5,000-case malformed-input fuzz gate;
- a runnable focused cut-free sequent-search baseline with eager invertible par
  steps and exhaustive tensor resource partitions;
- lossless bounded vertex reindexing with inverse round trips, a proved
  equivalence relation, and whole-checker/declarative-correctness invariance.
- a v0.3 `reindex-v1` serialized normal-form key proved invariant under that
  relation, plus an independent 1,000-record permutation/property audit.
- a theorem that this normal form is an in-class representative and a complete
  invariant for structurally well-formed certificates, plus the executable
  `Certificate.reindexEquivalent?` decision procedure.
- a well-founded logical sequentialization theorem: every checker-accepted
  certificate has a kernel `Derivation` whose sequent is exactly the ordered
  list of its conclusion formulas.
- a full well-founded sequentialization theorem: every checker-accepted
  certificate has a concrete first-order `CutFreeDerivation`; its executable
  desequentialization is `ProofNetEquivalent` to the input and carries the
  same ordered formula boundary.
- the v0.5 executable `Certificate.sequentialize` API that searches
  checker-preserving inverse rules and returns a proof-bearing tree, exact
  ordered input boundary, accepted desequentialization, and
  `ProofNetEquivalent` output. `Certificate.sequentialize_complete` proves this
  runtime search succeeds for every checker-accepted certificate; it also
  passes all 250 broad generated regressions, the same 250 nets with every link
  list reversed, and a dedicated repeated-boundary-label regression.
- the v0.9 `Certificate.verifyDerivation?` API for clients that
  already have a proposed cut-free derivation. It does not enumerate
  switchings on the input or search vertex permutations: it performs
  structural validation, independently infers and desequentializes the tree,
  then uses the proved non-factorial intrinsic canonical code. A successful
  result carries checker acceptance of the produced net and exact
  `ProofNetEquivalent` identity with the submitted certificate.
- the automatic v0.9 `Certificate.reconstructDerivation?` path.
  Its structure-guided fast path recursively peels terminal par links or
  splits terminal tensors, aligns repeated boundary occurrences by
  vertex-number-free formula-tree/axiom profiles, and validates the completed
  tree once with `verifyDerivation?`. A separately proved exhaustive path is
  retained as the fallback, so failed heuristics do not weaken completeness.
  Neither path calls the all-switchings checker. Lean proves it succeeds on
  every reference-checker-accepted certificate and proves
  `Certificate.reconstructsDerivation = Certificate.check` for all inputs.
  The current fallback can still backtrack and enumerate repeated-label
  orders, so no polynomial or linear worst-case claim is made.
- a fail-closed `Certificate.reconstructDerivationWithinLimits` API with
  explicit formula-occurrence, link, and conclusion ceilings. The qualified
  default is 128/96/24 and never enters the exhaustive formula-order
  fallback. Limit failures and heuristic misses are structured
  `ReconstructionError` values, not claims that the certificate is logically
  invalid. Every successful result carries the same soundness evidence and is
  proved inside the unbounded reconstruction decision's accepted set;
- an executable finite `proofNetCanonicalFamily` whose extensional membership
  equality is proved equivalent to exactly `ProofNetEquivalent` on
  structurally well-formed certificates. This is a factorial specification
  oracle, not a compact wire key or arbitrary unlabeled-graph canonicalizer.
- a released experimental `proofNetCanonicalFingerprint?` value that selects the
  lexicographically least serialized member of that family. Lean proves it is
  total and invariant under `ProofNetEquivalent`; the JSON-string API remains a
  forward-only convenience because no `Json.compress` injectivity theorem is
  assumed;
- an explicitly versioned `proofNetCanonicalCode?` token key.
  Its underlying structural encoder is proved injective, and Lean proves on
  structurally well-formed certificates (hence on checker-accepted inputs) that
  code equality is equivalent to exactly `ProofNetEquivalent`. It still
  materializes the factorial family;
- a released `proofnet-canonical-key-0.1` JSON wire wrapper with a bounded
  parser, structured errors, schema and fixture, v0.3-to-key semantic migration,
  and a safe matcher theorem for untrusted parsed keys. Public generation and
  matching reject inputs above seven links before factorial materialization;
  the exact typed key remains an unbounded specification oracle. Its 1,000-case
  wire property corpus, 5,000-case malformed-key fuzz corpus, and measured
  1/4/7-link benchmark pass, but larger or ordinary pairwise comparisons should
  use `CheckedCertificate.sameProofNet?`;
- an intrinsic canonicalizer that traverses the ordered conclusion
  forest, follows each unique tensor/par producer in premise order, emits every
  orientation-sensitive link exactly once, and then erases submitted vertex
  numbers. Lean proves exact traversal coverage, exact link permutation,
  in-class representation, and equality iff `ProofNetEquivalent` on the
  structurally well-formed domain. The separate
  `proofnet-canonical-key-0.2` wire removes the seven-link ceiling and has been
  differentially checked against the factorial oracle on 1,000 deterministic
  cases and exercised on 1,000 additional mixed derivation-generated accepted
  nets; its direct implementation is polynomial, currently
  `O(VL + V^2)`, and still enforces independent token/character limits;
- a clean downstream Lake consumer pinned to the exact public `v0.7.0` tag,
  exercising bounded-key exactness, safe matching, over-limit
  failure, and executable sequentialization;
- a checked pairwise identity API,
  `CutFreeDerivation.CheckedCertificate.sameProofNet?`, proved to decide
  exactly `ProofNetEquivalent`. Its search enforces the ordered conclusion
  boundary and numeric-free one-hop incident-link roles while generating
  formula-occurrence alignments; a 64-pair
  repeated-label stress case generates one candidate instead of the
  unconstrained label enumerator's theoretical `(64!)^2` orders. This remains
  an exact scoped decision procedure, not a compact canonical wire key or an
  arbitrary graph-isomorphism algorithm;
- a conservative v0.6 LeanProp bridge with judgments
  indexed by separate persistent and linear proposition contexts. Persistent
  weakening/contraction and both exchanges are explicit, while no linear
  weakening/contraction constructors exist. Conjunction, implication,
  equality rewriting, universal instantiation, and existential witnesses are
  interpreted into actual Lean proof terms; a kernel theorem proves that the
  number of linear-axiom leaves equals the linear-context length. The explicit
  exchange syntax represents exactly `List.Perm` under `Nonempty`; every such
  persistent or linear exchange is admissible, and transporting a dependent
  proof environment through exchange and its inverse is identity in both
  directions. A typed normalizer recursively removes every immediate
  persistent contraction-over-weakening redex; Lean proves the result reduced,
  the operation idempotent and size-nonincreasing, and the linear-resource
  count and proof interpretation preserved. This is a noncomputable
  proof-construction API over proposition-indexed derivations, not a runtime
  raw-schema normalizer;
- a proposition-independent schema layer for generated atoms/conjunctions/
  implications. Its 600-template deterministic corpus covers persistent
  duplication/discard, linear pairing/exchange/modus ponens, and projection;
  every packed schema has a universal theorem reconstructing a Lean proof
  under every atom valuation. A separate unindexed checker infers exact
  persistent/linear sequents, returns stable path-aware diagnostics, and has a
  theorem that every erased indexed schema is accepted with its original
  boundary. CI checks all 600 erased positives and 1,000 malformed templates
  covering every error code. A strict `leanprop-schema-0.1` JSON contract,
  native Lean parser, checker-gated entry point, checked fixtures, and separate
  deterministic 5,000-case mutation-fuzz gate now cover untrusted strings. A
  Lean-emitted 1,600-record stream has a CI-checked SHA-256 manifest. Every
  accepted raw/wire schema is now elaborated into an indexed derivation, and
  the checked API exposes universal Lean proof reconstruction;

The universal v0.4 theorem still returns
`Nonempty (SequentializationResult input)` in `Prop`. The new runtime API does
not extract that witness by choice: it performs finite inverse-rule and
occurrence-permutation search, permits semantically irrelevant link-list
permutation, and rechecks its output. Its separate totality theorem is proved
by the terminal-rule dichotomy, checker-gated candidate totality, complete
finite boundary alignment, and well-founded fuel induction. The path-based
downstream consumer executes the API and consumes that theorem, and CI
 separately audits 667 declarations: 423 public MLL logical-boundary theorems
 against the exact axiom set `[propext, Classical.choice, Quot.sound]`, plus 25
 axiom-free, 104 `propext`-only, and 115 `propext`/`Quot.sound` boundaries. LeanProp
boundaries are audited separately: the proof-term interpreter,
proposition-level permutation completeness, and the two
exchange-admissibility theorems are axiom-free.
Resource-count, dependent-environment round trips, packed-schema soundness,
permutation elaboration, checked-wire soundness, and six structural-
normalization theorems use exactly `propext`. Exact agreement between
formula-only inference and typed elaboration, its acceptance-lifting
corollary, checked-wire inference, and the normalizer size bound use exactly
`[propext, Quot.sound]`.
The two public graph-acyclicity transport theorems and the two new exact
first-frontier/prefix-path theorems are independently locked to exactly
`[propext, Quot.sound]` and do not add `Classical.choice`.

This remains a research prototype rather than a mature general-purpose
library. The supported unit-free, cut-free MLL reverse-sequentialization
theorem is now complete, but its certificate model does not include cut
elimination, units, exponentials, additives, or quantifiers. The experimental
LeanProp layer has quantifier proof-template nodes but no claim of proof-net
semantics; its wire layer intentionally covers only named atoms, ordinary
conjunction, and implication, not typed equality/quantifier terms or broad
mathlib expressions. The
repository also lacks canonicalization modulo reordered conclusions or
arbitrary graph isomorphism, long-term cross-version API stability beyond the
documented compatibility contracts, optimized checking and sequentialization,
and a Lean tactic. The API,
diagnostics, compatibility, performance, independent downstream, and
large empirical readiness criteria are tracked separately and are not implied
by the theorem.

## Trust path

```text
untrusted derivation tree or certificate
        |
        v
validated desequentialization (when starting from a derivation)
        |
        v
structural well-formedness + every switching is a tree
        |
        v
Lean theorem: accepted -> declarative correctness
        |
        v
kernel `Derivation` with the exact ordered input sequent
        |
        v
Lean kernel
```

The external AI, JSON input, and future graph proposer are untrusted. Use
`Certificate.checkedFromString` to parse and validate an external canonical
v0.2 or reindex-normalized v0.3 certificate before exposing it to trusted code.
See [docs/trust-model.md](docs/trust-model.md) for the exact boundary.

The separate LeanProp wire API does not expose accepted JSON as mere syntax:
`LeanProp.Schema.Raw.Derivation.checkedFromString` returns an indexed
derivation, `CheckedDerivation.inferred` recovers the exact checked sequent,
and `CheckedDerivation.sound` reconstructs its Lean proposition under every
atom valuation and matching persistent/linear proof environment.

```lean
match Certificate.checkedFromString input with
| .ok checked => -- checked.accepted : checked.certificate.check = true
    useCertificate checked.certificate
| .error error =>
    report error.path error.message
```

## Build

Prerequisites: Git and [Elan](https://github.com/leanprover/elan). The pinned
Lean version is recorded in `lean-toolchain`.

```powershell
lake build
lake exe proofnet_ir_tests
lake exe proofnet_ir_consumer_index_tests
lake exe proofnet_ir_figure7_primitives_tests
python scripts/generate_dataset.py --check
python scripts/audit_v03_canonical.py
lake exe proofnet_ir_api_docs --check
python scripts/fuzz_malformed_parser.py
lake exe proofnet_ir_benchmark
lake exe proofnet_ir_reconstruction_audit
lake exe proofnet_ir_reconstruction_stress
python scripts/focused_search.py examples/focused-sequent-v0.2.json --require-found
python scripts/run_matched_experiment.py --check-committed
python scripts/validate_model_publication_redaction.py
python scripts/test_model_publication_redaction.py
python scripts/run_model_experiment.py --check-preregistered
python scripts/run_model_experiment_amended.py --check-amendment
python scripts/run_model_experiment_amended.py --check-committed
```

On Windows systems that explicitly block a generated audit executable with
application-control error 4551, the opt-in
`python scripts/audit_v010_windows.py` wrapper runs the same two Lean audit
sources through `lake env lean --run`. The byte-frozen
`scripts/audit_v010.py` remains unchanged for preregistration verification,
and every non-4551 failure still fails closed.

Expected smoke-test output:

```text
ProofNetIR: all certificate and v0.3 fixture checks passed
```

## Repository map

```text
ProofNetIR/Formula.lean       MLL formulas and linear negation
ProofNetIR/Certificate.lean   occurrences, links, and structural validation
ProofNetIR/Reindex.lean       lossless bounded vertex renaming and transport
ProofNetIR/Graph.lean         finite graph closure and declarative tree property
ProofNetIR/Checker.lean       switchings, executable checker, soundness/completeness
ProofNetIR/Reconstruct.lean   supported sequent derivation reconstruction
ProofNetIR/Generate.lean      recursive derivation-first identity certificates
ProofNetIR/Mutation.lean      labeled corruptions for negative fixtures
ProofNetIR/DerivationTree.lean arbitrary cut-free trees and desequentialization
ProofNetIR/GraphComposition.lean tree-preserving par/tensor graph composition
ProofNetIR/SwitchingComposition.lean switching correctness under rule composition
ProofNetIR/StructuralComposition.lean structural correctness under rule composition
ProofNetIR/DesequentializationSoundness.lean derivation-to-certificate invariants
ProofNetIR/NetEquivalence.lean semantic equivalence and checker invariance
ProofNetIR/Sequentialization.lean general theorem contract and inverse-rule work
ProofNetIR/LocalIdentity.lean proved local invariants for exact identity pruning
ProofNetIR/ExecutableSequentialization.lean runtime inverse search and diagnostics
ProofNetIR/ProofNetIdentity.lean checked exact pairwise proof-net identity API
ProofNetIR/StructuralCode.lean injective exact-key structural token encoding
ProofNetIR/CanonicalKeyWire.lean bounded exact-key wire and safe matching
ProofNetIR/IntrinsicCanonical.lean non-factorial exact canonical representative
ProofNetIR/IntrinsicCanonicalKeyWire.lean v0.2 intrinsic-key wire and migration
ProofNetIR/Serialization.lean v0.2 fixed-number and v0.3 reindex wire formats
ProofNetIR/Parser.lean        v0.2/v0.3 parser, migration, checked-input boundary
ProofNetIR/Unification.lean   eager/worklist Figure-5 token semantics
ProofNetIR/SequentialUnification.lean bounded/tagged NEXTAXIOM and local totality
ProofNetIR/SequentialRoute.lean exact oriented successful NEXTAXIOM routes
ProofNetIR/SequentialConsumerIndex.lean shared sound/complete consumer lookup
ProofNetIR/SequentialSchedulerState.lean delayed raw-age sigma/ready/waiting state
ProofNetIR/SequentialSchedulerBridge.lean typed initial/later reservation bridge
ProofNetIR/SequentialFigure7New.lean invariant-bound operational Figure-7 new rule
ProofNetIR/SequentialFigure7History.lean proof-relevant empty/init/new history
ProofNetIR/SequentialFigure7Rules.lean local concl/nop/wait/forward rules
ProofNetIR/SequentialFigure7UnifyOne.lean strict-singleton waiting-par activation and unify
ProofNetIR/SequentialFigure7Unify.lean arbitrary stored-payload production-core fold
ProofNetIR/SequentialFigure7UnifyPayload.lean atomic tensor/fold/drain payload unify
ProofNetIR/SequentialFigure7UnifyPayloadInvariant.lean arbitrary-payload full-invariant transport
ProofNetIR/SequentialFigure7UnifyPayloadEnabled.lean input-only conditional payload applicability
ProofNetIR/SequentialFigure7StableEnabled.lean input-only stable-rule applicability
ProofNetIR/SequentialFigure7Dispatcher.lean canonical six-rule dispatcher and certified history
ProofNetIR/SequentialFigure7PriorityEnabled.lean exact priority-aware applicability correspondence
ProofNetIR/SequentialFigure7NewInputNecessary.lean one-way input-only necessary projection for new
ProofNetIR/SequentialFreshSourceLeftRun.lean exact proof-relevant production NEXTAXIOM runs
ProofNetIR/SequentialFigure7NewEnabled.lean input-only local new applicability iff execution
ProofNetIR/SequentialFigure7TagHistory.lean exact tag/slot augmentation of certified history
ProofNetIR/SequentialSchedulerInvariant.lean state-only Figure-7 invariant
ProofNetIR/SequentialComponentProvenance.lean exact proof-only component identity
ProofNetIR/LeanPropNormalization.lean typed persistent structural normal form
ProofNetIRTests.lean          positive/negative compile-time and smoke fixtures
ProofNetIRConsumerIndexTests.lean orientation and fail-closed consumer tests
ProofNetIRFigure7PrimitivesTests.lean typed Figure-7 transition regressions
ProofNetIRFigure7UnifyPayloadInvariantTests.lean full-SI length-two payload regression
ProofNetIRDataset.lean        deterministic 1,000-record dataset emitter
ProofNetIRParserFuzz.lean     stdin driver for native malformed-input fuzzing
ProofNetIRBenchmark.lean      checked depth-2/3/4 runtime regression budget
ProofNetIRAPIDocs.lean        generated public API manifest and reference
ProofNetIRExperimentCorpus.lean deterministic matched-task corpus emitter
ProofNetIRModelExperimentCorpus.lean held-out model-task base emitter
ProofNetIRExperimentVerify.lean Lean checker/sequentializer batch boundary
consumer-smoke/               independent downstream Lake dependency test
consumer-release-smoke/       clean consumer pinned to public v0.5.0 tag
consumer-v06-candidate-smoke/  clean consumer pinned to public v0.6.0 tag
consumer-v07-candidate-smoke/  clean consumer pinned to public v0.7.0 tag
consumer-v08-candidate-smoke/  clean consumer pinned to public v0.8.0 tag
consumer-v09-candidate-smoke/  clean consumer pinned to public v0.9.0 tag
schemas/                      versioned external certificate contract
examples/                     valid and invalid JSON certificates
datasets/v0.2/                committed checker-labeled corpus and manifest
datasets/leanprop-v0.1/       Lean-emitted schema corpus manifest
scripts/focused_search.py     focused cut-free comparison baseline
scripts/run_matched_experiment.py matched generation/repair experiment runner
scripts/run_model_experiment.py preregistered held-out model experiment runner
scripts/run_model_experiment_amended.py hard-timeout protocol amendment runner
scripts/validate_model_publication_redaction.py metadata-redaction history audit
scripts/test_model_publication_redaction.py redaction mutation regression
scripts/audit_v03_canonical.py independent 1,000-record reindex-key audit
scripts/fuzz_malformed_parser.py deterministic 5,000-case parser fuzz gate
docs/                         architecture, literature map, roadmap, trust boundary
```

## Scientific status

The first deterministic matched experiment is complete: under a fixed
1,000-unit per-method budget on 1,000 positive derivation-generated MLL tasks,
focused search solved 760, while formula-skeleton proof-net generation and
one-edit repair solved all 1,000. Lean rejected every distinct mutation and
accepted plus executably sequentialized every distinct claimed certificate.
The [full report](experiments/matched-v0.1/README.md) explains why this does not
show that proof graphs generally outperform focused search or tactic
generation: most atom labels are unique, the graph method receives the full
formula skeleton, repair starts one edit from a valid net, and no learned model
or ordinary Lean goal is involved.

A second 180-task study is now preregistered across depths 2--4, repeated-label
and unique-label strata, balanced positive/negative tasks, and reference repair
distances two/three. All 360 model calls are frozen, but the original runner's
soft-only wall-clock budget prevented scoring from completing in 120 minutes.
A public amendment preserves the byte-exact original runner in Git and every
response while adding process-level hard deadlines. A later transparent
publication-only amendment replaces the machine-local GGUF path with a stable
model alias; it retains every historical request hash and adds independently
recomputable canonical request hashes. Its history audit fixes the source
corpus, rejects duplicate JSON keys, and mutation-tests both semantic drift and
cross-platform absolute-path encodings. Final results are now committed:
focused search 85/180, net generation 160/180, constructed distance-ordered
repair 180/180, model direct 117/180, and model repair 2/180. Model direct was
only 27/90 on positives despite 90/90 on deliberately atom-imbalanced
negatives. See the [final report](experiments/model-v0.2/report.md) and
[redaction receipt](experiments/model-v0.2/publication-redaction-amendment-1.json)
for the exact evidence and limitations.

The broader plan is in [docs/roadmap.md](docs/roadmap.md). Source screening and
project rationale are recorded in [docs/literature-map.md](docs/literature-map.md).
The current representative workload and its explicit scalability limitation
are recorded in [docs/performance.md](docs/performance.md). The auditable
source-coverage record is in
[docs/reading-ledger.md](docs/reading-ledger.md), and the first matched
evaluation is specified in
[docs/experiment-protocol.md](docs/experiment-protocol.md).
The stricter post-v0.2 coverage and reuse assessments are in
[docs/source-coverage-audit.md](docs/source-coverage-audit.md) and
[docs/library-readiness-audit.md](docs/library-readiness-audit.md). The
scoped v0.6 claims and release evidence are in
[docs/v0.6-release-audit.md](docs/v0.6-release-audit.md), and the exact-key
v0.7 release evidence is in
[docs/v0.7-release-audit.md](docs/v0.7-release-audit.md), and the v0.8
intrinsic-key release evidence is in
[docs/v0.8-release-audit.md](docs/v0.8-release-audit.md). The
v0.9 graph-semantics, reconstruction, unification, and release evidence is in
[docs/v0.9-release-audit.md](docs/v0.9-release-audit.md). The
external-consumer walkthrough is in [docs/tutorial.md](docs/tutorial.md), and
the kernel-environment-generated declaration surface is in
[docs/api-reference.md](docs/api-reference.md). The
representation comparison that guides general sequentialization is in
[docs/formalization-comparison.md](docs/formalization-comparison.md). Completed
page-level source audits, including Pfenning's 168 unique pages, Manin's 389
physical pages, Marcolli et al.'s 75 pages, the 33-page *Geometry of
Neuroscience* audit, and Park's 76 pages, live under
[docs/source-pages/](docs/source-pages/geometry-of-neuroscience.md).
Wire-version stability and migration rules are in
[docs/compatibility.md](docs/compatibility.md), and the exact v0.3 guarantees
are in [docs/v0.3-design.md](docs/v0.3-design.md).

## License

MIT. See [LICENSE](LICENSE).
