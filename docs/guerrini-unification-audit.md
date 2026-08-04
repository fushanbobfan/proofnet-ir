# Guerrini unification implementation audit

## Source and scope

This audit uses Stefano Guerrini, *Correctness of Multiplicative Proof Nets is
Linear* (LICS 1999), ten pages, downloaded from the primary paper record on
2026-07-23. The local audit copy has SHA-256
`47c2b9fe82c73db3bcbb5c0dab183cb2130c9c446a1ae0f9c72fe59e53cbb149`.
The complete extracted text and all eight figures were inspected. The paper is
supplemental primary literature; it was not one of the seven original PDFs
placed in the parent knowledge folder.

The official record and abstract for Guerrini's later journal article,
[*A linear algorithm for MLL proof net correctness and
sequentialization*](https://www.sciencedirect.com/science/article/pii/S0304397510007127),
*Theoretical Computer Science* 412(20), 2011,
DOI `10.1016/j.tcs.2010.12.021`, were checked on 2026-07-28. The abstract
describes the article as the full-detail presentation of the algorithm first
introduced in 1999. The full text was not accessible in this audit and has not
been read. It is therefore not counted as a locally read PDF and cannot be used
to settle the indexing discrepancy below.

The paper treats multiplicative proof structures without constants and also
allows cuts through a dummy-link encoding. ProofNet-IR v0.9 currently
formalizes only the cut-free, unit-free fragment, so dummy links and cut
handling are outside the implemented state machine.

## Exact link mapping

Guerrini's abstract link classes map to the current certificate syntax as
follows:

| Guerrini link | Switching behavior | ProofNet-IR link |
|---|---|---|
| axiom | edge between its two conclusions | `Link.axiom` |
| unary | retain one premise-to-conclusion edge | `Link.par` |
| binary | retain both premise-to-conclusion edges | `Link.tensor` |
| dummy | no switching edge; represents a cut target | unsupported |

Figure 5 gives three unification rules:

1. `start`: assign a fresh token to both conclusions of an unmarked axiom;
2. `forward`: fire a unary/par link only when both premises yield the same
   current token class, then mark its conclusion with that class;
3. `unify`: fire a binary/tensor link only when its premises yield distinct
   token classes, merge those classes, then mark its conclusion.

An armed binary link whose premises already yield the same token is a
permanent deadlock. An armed unary link whose premises yield different tokens
waits because a later binary merge can make it ready. Definition 11 and
Proposition 12 characterize correctness by a total marking whose partition has
one thread. Proposition 15 and Theorem 16 concern the more disciplined
sequential strategy of Figures 7 and 8 and its linear implementation.

## What the code implements

`ProofNetIR/Unification.lean` implements a deterministic, eager-start
unification pass:

- all axiom threads are initialized;
- connective links are scanned left to right;
- ready par and tensor links fire according to Figure 5;
- scans repeat until no progress or the link-count fuel is exhausted;
- every token class carries a partial `CutFreeDerivation` and exact occurrence
  frontier;
- a successful single component is exchanged to the submitted ordered
  conclusion boundary.

The generated tree is not trusted. `unificationReconstruct?` submits it to the
independent `verifyDerivation?` boundary, which rechecks structural
well-formedness, formula inference, desequentialization, and intrinsic
`ProofNetEquivalent` identity.

Library callers can use the detailed `unificationDerivationCandidate` and
`unificationReconstruct` forms to receive a stable `UnificationErrorCode`,
message, and input counts. Except for `malformedInput`, these diagnostics mean
that the deterministic tier did not produce a verified result; they are not
logical rejections. The `?` forms are convenience wrappers.

The corresponding `WithStats` forms retain exact eager-scan counters. Their
result type contains proof fields
`passes ≤ |links|` and `linkVisits = passes * |links|`; the public axiom-free
theorem `UnificationCandidateResult.linkVisitsBound` derives the scoped
quadratic link-visit bound. This is not a total runtime theorem: frontier
lookup, representative traversal, independent verification, and fallback are
outside the counter.

`ProofNetIR/SequentialUnification.lean` now isolates the first sequential
primitive from those eager/worklist paths. It builds one reusable
occurrence-source index and kernel-proves exact submitted-link origin for every
stored incidence. That `SourceIndex.Sound` theorem gives provenance only, not
lookup existence or uniqueness. Since both axiom endpoints are registered, a
malformed self-axiom contributes twice to one source bucket; structural
well-formedness is what now proves a singleton lookup at every in-bounds
occurrence. `nextAxiomWithFuel?` is bounded and globally tagged. It fails
closed on an out-of-domain, previously tagged, previously marked, missing, or
non-unique source, and on malformed source orientation. A success retains the
exact submitted axiom link index and endpoints, the updated tag array, and the
recursive occurrence trace. Its proof fields and soundness theorems establish
tag-array size preservation, monotonicity of old true tags, trace `Nodup`,
input-false/output-true tagging of every trace occurrence and both endpoints,
input-unmarked endpoints, and `trace.length ≤ fuel`. Its `Touched` carrier is
the trace plus both endpoints, and two successful calls have disjoint touched
carriers if the second call uses exactly `first.tags`. This is the scope of the
global no-revisit discipline; resetting or replacing that array is outside the
theorem. `dynamicStartWithFuel?` then applies exactly the existing
token-semantic start update; under `Abstractable` and
`OrderedParents`, `DynamicStartResult.refinesStart` proves one Figure-5
`UnificationStep.start`. Regressions cover the expected canonical trace/tags,
zero fuel, out-of-bounds, already-tagged and marked starts, missing and
duplicate source buckets, threaded-result-tags repeat rejection, and the
dynamic state update.

`SequentialRoute.lean` now proves the exact orientation missing from the result
fields alone: the successful trace is a nonempty chain from the requested
start through exact submitted tensor/par conclusions to stored left premises,
ending at the axiom endpoint actually reached. The other endpoint is its
partner, and a proof relates the pair to either submitted axiom orientation.
The stored-right canonical regression reaches `1` through `[5, 1]` while the
submitted link remains `.axiom 0 1`.

There is also a precise initial/local totality result.
`SearchClearThrough certificate state tags rank` requires every in-bounds
occurrence at complexity at most `rank` to be untagged and unassigned. Under
that premise, structural well-formedness, state abstraction, and
`formulaComplexityAt start < fuel`,
`nextAxiomWithFuel?_exists_of_structural_clearThrough` proves the production
source-index call returns `some`. Full carrier freshness gives the rank budget
`formulaComplexityAt start + 1`. This does not prove totality of the existing
carrier-size `nextAxiom?` wrapper, nor does it prove that a later Figure-7
`new` state satisfies the freshness premise. In fact, one success tags
complexity-zero axiom endpoints, so the global low-rank predicate cannot be
threaded unchanged to a second call at any natural rank. The full scheduler
needs a route-local freshness invariant.

This search checkpoint remains deliberately weaker than Figures 7–8.
`dynamicStartWithFuel?` immediately marks both endpoints with a fresh token; it
is an independent eager Figure-5 refinement, not the paper's delayed
`init`/`new` transition, which first pushes axiom endpoints into `R`.

`SequentialSchedulerState.lean` now formalizes the first independent delayed
state slice. `RawTokenAge` is a discovery-order age and not a union-find
representative. `SigmaAgePartition` makes `σ` a strictly increasing list of
raw-age interval boundaries below the horizon, beginning at zero whenever the
horizon is positive. Fixed-capacity `WaitingCell` storage separates
out-of-bounds lookup from in-bounds undefined `⊥` and initialized empty `∅`.
The strict empty `init` reserves raw age zero and enqueues
`[reached, partner]` without marking either endpoint or defining `W(0)`.

There is an internal source conflict at the next `new`. The prose defines
`W(j)` only for the nonactive boundaries
`j ∈ {i₀, ..., i_{l-1}}` of `σ = i₀ : ... : i_l`, and says that an undefined
cell cannot be operated on. The printed `new` line instead writes `∅` at the
freshly pushed top. The printed `unify` line then pops the active top, reads the
old predecessor's waiting set, and clears that predecessor. Taken literally,
the printed `new` leaves the cell needed by the next `unify` undefined while
initializing the new active cell that the prose excludes from the domain.

The code keeps both readings visible. `newEnqueue?` is a literal transcription
of the printed fresh-cell write and is retained only as a source-audit helper;
production code does not compose it. `operationalNewEnqueue?` implements the
project's operational interpretation: it initializes the old active boundary
to `∅`, appends the fresh boundary as the new active top, and leaves that fresh
cell `⊥`. `OperationalWaitingDomain` states that, below the allocated horizon,
initialized waiting cells are exactly `sigma.dropLast`. Strict `init`
establishes this invariant, and operational `new` preserves it, all with
kernel-checked proofs. This is a project interpretation chosen to make the
prose, `wait`, and `unify` composable; it is not an author-confirmed erratum or
a claim that no other repair is possible.

`SequentialSchedulerBridge.lean` uses only the operational transition for
production reservations. `ReservationState` holds the delayed stack,
production core, and complete tags. `initializeReservation?` and
`reserveNewAxiom?` execute initial and later reservation-only prefixes; the
typed `InitialReservationStep` and `NewReservationStep` records expose the
exact successful search, orientations, enqueue, production reservation, and
output. Their `some_iff` theorems are bidirectional executable specifications.

The wrapper keeps submitted component orientation separate from
`[reached, partner]` ready order and threads the entire result tag array.
Composable initial/later or later/later typed steps therefore cannot reserve
the same submitted axiom-link index. This does not identify equal-valued
duplicate axioms at different indices without another structural premise. It
is scoped replay exclusion, not a low-level global property: resetting tags
can make `NEXTAXIOM` rediscover the old axiom, while the operational stack
guard independently rejects endpoints already stored in ready or waiting
payloads.
`reserveAxiomAt?` itself has no tag or queue guard and remains replayable.
The canonical receipt reserves submitted/ready `[0,1]`/`[1,0]`, then
`[2,3]`/`[3,2]`.

`ReservationInvariant` bundles `WellShaped`, `RealizesSigma`,
`OrderedParents`, `Abstractable`, `ComponentsFormulaConsistent`,
component/parent carrier alignment, started-axiom/counter alignment, and tag
alignment, together with `OperationalWaitingDomain`. Initialization
establishes it and every successful later wrapper preserves it. It is a
preservation bundle for wrapper-generated histories, not a reachability or
tag-history characterization; `tags_size` does not rule out reset tags. Later
`RealizesSigma` preservation uses the sigma-append old/fresh lemmas and the
production old/fresh representative lemmas. A
deliberately arbitrary ordered parent forest `#[0, 1, 0]` with
`sigma = [0, 1]` has age `2` at sigma boundary `1` but production
representative `0`. It is not proved reachable by an actual `unify`/union
transition; it only refutes automatic derivation of `RealizesSigma` from
`WellShaped`, marks/horizon alignment, and `OrderedParents`.

The next checkpoint defines the exact local Figure-7 `new` rule under a
supplied `ReservationInvariant`. It synchronizes pop-before-mark and raw-age
marking, fixes lookup to the certificate's sound-and-complete consumer index,
handles both tensor premise orientations, searches from the mate in the
post-mark core, and appends/reserves the exact returned axiom. The proof
argument blocks independently forged stack/core horizons and raw ages.
`SequentialFigure7History.lean` now inductively retains exact
empty/init/operational-new executions. For this restricted history Lean proves
tags iff recorded search touch, pairwise disjoint touched sets, globally
distinct submitted axiom-link slots, and reservation-event counts equal to
both raw-age and production counters. This does not define ready/waiting
payload ownership or the full scheduler invariant. A separate exact local
`wait` transition now compares raw marks, resolves the destination with
`sigmaBoundary?`, and prepends to one initialized bucket, without claiming
global ownership. The exact local `forward` transition and its independent
Boolean-free `ForwardRule` correspondence are now kernel checked. The paper
guard is the non-strict raw-age comparison; active-ready `Nodup` is isolated
as a fail-closed list-shape refinement. Successful wait/forward steps preserve
the complete supplied state-only scheduler invariant, but this is not a
reachability theorem.

The frozen strict-singleton unification checkpoint covers exactly
`W(j) = [c]`. It recovers `c`'s producer from the occurrence source index as a
singleton containing the exact submitted par slot and stored orientation, then
executes one atomic prepare → tensor construction/union → waiting-par
activation → scheduler drain. `WaitingParActivationRule` and `UnifyOneRule`
state independent Boolean-free relations, and Lean proves their
typed/executable correspondence, output uniqueness, `ReservationInvariant`
preservation, complete occurrence-exact `SchedulerInvariant` preservation,
and the exact connective-counter increase by two. The executable rejects an
empty cell and every payload with at least two elements. Figure 7 specifies
moving `W(j)` into ready; explicitly constructing the par derivation before
that move is ProofNet-IR's provenance-carrying representation refinement, not
a claim that the paper prescribes it.

The arbitrary-payload activation fold and atomic `UnifyPayload` composition are
now kernel checked. Every successful typed/executable atomic step from a full
input `SchedulerInvariant` preserves the complete occurrence-exact invariant:
the input supplies pre-activation freshness and exact producer/boundary facts,
each activation establishes ownership, and the final forest covers the whole
payload. This is conditional preservation, not applicability or reachability.
Integration of the now exact local
`concl`/`nop`/`wait`/`forward`/`UnifyEmpty`/`UnifyOne`/`UnifyPayload` rules into
full reachability and dispatcher/history, later-state applicability/totality,
progress, pure-worklist completeness, fallback removal, faithful
`NEXTAXIOM`/token-age sequencing, scheduler correctness, and the whole-scheduler
linear cost model remain open.
Future guards must compare raw assigned ages; replacing them by
representatives would change the algorithm.

An event-driven prototype now precomputes which links consume each occurrence.
It initially enqueues connectives once, enqueues only consumers of newly
marked conclusions, stores armed unequal-token pars in a deduplicated waiting
set, and requeues that set after a tensor union. Candidates still cross
`verifyDerivation?`. Lean proves worklist fast-path soundness, its fallback
wrapper equal to `check`, and a conservative `n(n+4)+1` link-attempt cap.
Current `main` additionally proves that structural single-consumer ownership,
distinct successful firings, and the bounded waiting registry keep all
successful insertions within that cap, and exact insertion/pop accounting
forces the canonical final queue to be empty. Scheduler coverage then gives an
exact witness for every submitted but unfired connective in that quiescent
state: an idle premise, a distinct-thread registered par, or a same-thread
tensor deadlock.
Selecting an unassigned conclusion of least formula complexity now refines
that result. Structural well-formedness recovers its concrete source link,
strict premise complexity makes both premises assigned, and the remaining
witness is therefore an exact submitted distinct-thread waiting par or
same-thread tensor deadlock. The abstract semantics now proves that every
semantic thread stays connected inside the active all-left reference
subgraph, and that invariant is transported through the concrete canonical
worklist run. Declarative reference-switching acyclicity then excludes the
same-thread tensor branch: its two fixed edges would close the active thread
path into an edge-simple cycle. The only remaining correct-state obstruction
is an exact distinct-thread waiting par. The converse direction is now also
kernel checked. Every reachable marking is causally closed, each active
retained reference edge stays inside one semantic thread, and therefore an
active reference walk between marked occurrences exists exactly when their
raw tokens share one union-find class. The two premises of the remaining
waiting par are consequently proved to have no active reference walk between
them. Exact occurrence-aware tree-edge exchange now flips only that submitted
par and constructs a reference simple path between its premises which avoids
the par conclusion. The absence of an active walk therefore yields a concrete
unmarked internal occurrence on this path, distinct from both premises and
the conclusion. The current first-frontier theorem strengthens this to an
exact retained edge occurrence directed from a marked source into an unmarked
target, together with an entirely active prefix. Exact active-component/thread
correspondence proves that this source carries the waiting par's left token.
Reading the path backward selects the last inactive frontier and proves that
its marked target carries the right-premise token. The two distinct boundary
occurrences form one exact ordered decomposition of the reference path.
Exact retained-edge/source-link lookup, completed axiom
initialization, and causal closure classify that occurrence as a forward
premise-to-conclusion edge of a concrete submitted par or tensor. Quiescent
scheduler coverage now refines the par case to either an unassigned omitted
premise or two distinct registered tokens, and refines the tensor case to an
unassigned opposite premise after excluding the same-thread deadlock. This
classification now holds at both sides of the bracketed region. What remains
is narrower still: cutting at the first unmarked-to-marked reentry proves
that every intervening path occurrence has two unmarked endpoints, while both
boundary orientations retain exact scheduler classifications. The global
progress argument now also retains the globally minimum-complexity unassigned
waiting conclusion. Strict premise descent normalizes each boundary to a
target rank above that minimum or another exact registered distinct-thread
par. The general chase now retains a composable proof object containing the
exact submitted source connective and selected premise at every downward
step, rather than discarding the structural route after deriving its endpoint
rank. Iterating the resulting dependency on the finite formula carrier
produces a concrete nonempty closed segment. Every structural step is now
lifted to the exact full occurrence-graph edge from connective conclusion to
selected premise. Nontrivial chases compose into vertex-simple paths whose
edges are all traversed backward and whose internal turns are consequently
cusp-free. A state-indexed reachability witness retains that every visited
formula occurrence remains unassigned. The scheduler frontier is also lifted
occurrence-exactly, and the first nontrivial chase edge is proved not to
reverse it immediately. An exact-index classifier for the deterministic mask
now distinguishes the retained axiom, tensor, and left-par occurrences
without quotienting parallel edge values. Structural typing excludes the
axiom case at a formula tail, and unique producer ownership synchronizes the
frontier producer with the first tail producer. Thus each nontrivial turn is
proved to be a genuine par cusp or a tensor-colored free turn. Every dependency
is now also packaged as a composable complete-graph segment from its source
waiting conclusion to its target, using the exact source-par incidence,
retained reference-prefix lift, and all-backward formula tail. The finite
closed dependency family is kernel-concatenated into a genuinely nonempty
closed occurrence-aware `fullGraph` walk. Any adjacent-segment reverse pair is
now tied to the exact retained reflexive frontier occurrence and the same
stored full-edge index is proved to annotate the next waiting par. A generic
exact-occurrence cancellation lemma and its dependency-level specialization
remove one such pair while preserving the endpoints, all remaining
occurrences, and the nesting witness. A terminating exact-occurrence
normalization now repeatedly cancels internal pairs and rotates a reversing
last/first pair. It reduces the nonempty dependency obstruction to a closed
walk that is either empty or cyclically nonbacktracking, with every surviving
occurrence inherited from the original walk. The empty branch is not an
artifact: nested out-and-back tree walks genuinely normalize away. The
normalizer now retains a proof-relevant tree of every internal cancellation
and rotated closing cancellation. Lean proves that, for every directed-edge
value represented in an empty-normalizing dependency obstruction, the reverse
orientation of the same stored edge also occurs there. This is exact-index
membership, not yet a bijection between list positions. The scheduler-level
theorem exposes that trace and membership result directly. Segment
classification also proves every forward-oriented occurrence in the
concatenated obstruction is retained by the all-left reference switching.
Consequently, an empty normal form forces every original edge index to be
reference-retained: a backward occurrence inherits retention from its
forward reverse. The scheduler theorem now transports the original nonempty
closed exact-occurrence walk into the deterministic reference switching, and
the public `DeclarativelyCorrect.referenceSwitchingTree` theorem packages that
graph's `IsTree` proof. This reduces the empty branch to a fully retained nested
reference-tree walk but does not by itself rule that walk out: nested
backtracking remains possible in a tree. The nonempty branch is sharper too:
exact masking preserves cyclic nonbacktracking, every valid occurrence
switching is proved a tree, and par-pair sparsity would place the entire
obstruction in one such switching. Lean therefore extracts a concrete par whose
two exact premise occurrences survive and uses all-left forward retention to
prove that its omitted right occurrence is traversed backward. The remaining
empty branch now exposes an exact internal-or-closing cancellation site in the
original traversal. Lean proves cyclically nonbacktracking inputs are fixed by
normalization and proves that an internal cancellation in an append of two
individually nonbacktracking pieces must cross their unique junction. The
selected dependency-segment decomposition is now retained as an indexed finite
family with every segment's scheduler endpoint classifications. Lean localizes
the site to an adjacent or cyclic junction and proves that its incoming
occurrence is simultaneously the preceding dependency's retained reflexive
end and the following waiting par's stored left incidence. Each dependency now
also retains its exact first marked-to-unmarked frontier and proves every
preceding path endpoint assigned. Thus any forward occurrence entering an
unassigned vertex is exactly that frontier. Structural producer uniqueness and
the registered waiting-par premises force a frontier entering another waiting
par to be reflexive, with no nontrivial formula-premise tail. In the fully
cancelling simple cycle, Lean pairs every source reverse with the unique cyclic
predecessor's exact last occurrence and proves every segment ends at its
reflexive frontier. The remaining argument must exclude the resulting
multi-node cycle of retained reference paths and waiting-par incidences and
transport turn classifications around the concrete nonempty obstruction into
an excluded edge-simple switching cycle or forbidden nesting in a correct
quiescent state.

This flat production prototype is not the sequential strategy of Figures
7--8. It starts all axioms eagerly, uses a flat waiting set, and does not use
the separate bounded/tagged `NEXTAXIOM` or delayed-state checkpoints. Its own
production state has no `σ`/`R`/`W` stack, token-age interval partition, or
specialized union-find invariant. The
attempt cap is no longer merely imposed by fuel: its scheduler sufficiency is
proved.
That result now rules out tensor deadlock on a correct nonfinal net and
identifies the remaining waiting par as an exact active-component separation;
the separation is now localized to a conclusion-avoiding reference path with
a genuine unmarked internal occurrence, and every subsequent formula chase
retains all exact connective/premise steps through its terminal waiting par.
The global correct-state progress theorem remains open.

A stable small regression makes the scheduler distinction executable. Its
three submitted axiom links receive fresh ages 0, 1, and 2 in link order. Of
the two submitted tensors, reverse connective queuing attempts the tensor over
the age-0 and age-2 premises first. The certificate is structurally well
formed, reference accepted, and the worklist succeeds with two attempts, zero
waiting requeues, and two firings. Those public counters do not themselves
reveal the noncontiguous token class; that fact follows from the exact
certificate plus the eager-start and reverse-queue definitions. Consequently
contiguous token-age intervals, top-adjacent interval union, and Figure-7 LIFO
behavior are false as generic invariants of this flat scheduler.

The `step` field of a `SchedulerOccurrence` produced by
`tagSchedulerFamily` is likewise the index of a segment in a selected finite
waiting-dependency cycle. It is not an absolute worklist firing time, axiom
age, or stack depth. Finally, endpoint order
`firstTag → lastTag → anchor → outerLast` places the two endpoint pairs in
separated intervals; ordinary proper nesting permits such sibling intervals
and therefore cannot supply a contradiction.

Lean currently proves:

```text
unificationReconstruct? = some result → check = true
unificationFastCheck = true → check = true
unificationCheck = check
unificationCheck = true ↔ DeclarativelyCorrect
```

The default exact decision tries the event-driven worklist, then the eager
scan, then the already complete checker-free recursive sequentializer. None of
those branches enumerates switching graphs.

## What is not yet proved

The following stronger claims are intentionally absent:

- `unificationFastCheck = check`;
- `unificationWorklistFastCheck = check`;
- removal of the recursive reconstruction fallback;
- completeness or confluence of the eager repeated-scan schedule;
- exact-state or structural-only confluence of the flat worklist: the first is
  refuted on a derivation-generated correct certificate and the second on a
  structurally well-formed certificate;
- a polynomial, quasi-linear, or linear bound for the hybrid
  `unificationCheck`;
- a polynomial bound for the complete candidate-plus-verifier execution; the
  current proved quadratic statement counts eager link-list visits only;
- equivalence between this eager implementation and the full sequential
  `σ`/`R`/`W`, token-age, `NEXTAXIOM`, and special union-find algorithm
  in Figures 7--8;
- axiom-link-index replay exclusion after resetting/replacing tags or direct
  low-level reservation. The proved result covers only composable typed wrapper
  calls that thread the complete output tags, and says nothing about
  equal-valued duplicate axioms at different indices without extra structure;
- reachable later-state selection/applicability totality, ready/waiting
  payload ownership through complete reachable transitions, and full-history
  integration of the exact local
  `concl`/`nop`/`wait`/`forward`/`UnifyEmpty`/`UnifyOne`/`UnifyPayload` rules, the
  complete scheduler transition system,
  scheduler
  correctness, and scheduler-cost
  theorems. Initial/local search totality, initial/later reservation invariant
  preservation, `OperationalWaitingDomain`, the exact invariant-bound local
  `new` pipeline, and exact tag history for genuine init/new executions are
  proved;
- support for cuts, dummy links, units, Mix, additives, or exponentials.

The current repeated scan can take a quadratic number of link visits before
independent derivation verification. A fast-path miss invokes the exhaustive
recursive fallback. Therefore citing Guerrini's Theorem 16 as a complexity
theorem for the present executable would be incorrect.

## Differential evidence

`proofnet_ir_unification_audit` checks 1,500 deterministic certificates:

- 250 derivation-generated positives;
- their 250 reversed-link variants;
- their 250 reversed-boundary variants;
- 750 malformed missing-link, duplicate-link, or invalid-axiom mutations.

It additionally checks a structurally well-formed but disconnected
two-axiom sentinel and requires the stable `nonUniqueThread` diagnostic. The
audit also checks the accepted three-axiom/two-tensor reordered regression and
requires worklist success with exactly two attempts, zero waiting requeues, and
two successful firings. The fixture records the observable schedule receipt;
its age-0/age-2 merge is obtained from the fixed links and scheduler
definitions, not inferred from public statistics. The
first recorded Windows run reported 750/750 positive fast-path hits, zero
positive misses, zero false positives, and exact hybrid/reference agreement.
This is regression evidence, not the missing fast-path completeness theorem.
The main 291-case performance workload and the 18-case repeated-label stress
suite also require the deterministic fast path to return a proof-bearing
result.

A second positive-only counterexample search now covers 7,200 reordered
derivation-generated certificates from 1,200 seeds, depths zero through seven,
up to 447 formula occurrences and 319 links. It observed no fast-path miss in
the current recorded run. The source theorem
`CutFreeDerivation.desequentialize?_check` establishes acceptance of each base
certificate; the order variants preserve the same occurrences and links.
This finite search is intentionally kept separate from the universal
completeness theorem.

The same two gates now also require the event-driven worklist. They observed
750/750 and 7,200/7,200 worklist hits, respectively, with zero false positives
or positive misses. The larger search recorded at most 995 link attempts and
691 waiting requeues. These remain finite regression results.

An uncommitted exploratory local scheduler-state audit rejects exact
concrete-state confluence on a derivation-generated correct certificate and
rejects structural-only confluence on a structurally well-formed certificate.
The surviving candidate quotient records the marked occurrence domain and the
occurrence-thread partition. Across 80 derivation-generated correct
certificates, that local run visited 2,734 reachable quotient states and
checked 7,148 enabled critical pairs, observing 0 disabled pairs and
0 quotient non-diamonds. There is currently no committed script or artifact
that reproduces these counts, so they are not a release or CI gate. This
exploratory result does not establish a local-diamond theorem, confluence,
correct-state progress, pure-worklist completeness, fallback removal, or
linearity.

## Remaining formalization route

1. State the operational one-step relation independently of the executable
   scan and prove that every fired component denotes the corresponding parsing
   substructure.
2. Use full-switching connectivity plus causal closure to exclude the
   unmarked internal region now exposed on the exact reference path between
   the remaining waiting par premises; same-thread tensor deadlock is already
   excluded by the active-path switching-cycle theorem. Exact retained-edge
   transport, par-cusp/tensor-free boundary classification, composable
   dependency segments, a nonempty closed `fullGraph` walk, internal
   nonbacktracking of every individual segment, the fact that any inter-segment
   immediate reversal forces a reflexive preceding formula chase, the exact
   retained-frontier/next-waiting-par occurrence binding, one-step
   occurrence-preserving cancellation, and terminating internal-plus-cyclic
   normalization to an empty or cyclically nonbacktracking closed walk are now
   proved. The exact first frontier and its assigned prefix are now retained;
   a frontier entering a registered waiting par is proved reflexive; and every
   segment of the fully cancelling simple cycle is paired with its unique
   cyclic predecessor and ends reflexively. The occurrence-indexed segment
   witness is now preserved through that family: deleting each exact
   source/frontier pair gives a deterministic residual core whose endpoints
   share a live token, whose successor incidence is exact, and whose every
   edge has assigned endpoints before the first inactive frontier. Each core
   is now also kernel-proved nonempty: otherwise adjacent waiting pars would
   consume one exact premise and structural one-parent ownership would collapse
   two distinct simple-cycle nodes. Removing the exact source/frontier
   boundaries preserves no-immediate-reverse, so the deterministic active
   family now consists of nonempty internally nonbacktracking cores. Those
   indexed cores are now composed into a nonempty closed full-graph walk whose
   last endpoint returns to the first core's exact source-premise base. Every
   core occurrence is reference-kept, so a nonempty cyclically nonbacktracking
   normal form would contradict the reference switching tree. The core-only
   walk is now proved to normalize to empty, with an exact reversal localized
   to a cyclic junction between two nonempty internally reduced cores. That
   cyclic witness is now reindexed to one exact dependency step and reconciled
   with both complete segment decompositions. The two consecutive segments
   contain the exact contiguous word
   `inner, outer, outer.reverse, inner.reverse`, and segment
   nonbacktracking proves the two layers do not degenerate into one pair. Both
   original full-segment witnesses are now retained at that indexed step.
   Each `core ++ frontier` is pointwise aligned with its exact reference-
   switching prefix, and the successor prefix is proved to start with the
   inner occurrence's exact reverse. The exact multi-par flip is now local and
   compositional: every reflexive dependency has a vertex-simple
   backward-right-par/reversed-strict-suffix replacement which avoids the
   target waiting par's exact retained left occurrence. The replacements form
   a nonempty closed cyclically nonbacktracking full-graph walk, and Lean proves
   all internal, adjacent-segment, and closing transitions cusp-free. The
    omitted right occurrence is uniquely the head of its indexed source
    segment, and the matching retained left occurrence is proved to lie in a
    distinct indexed segment. First-repeat prefix injectivity additionally
    proves that their common conclusion is a non-start vertex reached inside
    the holder segment's target list, and pins the two exact mask facts to
    retained-left and omitted-right. The holder segment is now split at that
    conclusion into incoming and outgoing simple paths with a nonempty incoming
    side, orientation-exact retained-left membership, and no other shared
    vertex. The two indexed conflict segments are now given an exact
    before/middle/after order, and cutting the cyclic family at the conclusion
    constructs two closed full-graph arcs. The first arc is nonempty and
    contains the omitted-right occurrence; retained-left is assigned to one
    of the arcs, and the concatenation covers all flipped occurrences up to
    the cyclic-rotation permutation. The exact rotation equation now
    transports internal cusp-freedom to the concatenation and to both arcs.
    In the forward retained-left orientation, the exact first-arc head and
    last edge are now the omitted-right and retained-left occurrences, and
    their closing turn is proved to be a par cusp. In the backward orientation,
    retained-left is the exact head of the nonempty second arc. The exact
    rotation boundary and equality of the two reversed par-incidence colors
    now prove every second-arc closing turn cusp-free. Thus this branch yields
    a closed, internally cusp-free, cyclically nonbacktracking second arc that
    is strictly shorter than the original flipped walk. It is not necessarily
    vertex-simple. Every occurrence in this shorter arc now retains an exact
    indexed flipped-scheduler segment and every forward occurrence remains
    reference-kept. Correctness forces another backward-right par obstruction
    inside the arc; Lean locates its omitted right at the exact head of one
    classified segment, its retained left in a distinct classified segment,
    and the shared conclusion at the former segment's start but internally in
    the latter segment. A generic cyclic scheduler-subarc state now retains
    closedness, internal and closing cusp-freedom, forward reference retention,
    pointwise scheduler provenance, and the located par chord through each
    cut. Rotating omitted-right to the head and cutting at retained-left yields
    either a forward closing par cusp or a strictly shorter backward state.
    Every step records the exact rotation and smaller contiguous cyclic
    interval in a proof-relevant state-and-interval trace. Every backward step
    now identifies that cut with the exact positioned right/left tags that
    generated it. Well-founded recursion on
    traversal length closes the infinite-backward branch and produces a
    terminal forward par-cusp interval with its interval trace back to the
    original flipped family. The terminal object now retains the exact
    complementary cyclic interval, proves it nonempty, closed, internally
    cusp-free, and strictly shorter, and proves that any closing cusp there is
    only the exact last/first reversal rather than another nontrivial par cusp.
    Ordinary loop erasure remains unnecessary and unsafe because it can create
    a new closing cusp by re-pairing incidences at the erased vertex. Lean now
    strips the exact reverse shells with a proof-relevant positional and length
    trace, retains the normalized core's exact scheduler provenance, and
    recursively extracts strictly nested terminal forward cusps from every
    cusp-free nonempty core. Well-founded descent first leaves an empty shell
    core or a nontrivial closing-par core. The empty shell is now excluded by
    its forced midpoint occurrence/reverse cusp, contradicting inherited
    internal cusp-freedom. The closing core's first/last scheduler tags now
    share one witness with the same par link, normalized closed core, and exact
    `first :: middle ++ [last]` split. Lean proves this artificial seam is not
    an original same-segment or segment-boundary coordinate adjacency. The
    backward search now replaces every bare cut by a generator-exact semantic
    frame sharing one positioned obstruction, both endpoint tags, both cyclic
    decompositions, and the retained suffix. The terminal step now likewise
    binds its generator, arc, complement, derived strict cut, closed walk,
    source-fixed reverse-shell normalization, and nesting trace in one indexed
    witness; the terminal path no longer uses the first generic
    `CyclicIntervalCut` positional lift. The terminal base, data-indexed global
    ancestry, closing outcome, and normalized endpoint split are now assembled
    into one exact closing package: the first three share
    `(base, complementBase, taggedComplement, taggedNormalized)`, while the
    endpoint split shares that `taggedNormalized`. The complete terminal
    `StepAt` frame remains existential inside its wrapper rather than an index
    of the global package, but a private structural theorem opens each wrapper
    once and threads that same frame through reverse-shell, backward-search,
    nesting, and global ancestry.

    The enriched replay now carries an occurrence-position endpoint zipper
    whose gap is the complete complementary arc between the fixed tagged
    endpoints, explicitly distinct from the older candidate cursor gap. Every
    indexed flipped segment is nonempty. An empty exact gap in the initial
    scheduler family would therefore force the coordinate adjacency already
    excluded by the endpoint witness, so the complete gap is nonempty.

    The stronger canonical replay of the fixed terminal step now always
    first-opens before ancestry: a nonempty reverse-shell context opens in its
    first frame, while an empty shell leaves the generator's nonempty omitted
    arc to open in the second. It retains the exact reverse equation, the
    omitted-right zero-offset backward anchor, the forward retained-left last
    occurrence of the outer terminal arc, and the canonical base gap
    `closing ++ taggedArc ++ opening`. The erased outer arc is a closed
    `EdgeWalk` at the complement base and a `CuspFreeTraversal`, while its exact
    cyclic closing pair from the outer last occurrence to the anchor is a
    nontrivial cusp. The proof internally uses the shell branch to construct
    first opening, but the returned first-opening proposition does not expose
    that frame together with the anchor origin. Gap sublist preservation
    carries the entire outer `taggedArc` in original linear order through
    ancestry into the initial scheduler-family gap, including its same
    omitted-right head and retained-left last occurrence. The generic
    head/getLast-plus-sublist decomposition theorem further exhibits the gap as
    `g0 ++ anchor :: g1 ++ outerLast :: g2`, and the zipper rotation supplies
    `CyclicFourPointDisplayAt firstTag lastTag anchor outerLast`. This generic
    relation permits empty intervals and repeated values. It is not a strict
    scheduler-rank theorem: the ordered sublist need not be contiguous, and the
    display proves no fixed linear rank, crossing, cyclic betweenness, or
    model-specific scheduler-order/proper-nesting relation.
    The complete initial `tagSchedulerFamily` is `Nodup` in exact
    `SchedulerOccurrence` coordinates, so the specialized result now proves
    `[firstTag, lastTag, anchor, outerLast].Nodup`. This does not distinguish
    their erased directed edges, endpoints, or vertices. The terminal replay
    retains the same outer positioned par choice, and exact ancestry membership
    lifts both that choice and the inner normalized closing witness to the
    complete initial family. One theorem returns both positioned witnesses,
    four-point display, and four-tag `Nodup` together. The resulting order
    `firstTag → lastTag → anchor → outerLast` separates the paired inner and
    outer endpoints rather than alternating them, so it is not a crossing.
    Intervening intervals may be empty.
    Guerrini's correctness/reduction
    results do not provide that bespoke final contradiction for the present
    flat eager scheduler.
3. Do not assume contiguous token-age intervals or generic LIFO nesting for the
   current flat worklist: the fixed accepted regression above refutes that
   invariant, and ordinary laminarity permits the separated endpoint pairs as
   siblings. Exact-state confluence and structural-only confluence are also
   refuted. Instead, investigate preservation of the existing residual parsing
   witness under every competing successful firing, or prove a
   local-diamond/confluence theorem modulo the candidate observation consisting
   of the marked occurrence domain and occurrence-thread partition. The
   uncommitted exploratory 80-certificate/2,734-state/7,148-pair local audit
   with zero observed quotient non-diamonds is neither reproducible release
   evidence nor that theorem.
4. Use that residual/confluence result, or another scheduler-specific progress
   argument, to exclude the closing-par base and prove
   correct-quiescent-state progress. Then prove the current event-driven
   worklist complete, yielding
   `unificationWorklistFastCheck = check`.
5. Remove the recursive reconstruction fallback from the exact worklist
   decision only after that equality is kernel checked.
6. Build on the now-kernel-checked initial/later bridge between bounded/tagged
   `NEXTAXIOM`, delayed raw-age state, and production `UnificationState`.
   `ReservationState`, both executable wrappers and typed `some_iff`
   specifications, strict-tag composable axiom-link-index replay exclusion,
   later `RealizesSigma` preservation, submitted/ready orientation separation, and
   the preserved `ReservationInvariant` are already proved. Keep the immediate
   dynamic-start refinement separate from the mark-preserving delayed
   reservation wrappers.
7. Extend the now-proved invariant-bound local Figure-7
   `new`/`wait`/`forward`/`UnifyEmpty`/`UnifyOne`/`UnifyPayload` rules and exact
   init/new execution history into a full transition system: derive later-state
   selection and arbitrary-payload applicability/totality, preserve queue and
   payload ownership through reachable executions, and prove full-history
   integration of every local transition. Keep the printed
   fresh-cell helper and the project's operational inactive-boundary
   interpretation distinct; the latter is kernel checked but is not an
   author-confirmed erratum.
   Replace eager axiom starts and flat waiting requeues only after token-age
   interval sequencing and its specialized union-find invariants are proved;
   the flat scheduler counterexample prevents reusing those invariants.
8. Only after the complete `NEXTAXIOM`, token-age, waiting-stack, union-find,
   and implemented-operation cost invariants are formalized should the library
   expose a Guerrini-linear complexity theorem.
